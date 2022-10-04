use halo2_curves::bn256::{Bn256, Fq, Fr, G1Affine};
use halo2_proofs::{
    circuit::{floor_planner::V1, Layouter, Value},
    dev::MockProver,
    plonk::{self, Circuit, ConstraintSystem},
    poly::{commitment::ParamsProver, kzg::commitment::ParamsKZG},
};
use halo2_wrong_ecc::{
    self,
    integer::rns::Rns,
    maingate::{
        MainGate, MainGateConfig, MainGateInstructions, RangeChip, RangeConfig, RangeInstructions,
        RegionCtx,
    },
    EccConfig,
};
use halo2_wrong_transcript::NativeRepresentation;
use itertools::Itertools;
use plonk_verifier::{
    loader::{
        halo2::{self},
        native::NativeLoader,
    },
    pcs::{
        kzg::{
            Bdfg21, Gwc19, Kzg, KzgAccumulator, KzgAs, KzgAsProvingKey, KzgAsVerifyingKey,
            KzgSuccinctVerifyingKey, LimbsEncoding,
        },
        AccumulationScheme, AccumulationSchemeProver,
    },
    system::{
        self,
        circom::{compile, Proof, PublicSignals, VerifyingKey},
    },
    util::arithmetic::{fe_to_limbs, CurveAffine, FieldExt},
    verifier::{self, PlonkVerifier},
    Protocol,
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use std::{iter, rc::Rc};

const LIMBS: usize = 4;
const BITS: usize = 68;
const T: usize = 17;
const RATE: usize = 16;
const R_F: usize = 8;
const R_P: usize = 10;

type Pcs = Kzg<Bn256, Bdfg21>;
type Svk = KzgSuccinctVerifyingKey<G1Affine>;
type As = KzgAs<Pcs>;
type AsPk = KzgAsProvingKey<G1Affine>;
type AsVk = KzgAsVerifyingKey;
type Plonk = verifier::Plonk<Pcs, LimbsEncoding<LIMBS, BITS>>;

type BaseFieldEccChip = halo2_wrong_ecc::BaseFieldEccChip<G1Affine, LIMBS, BITS>;
type Halo2Loader<'a> = halo2::Halo2Loader<'a, G1Affine, Fr, BaseFieldEccChip>;
type PoseidonTranscript<L, S, B> = system::circom::transcript::halo2::PoseidonTranscript<
    G1Affine,
    Fr,
    NativeRepresentation,
    L,
    S,
    B,
    LIMBS,
    BITS,
    T,
    RATE,
    R_F,
    R_P,
>;

#[derive(Clone)]
pub struct MainGateWithRangeConfig {
    main_gate_config: MainGateConfig,
    range_config: RangeConfig,
}

impl MainGateWithRangeConfig {
    pub fn configure<F: FieldExt>(
        meta: &mut ConstraintSystem<F>,
        composition_bits: Vec<usize>,
        overflow_bits: Vec<usize>,
    ) -> Self {
        let main_gate_config = MainGate::<F>::configure(meta);
        let range_config =
            RangeChip::<F>::configure(meta, &main_gate_config, composition_bits, overflow_bits);
        MainGateWithRangeConfig {
            main_gate_config,
            range_config,
        }
    }

    pub fn main_gate<F: FieldExt>(&self) -> MainGate<F> {
        MainGate::new(self.main_gate_config.clone())
    }

    pub fn range_chip<F: FieldExt>(&self) -> RangeChip<F> {
        RangeChip::new(self.range_config.clone())
    }

    pub fn ecc_chip<C: CurveAffine, const LIMBS: usize, const BITS: usize>(
        &self,
    ) -> halo2_wrong_ecc::BaseFieldEccChip<C, LIMBS, BITS> {
        halo2_wrong_ecc::BaseFieldEccChip::new(EccConfig::new(
            self.range_config.clone(),
            self.main_gate_config.clone(),
        ))
    }
}

pub struct SnarkWitness {
    protocol: Protocol<G1Affine>,
    instances: Vec<Vec<Value<Fr>>>,
    proof: Value<Vec<u8>>,
}

impl SnarkWitness {
    pub fn without_witnesses(&self) -> Self {
        SnarkWitness {
            protocol: self.protocol.clone(),
            instances: self
                .instances
                .iter()
                .map(|instances| vec![Value::unknown(); instances.len()])
                .collect(),
            proof: Value::unknown(),
        }
    }

    pub fn proof(&self) -> Value<&[u8]> {
        self.proof.as_ref().map(Vec::as_slice)
    }
}

pub fn accumulate<'a>(
    svk: &Svk,
    loader: &Rc<Halo2Loader<'a>>,
    snarks: &[SnarkWitness],
    as_vk: &AsVk,
    as_proof: Value<&'_ [u8]>,
) -> KzgAccumulator<G1Affine, Rc<Halo2Loader<'a>>> {
    let assign_instances = |instances: &[Vec<Value<Fr>>]| {
        instances
            .iter()
            .map(|instances| {
                instances
                    .iter()
                    .map(|instance| loader.assign_scalar(*instance))
                    .collect_vec()
            })
            .collect_vec()
    };

    let mut accumulators = snarks
        .iter()
        .flat_map(|snark| {
            let instances = assign_instances(&snark.instances);
            let mut transcript =
                PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, snark.proof());
            let proof =
                Plonk::read_proof(svk, &snark.protocol, &instances, &mut transcript).unwrap();
            Plonk::succinct_verify(svk, &snark.protocol, &instances, &proof).unwrap()
        })
        .collect_vec();

    let acccumulator = if accumulators.len() > 1 {
        let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, as_proof);
        let proof = As::read_proof(as_vk, &accumulators, &mut transcript).unwrap();
        As::verify(as_vk, &accumulators, &proof).unwrap()
    } else {
        accumulators.pop().unwrap()
    };

    acccumulator
}

struct Accumulation {
    svk: Svk,
    snarks: Vec<SnarkWitness>,
    instances: Vec<Fr>,
    as_vk: AsVk,
    as_proof: Value<Vec<u8>>,
}

impl Accumulation {
    pub fn new<const N: usize>(testdata: Testdata<N>) -> Self {
        let params =
            ParamsKZG::<Bn256>::setup(2 as u32, ChaCha20Rng::from_seed(Default::default()));

        let vk: VerifyingKey<Bn256> = serde_json::from_str(testdata.vk).unwrap();
        let protocol = compile(&vk);

        let public_signals = testdata
            .public_signals
            .iter()
            .map(|public_signals| {
                serde_json::from_str::<PublicSignals<Fr>>(public_signals).unwrap()
            })
            .collect_vec();
        let proofs = testdata
            .proofs
            .iter()
            .map(|proof| {
                serde_json::from_str::<Proof<Bn256>>(proof)
                    .unwrap()
                    .to_compressed_le()
            })
            .collect_vec();

        let mut accumulators = public_signals
            .iter()
            .zip(proofs.iter())
            .flat_map(|(public_signal, proof)| {
                let instances = [public_signal.clone().to_vec(); 1];
                let mut transcript =
                    PoseidonTranscript::<NativeLoader, _, _>::new(proof.as_slice());
                let proof =
                    Plonk::read_proof(&vk.svk().into(), &protocol, &instances, &mut transcript)
                        .unwrap();
                Plonk::succinct_verify(&vk.svk().into(), &protocol, &instances, &proof).unwrap()
            })
            .collect_vec();

        let as_pk = AsPk::new(Some((params.get_g()[0], params.get_g()[1])));
        let (accumulator, as_proof) = if accumulators.len() > 1 {
            let mut transcript = PoseidonTranscript::<NativeLoader, _, _>::new(Vec::new());
            let accumulator = As::create_proof(
                &as_pk,
                &accumulators,
                &mut transcript,
                ChaCha20Rng::from_seed(Default::default()),
            )
            .unwrap();
            (accumulator, Value::known(transcript.finalize()))
        } else {
            (accumulators.pop().unwrap(), Value::unknown())
        };

        let KzgAccumulator { lhs, rhs } = accumulator;
        let instances = [lhs.x, lhs.y, rhs.x, rhs.y]
            .map(fe_to_limbs::<_, _, LIMBS, BITS>)
            .concat();

        Self {
            svk: vk.svk().into(),
            snarks: public_signals
                .into_iter()
                .zip(proofs)
                .map(|(public_signals, proof)| SnarkWitness {
                    protocol: protocol.clone(),
                    instances: vec![public_signals
                        .to_vec()
                        .into_iter()
                        .map(Value::known)
                        .collect_vec()],
                    proof: Value::known(proof),
                })
                .collect(),
            instances,
            as_vk: as_pk.vk(),
            as_proof,
        }
    }

    pub fn as_proof(&self) -> Value<&[u8]> {
        self.as_proof.as_ref().map(Vec::as_slice)
    }
}

impl Circuit<Fr> for Accumulation {
    type Config = MainGateWithRangeConfig;
    type FloorPlanner = V1;

    fn without_witnesses(&self) -> Self {
        Self {
            svk: self.svk,
            snarks: self
                .snarks
                .iter()
                .map(SnarkWitness::without_witnesses)
                .collect(),
            instances: self.instances.clone(),
            as_vk: self.as_vk,
            as_proof: Value::unknown(),
        }
    }

    fn configure(meta: &mut ConstraintSystem<Fr>) -> Self::Config {
        MainGateWithRangeConfig::configure::<Fr>(
            meta,
            vec![BITS / LIMBS],
            Rns::<Fq, Fr, LIMBS, BITS>::construct().overflow_lengths(),
        )
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<Fr>,
    ) -> Result<(), plonk::Error> {
        let main_gate = config.main_gate();
        let range_chip = config.range_chip();

        range_chip.load_table(&mut layouter)?;

        let (lhs, rhs) = layouter.assign_region(
            || "",
            |region| {
                let ctx = RegionCtx::new(region, 0);

                let ecc_chip = config.ecc_chip();
                let loader = Halo2Loader::new(ecc_chip, ctx);
                let KzgAccumulator { lhs, rhs } = accumulate(
                    &self.svk,
                    &loader,
                    &self.snarks,
                    &self.as_vk,
                    self.as_proof(),
                );

                // loader.print_row_metering();
                // println!("Total row cost: {}", loader.ctx().offset());

                Ok((lhs.assigned(), rhs.assigned()))
            },
        )?;

        for (limb, row) in iter::empty()
            .chain(lhs.x().limbs())
            .chain(lhs.y().limbs())
            .chain(rhs.x().limbs())
            .chain(rhs.y().limbs())
            .zip(0..)
        {
            main_gate.expose_public(layouter.namespace(|| ""), limb.into(), row)?;
        }

        Ok(())
    }
}

pub struct Testdata<const N: usize> {
    pub vk: &'static str,
    pub proofs: [&'static str; N],
    pub public_signals: [&'static str; N],
}

fn main() {}

// pub const TESTDATA_HALO2: Testdata<1> = Testdata {
//     vk: r#"
// {
//  "protocol": "plonk",
//  "curve": "bn128",
//  "nPublic": 1,
//  "power": 11,
//  "k1": "2",
//  "k2": "3",
//  "Qm": [
//   "3349529800503134758031206628826762579744090389775720856324415703418132588272",
//   "1047380119467254909383032258743707561779783672376181143324721807183433895005",
//   "1"
//  ],
//  "Ql": [
//   "7767045214241100521202624210544067470568603896753786311669908116745944438330",
//   "2761503195407699512821418421837091792920914786423811892261268458108417046825",
//   "1"
//  ],
//  "Qr": [
//   "2975170524298576570303711212258436671762476108775473882749069044845953535499",
//   "14378372896685219137765897674012660076935852372658477152445798047040143090024",
//   "1"
//  ],
//  "Qo": [
//   "9954726969673494279518385350127630762618300791674628690913856164268433703179",
//   "13965759471775973075363285410020114951590804896282136534205026646287563189772",
//   "1"
//  ],
//  "Qc": [
//   "16212144331199537797769995963505212438301349409393139691774264125327619032439",
//   "17085616814509624070169907909376975087673229154027196667482507285696043222953",
//   "1"
//  ],
//  "S1": [
//   "21427438936074527438404157582664231491469818071679458860143386701810092744404",
//   "19911030453621062116641782598975750504385985365438849435660556532368164383429",
//   "1"
//  ],
//  "S2": [
//   "13802677720850567775992768839702562890586195816216161661887530587428202866726",
//   "7079192343351352262490439774376827531848577755489091121777421558213991392309",
//   "1"
//  ],
//  "S3": [
//   "7382434879293711723612677553350129386486281744510841088538187725327021521690",
//   "11862269561183216572203078221388721953182973401672938240744501637694249454749",
//   "1"
//  ],
//  "X_2": [
//   [
//    "17697945884356840746175007528786997911945651836283409056261355173034919217326",
//    "11501088178268619001213046246621713845912613526390023569108826835703460118408"
//   ],
//   [
//    "2426853463090583396092113656235496011757344467781401934015976708559998134240",
//    "18934756257331934407911971941197693338781042972388885568003065304450754441155"
//   ],
//   [
//    "1",
//    "0"
//   ]
//  ],
//  "w": "1120550406532664055539694724667294622065367841900378087843176726913374367458"
// }
//     "#,
//     proofs: [r#"{
//  "A": [
//   "11061059603189782590330418259165078776630514368672082688811243104044860101540",
//   "21668757428762543016671135403653337903225051298789513367270755978051709738572",
//   "1"
//  ],
//  "B": [
//   "15086270057259696475553262311245448542212613657734428927573100611839505480405",
//   "15018511197851761273177786510821312288823130543628495195956277770824042190722",
//   "1"
//  ],
//  "C": [
//   "14972338772264545077554193622334454585886430717733475952116247858333029051612",
//   "18054617390851292490340784872096307735301268676836314087254309676459499099352",
//   "1"
//  ],
//  "Z": [
//   "14382338141451024608292942544807617949449861494221150754991236959826838416669",
//   "10385796778063295246729293672521215747529662283495782347357027111939539405273",
//   "1"
//  ],
//  "T1": [
//   "12751261278277586544140220350597873383550169238072927910121553847855318517163",
//   "10945599048902805478868261214279777223927364741842524822724265316476458100695",
//   "1"
//  ],
//  "T2": [
//   "5973795993600689757811815813854288461127743059999624555641758467641758046626",
//   "8726815948989040187593929257900012211722987404525002145019657362525782979044",
//   "1"
//  ],
//  "T3": [
//   "21072089102306420569765505555148563215048857791981467046074242987486533089930",
//   "17535943633965333368863208309663816996221234488938464214457981145265544794225",
//   "1"
//  ],
//  "eval_a": "19726214196348323683839603021032263816939421240984180066385077192452675481471",
//  "eval_b": "2333267538690138233648092707823188338618694351416835528648245962758838356337",
//  "eval_c": "10971899192792562347132356007458724596801409552494366719278016565035749074651",
//  "eval_s1": "6159818742975066475291358495938614244240245684888756593045209785852937729279",
//  "eval_s2": "15197205121556034064086123849398780541310753223034430556904169800753100031633",
//  "eval_zw": "5530376799911596881715592680894011517238842016192161340525184837122297439950",
//  "eval_r": "19659936227615256346904535692177058613252049032763580820688462126145909608495",
//  "Wxi": [
//   "6740641879457334845854395780205816355956771529536935615443431702468550162214",
//   "21183255617191143724097347727344457324556551775846802887934369815266291584190",
//   "1"
//  ],
//  "Wxiw": [
//   "21335840114976920556842587201078357495072120383201015684328760344203390789325",
//   "8096904663846811709871156788274714302796579221932332607896751009422510513707",
//   "1"
//  ],
//  "protocol": "plonk",
//  "curve": "bn128"
// }"#],
//     public_signals: [r#"[
//  "16071293540883839718875621424443923800287184249862748659884745950088030321914"
// ]"#],
// };

// #[derive(Parser)]
// struct Cli {
//     vk: std::path::PathBuf,
//     proofs_dir: std::path::PathBuf,
//     public_signals_dir: std::path::PathBuf,
//     count: usize,
// }

// fn parse_cmds() {
//     // (1) Read files into Testdata struct
//     // (2) Check whether it works
//     // (3) Export solidity verifier bytecode
//     // (4)
//     let args = Cli::parse();
//     // let d = File::open("path").unwrap();
// }

// fn main() {
//     let params = gen_srs(21);
//     let params_app = {
//         let mut params = params.clone();
//         params.downsize(8);
//         params
//     };

//     let agg_circuit = AggregationCircuit::new(TESTDATA_HALO2);
//     let pk = gen_pk(&params, &agg_circuit);
//     let deployment_code = gen_aggregation_evm_verifier(
//         &params,
//         pk.get_vk(),
//         aggregation::AggregationCircuit::num_instance(),
//         aggregation::AggregationCircuit::accumulator_indices(),
//     );

//     let proof = gen_proof::<_, _, EvmTranscript<G1Affine, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
//         &params,
//         &pk,
//         agg_circuit.clone(),
//         agg_circuit.instances(),
//     );
//     evm_verify(deployment_code, agg_circuit.instances(), proof);
// }
