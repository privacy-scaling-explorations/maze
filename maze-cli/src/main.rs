use anyhow::Context;
use clap::Parser;
use ethereum_types::Address;
use foundry_evm::executor::{fork::MultiFork, Backend, ExecutorBuilder};
use halo2_curves::bn256::{Bn256, Fq, Fr, G1Affine};
use halo2_kzg_srs::{Srs, SrsFormat};
use halo2_proofs::{
    circuit::{floor_planner::V1, Layouter, Value},
    dev::MockProver,
    plonk::{
        self, create_proof, keygen_pk, keygen_vk, verify_proof, Circuit, ConstraintSystem,
        ProvingKey, VerifyingKey as PlonkVerifyingKey,
    },
    poly::{
        commitment::{Params, ParamsProver},
        kzg::{
            commitment::{KZGCommitmentScheme, ParamsKZG},
            multiopen::{ProverGWC, VerifierGWC},
            strategy::AccumulatorStrategy,
        },
        VerificationStrategy,
    },
    transcript::{EncodedChallenge, TranscriptReadBuffer, TranscriptWriterBuffer},
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
        evm::{encode_calldata, EvmLoader},
        halo2::{self},
        native::NativeLoader,
    },
    pcs::{
        kzg::{
            Bdfg21, Kzg, KzgAccumulator, KzgAs, KzgAsProvingKey, KzgAsVerifyingKey,
            KzgSuccinctVerifyingKey, LimbsEncoding,
        },
        AccumulationScheme, AccumulationSchemeProver,
    },
    system::{
        self,
        circom::{compile, Proof, PublicSignals, VerifyingKey},
        halo2::{compile as compile_halo2, transcript::evm::EvmTranscript, Config},
    },
    util::arithmetic::{fe_to_limbs, CurveAffine, FieldExt},
    verifier::{self, PlonkVerifier},
    Protocol,
};
use rand::{rngs::OsRng, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::{ffi::OsStr, fmt::format, io::Cursor, iter, path::PathBuf, rc::Rc};

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
    pub fn new(
        params: ParamsKZG<Bn256>,
        vk: VerifyingKey<Bn256>,
        public_signals: Vec<PublicSignals<Fr>>,
        proofs: Vec<Proof<Bn256>>,
    ) -> Self {
        print!("Building circuit!");
        let protocol = compile(&vk);
        let proofs: Vec<Vec<u8>> = proofs.iter().map(|p| p.to_compressed_le()).collect();

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

    pub fn accumulator_indices() -> Vec<(usize, usize)> {
        (0..4 * LIMBS).map(|idx| (0, idx)).collect()
    }

    pub fn num_instance() -> Vec<usize> {
        vec![4 * LIMBS]
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

fn gen_proof<
    C: Circuit<Fr>,
    E: EncodedChallenge<G1Affine>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    pk: &ProvingKey<G1Affine>,
    circuit: C,
    instances: Vec<Vec<Fr>>,
) -> Vec<u8> {
    MockProver::run(params.k(), &circuit, instances.clone())
        .unwrap()
        .assert_satisfied();

    let instances = instances
        .iter()
        .map(|instances| instances.as_slice())
        .collect_vec();
    let proof = {
        let mut transcript = TW::init(Vec::new());
        create_proof::<KZGCommitmentScheme<Bn256>, ProverGWC<_>, _, _, TW, _>(
            params,
            pk,
            &[circuit],
            &[instances.as_slice()],
            OsRng,
            &mut transcript,
        )
        .unwrap();
        transcript.finalize()
    };

    let accept = {
        let mut transcript = TR::init(Cursor::new(proof.clone()));
        VerificationStrategy::<_, VerifierGWC<_>>::finalize(
            verify_proof::<_, VerifierGWC<_>, _, TR, _>(
                params.verifier_params(),
                pk.get_vk(),
                AccumulatorStrategy::new(params.verifier_params()),
                &[instances.as_slice()],
                &mut transcript,
            )
            .unwrap(),
        )
    };
    assert!(accept);

    proof
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    print!("Generating proving key!");
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_aggregation_evm_verifier(
    vk: &VerifyingKey<Bn256>,
    params: &ParamsKZG<Bn256>,
    plonk_vk: &PlonkVerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
    accumulator_indices: Vec<(usize, usize)>,
) -> Vec<u8> {
    println!("Generating evm verifier bytecode!");
    let svk = vk.svk().into();
    let dk = vk.dk().into();

    let protocol = compile_halo2(
        params,
        plonk_vk,
        Config::kzg()
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(accumulator_indices),
    );

    let loader = EvmLoader::new::<Fq, Fr>();
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(loader.clone());

    let instances = transcript.load_instances(num_instance);
    let proof = Plonk::read_proof(&svk, &protocol, &instances, &mut transcript).unwrap();
    Plonk::verify(&svk, &dk, &protocol, &instances, &proof).unwrap();

    loader.deployment_code()
}

fn evm_verify(deployment_code: Vec<u8>, instances: Vec<Vec<Fr>>, proof: Vec<u8>) {
    let calldata = encode_calldata(&instances, &proof);
    let success = {
        let mut evm = ExecutorBuilder::default()
            .with_gas_limit(u64::MAX.into())
            .build(Backend::new(MultiFork::new().0, None));

        let caller = Address::from_low_u64_be(0xfe);
        let verifier = evm
            .deploy(caller, deployment_code.into(), 0.into(), None)
            .unwrap()
            .address;
        let result = evm
            .call_raw(caller, verifier, calldata.into(), 0.into())
            .unwrap();

        dbg!(result.gas_used);

        !result.reverted
    };
    assert!(success);
}

pub struct Data<const N: usize> {
    pub vk: &'static str,
    pub proofs: [&'static str; N],
    pub public_signals: [&'static str; N],
}

fn prepare_params(path: PathBuf) -> anyhow::Result<ParamsKZG<Bn256>> {
    let params = match path.extension() {
        Some(ext) => match ext.to_str().unwrap() {
            "ptau" => Ok(Srs::<Bn256>::read(
                &mut std::fs::File::open(path)
                    .with_context(|| format!("Failed to read srs file"))?,
                SrsFormat::SnarkJs,
            )),
            "srs" => Ok(Srs::<Bn256>::read(
                &mut std::fs::File::open(path)
                    .with_context(|| format!("Failed to read srs file"))?,
                SrsFormat::Pse,
            )),
            _ => Err(anyhow::Error::msg(
                "Only .ptau or .srs files allowed for srs",
            )),
        },
        None => Err(anyhow::Error::msg("No file exists for srs")),
    }
    .and_then(|srs| {
        let mut buf = Vec::new();
        srs.write(&mut buf);
        let params = ParamsKZG::<Bn256>::read(&mut std::io::Cursor::new(buf))
            .with_context(|| "Error in reading srs to ParamsKzg")?;
        Ok(params)
    })?;

    Ok(params)
}

fn create_and_save_srs(dir_path: PathBuf, k: usize) -> anyhow::Result<ParamsKZG<Bn256>> {
    println!("Generating new srs for k:{}", k);
    std::fs::create_dir_all(dir_path.clone()).with_context(|| "Unable to locate directory")?;

    let params = ParamsKZG::<Bn256>::setup(k as u32, OsRng);
    let mut file_path = dir_path;
    file_path.extend(vec![format!("k-{}.srs", k)]);
    let mut file = std::fs::File::create(file_path).with_context(|| "Unable to create new file")?;
    params.write(&mut file)?;

    Ok(params)
}

fn prepare_circom_vk(path: PathBuf) -> anyhow::Result<VerifyingKey<Bn256>> {
    print!("Reading verification key!");
    let vk =
        std::fs::read_to_string(&path).with_context(|| "Unable to find verification key file")?;
    let vk: VerifyingKey<Bn256> =
        serde_json::from_str(vk.as_str()).with_context(|| "Malformed verification key")?;
    Ok(vk)
}

fn prepare_circom_inputs(
    path: PathBuf,
    count: usize,
) -> anyhow::Result<(Vec<Proof<Bn256>>, Vec<PublicSignals<Fr>>)> {
    let mut proofs: Vec<Proof<Bn256>> = vec![];
    let mut public_signals: Vec<PublicSignals<Fr>> = vec![];

    for i in 0..count {
        let mut proof = path.clone();
        proof.extend(vec![format!("proof{}.json", i + 1)]);
        let proof = std::fs::read_to_string(proof)
            .with_context(|| format!("Unable to read proof{}.json", i + 1))?;
        let proof = serde_json::from_str::<Proof<Bn256>>(&proof)
            .with_context(|| format!("Malformed proof{}.json", i + 1))?;
        proofs.push(proof);

        let mut public = path.clone();
        public.extend(vec![format!("public{}.json", i + 1)]);
        let public = std::fs::read_to_string(public)
            .with_context(|| format!("Unable to read public{}.json", i + 1))?;
        let public = serde_json::from_str::<PublicSignals<Fr>>(&public)
            .with_context(|| format!("Malformed public{}.json", i + 1))?;
        public_signals.push(public);
    }

    Ok((proofs, public_signals))
}

#[derive(Parser)]
struct Cli {
    vk: PathBuf,
    input_dir: PathBuf,
    ptau: PathBuf,
    count: usize,
}

fn main() {
    let args = Cli::parse();

    create_and_save_srs("./testdata".into(), 21).unwrap();

    let params = match prepare_params(args.ptau.clone()) {
        Ok(params) => params,
        Err(e) => {
            eprintln!("{}", e);
            println!("Preparing params. Note this must not be used in production");
            ParamsKZG::<Bn256>::setup(2, OsRng)
        }
    };

    let circom_vk = prepare_circom_vk(args.vk.clone()).unwrap();
    let (proofs, public_signals) =
        prepare_circom_inputs(args.input_dir.clone(), args.count).unwrap();

    // building circuit
    let circuit = Accumulation::new(params.clone(), circom_vk.clone(), public_signals, proofs);

    // mock proving circuit
    // println!("Running mock prover");
    // let mock_prover = MockProver::run(21, &circuit, vec![circuit.instances.clone()]).unwrap();
    // mock_prover.assert_satisfied();

    // proving key
    let proving_key = gen_pk(&params, &circuit);
    let verification_key = proving_key.get_vk();

    // bytecode generation
    println!("Generating evm verifier bytecode");
    let bytecode = gen_aggregation_evm_verifier(
        &circom_vk,
        &params,
        verification_key,
        Accumulation::num_instance(),
        Accumulation::accumulator_indices(),
    );
    print!("bytecode generated {:?}", bytecode);

    //
}

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
