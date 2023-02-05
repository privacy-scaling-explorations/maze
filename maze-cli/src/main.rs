use anyhow::Context;
use clap::{Parser, Subcommand};
use colored::Colorize;

use ethereum_types::Address;
use foundry_evm::executor::{fork::MultiFork, Backend, ExecutorBuilder, RawCallResult};
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
    cost::CostEstimation,
    loader::{
        evm::{encode_calldata, EvmLoader},
        halo2::{self},
        native::NativeLoader,
    },
    pcs::{
        kzg::{
            Gwc19, Kzg, KzgAccumulator, KzgAs, KzgAsProvingKey, KzgAsVerifyingKey,
            KzgSuccinctVerifyingKey, LimbsEncoding,
        },
        AccumulationScheme, AccumulationSchemeProver, Decider,
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
use std::{
    io::{Cursor, Write},
    iter,
    path::PathBuf,
    rc::Rc,
    time::Instant,
};
use utils::DimensionMeasurement;

mod utils;

const LIMBS: usize = 4;
const BITS: usize = 68;
const T: usize = 17;
const RATE: usize = 16;
const R_F: usize = 8;
const R_P: usize = 10;

type Pcs = Kzg<Bn256, Gwc19>;
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

#[derive(Clone)]
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

    let accumulator = if accumulators.len() > 1 {
        let mut transcript = PoseidonTranscript::<Rc<Halo2Loader>, _, _>::new(loader, as_proof);
        let proof = As::read_proof(as_vk, &accumulators, &mut transcript).unwrap();
        As::verify(as_vk, &accumulators, &proof).unwrap()
    } else {
        accumulators.pop().unwrap()
    };

    accumulator
}

#[derive(Clone)]
struct Accumulation {
    svk: Svk,
    snarks: Vec<SnarkWitness>,
    instances: Vec<Fr>,
    as_vk: AsVk,
    as_proof: Value<Vec<u8>>,
}

impl Accumulation {
    pub fn new(
        vk: VerifyingKey<Bn256>,
        public_signals: Vec<PublicSignals<Fr>>,
        proofs: Vec<Proof<Bn256>>,
    ) -> Self {
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

        let as_pk = AsPk::new(Some(vk.apk()));
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

        assert!(Pcs::decide(&vk.dk().into(), accumulator.clone()));

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

    pub fn instances(&self) -> Vec<Vec<Fr>> {
        vec![self.instances.clone()]
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
) -> (Vec<u8>, bool) {
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

    (proof, accept)
}

fn check_proof<
    E: EncodedChallenge<G1Affine>,
    TR: TranscriptReadBuffer<Cursor<Vec<u8>>, G1Affine, E>,
    TW: TranscriptWriterBuffer<Vec<u8>, G1Affine, E>,
>(
    params: &ParamsKZG<Bn256>,
    vk: &PlonkVerifyingKey<G1Affine>,
    instances: Vec<Vec<Fr>>,
    proof: Vec<u8>,
) -> bool {
    let instances = instances
        .iter()
        .map(|instances| instances.as_slice())
        .collect_vec();
    let mut transcript = TR::init(Cursor::new(proof.clone()));
    VerificationStrategy::<_, VerifierGWC<_>>::finalize(
        verify_proof::<_, VerifierGWC<_>, _, TR, _>(
            params.verifier_params(),
            vk,
            AccumulatorStrategy::new(params.verifier_params()),
            &[instances.as_slice()],
            &mut transcript,
        )
        .unwrap(),
    )
}

fn gen_pk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> ProvingKey<G1Affine> {
    let vk = keygen_vk(params, circuit).unwrap();
    keygen_pk(params, vk, circuit).unwrap()
}

fn gen_vk<C: Circuit<Fr>>(params: &ParamsKZG<Bn256>, circuit: &C) -> PlonkVerifyingKey<G1Affine> {
    keygen_vk(params, circuit).unwrap()
}

fn gen_aggregation_evm_verifier(
    vk: &VerifyingKey<Bn256>,
    params: &ParamsKZG<Bn256>,
    plonk_vk: &PlonkVerifyingKey<G1Affine>,
    num_instance: Vec<usize>,
    accumulator_indices: Vec<(usize, usize)>,
) -> Vec<u8> {
    let svk = vk.svk().into();
    let dk = vk.dk().into();

    let protocol = compile_halo2(
        params,
        plonk_vk,
        Config::kzg()
            .with_num_instance(num_instance.clone())
            .with_accumulator_indices(accumulator_indices),
    );

    verifier::Plonk::<Kzg<Bn256, Gwc19>>::estimate_cost(&protocol);

    let loader = EvmLoader::new::<Fq, Fr>();
    let mut transcript = EvmTranscript::<_, Rc<EvmLoader>, _, _>::new(loader.clone());

    let instances = transcript.load_instances(num_instance);
    let proof = Plonk::read_proof(&svk, &protocol, &instances, &mut transcript).unwrap();
    Plonk::verify(&svk, &dk, &protocol, &instances, &proof).unwrap();

    loader.deployment_code()
}

fn evm_verify(deployment_code: Vec<u8>, calldata: Vec<u8>) -> anyhow::Result<RawCallResult> {
    let mut evm = ExecutorBuilder::default()
        .with_gas_limit(u64::MAX.into())
        .build(Backend::new(MultiFork::new().0, None));

    let caller = Address::from_low_u64_be(0xfe);
    let verifier = evm.deploy(caller, deployment_code.into(), 0.into(), None)?;
    match evm.call_raw(caller, verifier.address, calldata.into(), 0.into()) {
        Ok(result) => Ok(result),
        Err(e) => Err(anyhow::anyhow!(e.to_string())),
    }
}

fn prepare_params(path: PathBuf) -> anyhow::Result<ParamsKZG<Bn256>> {
    let params = match path.extension() {
        Some(ext) => match ext.to_str().unwrap() {
            "ptau" => Ok(Srs::<Bn256>::read(
                &mut std::fs::File::open(path.clone()).with_context(|| {
                    format!("Failed to read .ptau file {}", path.to_str().unwrap())
                })?,
                SrsFormat::SnarkJs,
            )),
            "srs" => Ok(Srs::<Bn256>::read(
                &mut std::fs::File::open(path.clone()).with_context(|| {
                    format!("Failed to read .srs file {}", path.to_str().unwrap())
                })?,
                SrsFormat::Pse,
            )),
            _ => Err(anyhow::Error::msg(
                "Invalid file extension. Only .ptau or .srs files allowed for params",
            )),
        },
        None => Err(anyhow::Error::msg("Invalid file path for params")),
    }
    .and_then(|srs| {
        let mut buf = Vec::new();
        srs.write(&mut buf);
        let params = ParamsKZG::<Bn256>::read(&mut std::io::Cursor::new(buf))
            .with_context(|| "Malformed params file")?;
        Ok(params)
    })?;

    Ok(params)
}

fn gen_srs(k: u32) -> ParamsKZG<Bn256> {
    ParamsKZG::<Bn256>::setup(k, OsRng)
}

fn create_and_save_srs(dir_path: PathBuf, k: usize) -> anyhow::Result<ParamsKZG<Bn256>> {
    std::fs::create_dir_all(dir_path.clone()).with_context(|| {
        format!(
            "Failed to locate directory at {}",
            dir_path.to_str().unwrap()
        )
    })?;

    let params = gen_srs(k as u32);
    let mut file_path = dir_path;
    file_path.extend(vec![format!("k-{}.srs", k)]);
    let mut file = std::fs::File::create(file_path.clone()).with_context(|| {
        format!(
            "Failed to create new file at {}",
            file_path.to_str().unwrap()
        )
    })?;
    params.write(&mut file)?;

    Ok(params)
}

fn prepare_circom_vk(path: PathBuf) -> anyhow::Result<VerifyingKey<Bn256>> {
    let vk = std::fs::read_to_string(&path).with_context(|| {
        format!(
            "Failed to locate verification key at {}",
            path.to_str().unwrap()
        )
    })?;
    let vk: VerifyingKey<Bn256> =
        serde_json::from_str(vk.as_str()).with_context(|| "Malformed verification key")?;
    Ok(vk)
}

fn prepare_proofs(path: PathBuf) -> anyhow::Result<Vec<Proof<Bn256>>> {
    let str = std::fs::read_to_string(path.clone())
        .with_context(|| format!("Failed to locate {}", path.to_str().unwrap()))?;
    let proofs = serde_json::from_str::<Vec<Proof<Bn256>>>(&str)?;
    Ok(proofs)
}

fn prepare_public_signals(path: PathBuf) -> anyhow::Result<Vec<PublicSignals<Fr>>> {
    let str = std::fs::read_to_string(path.clone())
        .with_context(|| format!("Failed to locate {}", path.to_str().unwrap()))?;
    let public_signals = serde_json::from_str::<Vec<PublicSignals<Fr>>>(&str)?;
    Ok(public_signals)
}

#[derive(Parser)]
#[command(author, version, about, long_about = None)]
#[command(next_line_help = true)]
struct Cli {
    #[command(subcommand)]
    command: Option<Commands>,
}

#[derive(Subcommand)]
enum Commands {
    /// Setup mock
    MockSetup {
        verification_key: PathBuf,
        proofs: PathBuf,
        public_signals: PathBuf,
    },

    /// Generates EVM verifier
    GenEvmVerifier {
        verification_key: PathBuf,
        proofs: PathBuf,
        public_signals: PathBuf,
        params: PathBuf,
        output_dir: PathBuf,
    },

    /// Create proof
    CreateProof {
        verification_key: PathBuf,
        proofs: PathBuf,
        public_signals: PathBuf,
        params: PathBuf,
        output_dir: PathBuf,
    },

    /// Verify proof
    VerifyProof {
        verification_key: PathBuf,
        proofs: PathBuf,
        public_signals: PathBuf,
        proof_file: PathBuf,
        params: PathBuf,
    },

    /// EVM proof verify
    EvmVerifyProof {
        calldata: PathBuf,
        evmbytecode: PathBuf,
    },

    /// Create Params
    CreateParams { k: usize, output_dir: PathBuf },
}

fn report_elapsed(now: Instant) {
    println!(
        "{}",
        format!("Took {} seconds", now.elapsed().as_secs())
            .blue()
            .bold()
    );
}

fn main() {
    let cli = Cli::parse();

    match cli.command {
        Some(Commands::GenEvmVerifier {
            verification_key,
            proofs,
            public_signals,
            params,
            output_dir,
        }) => {
            println!(
                "{}",
                "Reading circom-plonk verification key, proofs, and public signals"
                    .white()
                    .bold()
            );
            let ((circom_vk, proofs), public_signals) = {
                match prepare_circom_vk(verification_key)
                    .and_then(|prev| {
                        let proofs = prepare_proofs(proofs)?;
                        Ok((prev, proofs))
                    })
                    .and_then(|prev| {
                        let ps = prepare_public_signals(public_signals)?;
                        Ok((prev, ps))
                    }) {
                    Ok(res) => res,
                    Err(e) => {
                        println!("{}", format!("{:#?}", e).red());
                        std::process::exit(1);
                    }
                }
            };
            assert!(proofs.len() == public_signals.len());
            println!();

            println!(
                "{}",
                format!("Building aggregation circuit for {} proofs", proofs.len())
                    .white()
                    .bold()
            );
            let circuit = Accumulation::new(circom_vk.clone(), public_signals, proofs);
            println!();

            // mock proving circuit
            println!(
                "{}",
                "Running mock prover for aggregation circuit".white().bold()
            );
            let now = Instant::now();
            match MockProver::run(3, &circuit, vec![circuit.instances.clone()])
                .with_context(|| "Mock prover failed")
            {
                Ok(mock_prover) => match mock_prover.verify() {
                    Ok(_) => {}
                    Err(errs) => {
                        println!("{}", "Mock prover failed with errors:".red());
                        errs.iter()
                            .for_each(|e| println!("{}", e.to_string().red()));
                    }
                },
                Err(e) => {
                    println!("{}", e.to_string().red());
                }
            }
            report_elapsed(now);
            println!();

            println!(
                "{}",
                "Reading parameters for commitment scheme".white().bold()
            );
            let now = Instant::now();
            let params = match prepare_params(params) {
                Ok(params) => params,
                Err(e) => {
                    println!("{}", e.to_string().red());
                    std::process::exit(1);
                }
            };
            report_elapsed(now);
            println!();

            println!("{}", "Generating evm verifier".white().bold());
            let now = Instant::now();
            let proving_key = gen_pk(&params, &circuit);
            let verification_key = proving_key.get_vk();
            let evm_bytecode = gen_aggregation_evm_verifier(
                &circom_vk,
                &params,
                verification_key,
                Accumulation::num_instance(),
                Accumulation::accumulator_indices(),
            );

            match std::fs::create_dir_all(output_dir.clone())
                .with_context(|| {
                    format!(
                        "Failed to locate directory at {}",
                        output_dir.to_str().unwrap()
                    )
                })
                .and_then(|_| {
                    let mut file_path = output_dir;
                    file_path.extend(vec!["evm-verifier.txt"]);
                    std::fs::File::create(file_path.clone())
                        .with_context(|| {
                            format!(
                                "Failed to create new file at {}",
                                file_path.to_str().unwrap()
                            )
                        })
                        .and_then(|mut file| {
                            file.write_all(&evm_bytecode).with_context(|| {
                                format!(
                                    "Failed to write evm verifier to {}",
                                    file_path.to_str().unwrap()
                                )
                            })
                        })
                }) {
                Ok(_) => {}
                Err(e) => {
                    println!("{}", e.to_string().red());
                    std::process::exit(1);
                }
            }
            report_elapsed(now);
            println!("{}", "Success".green());
        }
        Some(Commands::MockSetup {
            verification_key,
            proofs,
            public_signals,
        }) => {
            println!(
                "{}",
                "Reading circom-plonk verification key, proofs, and public signals"
                    .white()
                    .bold()
            );
            let ((circom_vk, proofs), public_signals) = {
                match prepare_circom_vk(verification_key)
                    .and_then(|prev| {
                        let proofs = prepare_proofs(proofs)?;
                        Ok((prev, proofs))
                    })
                    .and_then(|prev| {
                        let ps = prepare_public_signals(public_signals)?;
                        Ok((prev, ps))
                    }) {
                    Ok(res) => res,
                    Err(e) => {
                        println!("{}", format!("{:#?}", e).red());
                        std::process::exit(1);
                    }
                }
            };
            assert!(proofs.len() == public_signals.len());
            println!();

            println!(
                "{}",
                format!("Building aggregation circuit for {} proofs", proofs.len())
                    .white()
                    .bold()
            );
            let circuit = Accumulation::new(circom_vk.clone(), public_signals, proofs);
            println!();

            // mock proving circuit
            println!(
                "{}",
                "Running mock prover for aggregation circuit".white().bold()
            );
            let now = Instant::now();
            let dimension = DimensionMeasurement::measure(&circuit).unwrap();
            match MockProver::run(dimension.k(), &circuit, vec![circuit.instances.clone()])
                .with_context(|| "Mock prover failed")
            {
                Ok(mock_prover) => match mock_prover.verify() {
                    Ok(_) => {
                        println!("{}", "Success".green().bold());
                    }
                    Err(errs) => {
                        println!("{}", "Mock prover failed with errors:".red().bold());
                        errs.iter()
                            .for_each(|e| println!("{}", e.to_string().red().bold()));
                    }
                },
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red().bold());
                }
            }
            println!("{}", format!("k:{}", dimension.k()).blue().bold());
            report_elapsed(now);
        }
        Some(Commands::CreateProof {
            verification_key,
            proofs,
            public_signals,
            params,
            output_dir,
        }) => {
            println!(
                "{}",
                "Reading circom-plonk verification key, proofs, and public signals"
                    .white()
                    .bold()
            );
            let ((circom_vk, proofs), public_signals) = {
                match prepare_circom_vk(verification_key)
                    .and_then(|prev| {
                        let proofs = prepare_proofs(proofs)?;
                        Ok((prev, proofs))
                    })
                    .and_then(|prev| {
                        let ps = prepare_public_signals(public_signals)?;
                        Ok((prev, ps))
                    }) {
                    Ok(res) => res,
                    Err(e) => {
                        println!("{}", format!("{:#?}", e).red());
                        std::process::exit(1);
                    }
                }
            };
            assert!(proofs.len() == public_signals.len());
            println!();

            println!("{}", "Reading parameters for the circuit".white().bold());
            let now = Instant::now();
            let params = match prepare_params(params) {
                Ok(params) => params,
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                    std::process::exit(1);
                }
            };
            report_elapsed(now);
            println!();

            println!(
                "{}",
                format!("Building aggregation circuit for {} proofs", proofs.len())
                    .white()
                    .bold()
            );
            let circuit = Accumulation::new(circom_vk.clone(), public_signals, proofs);
            println!();

            // Make sure output_dir is accessible and can create
            // necessary files for storing the proof.
            // This is for precaution.
            match std::fs::create_dir_all(output_dir.clone())
                .with_context(|| {
                    format!(
                        "Failed to locate directory at {}",
                        output_dir.to_str().unwrap()
                    )
                })
                .and_then(|_| {
                    for i in ["proof", "evm-calldata"] {
                        let mut file_path = output_dir.clone();
                        file_path.extend(vec![format!("halo2-agg-{}.txt", i)]);
                        std::fs::File::create(file_path.clone()).with_context(|| {
                            format!(
                                "Failed to create new file at {}",
                                file_path.to_str().unwrap()
                            )
                        })?;
                    }
                    Ok(())
                }) {
                Ok(_) => {}
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                    std::process::exit(1);
                }
            }

            println!("{}", "Generating proving key".white().bold());
            let now = Instant::now();
            let pk = gen_pk(&params, &circuit);
            report_elapsed(now);
            println!();

            println!("{}", "Generating proof".white().bold());
            let now = Instant::now();
            let (proof, is_valid) = gen_proof::<
                _,
                _,
                EvmTranscript<G1Affine, _, _, _>,
                EvmTranscript<G1Affine, _, _, _>,
            >(
                &params, &pk, circuit.clone(), circuit.instances()
            );
            report_elapsed(now);
            if !is_valid {
                println!("{}", "Invalid proof generation".red().bold());
            }

            let calldata = encode_calldata(&circuit.instances(), &proof);
            for i in [("proof", proof.clone()), ("evm-calldata", calldata.clone())] {
                let mut file_path = output_dir.clone();
                file_path.extend(vec![format!("halo2-agg-{}.txt", i.0)]);
                match std::fs::File::create(file_path.clone())
                    .with_context(|| {
                        format!(
                            "Failed to open file at {}",
                            file_path.clone().to_str().unwrap()
                        )
                    })
                    .and_then(|mut file| {
                        file.write_all(&i.1).with_context(|| {
                            format!("Failed to write to file at {}", file_path.to_str().unwrap())
                        })
                    }) {
                    Ok(_) => {}
                    Err(e) => {
                        println!("{}", format!("{:#?}", e).red());
                    }
                }
            }
            println!();

            println!("{}", "Simulating evm verification".white().bold());
            let verification_key = pk.get_vk();
            let evm_bytecode = gen_aggregation_evm_verifier(
                &circom_vk,
                &params,
                verification_key,
                Accumulation::num_instance(),
                Accumulation::accumulator_indices(),
            );
            match evm_verify(evm_bytecode, calldata.clone())
                .with_context(|| "Simulating evm verification failed")
            {
                Ok(result) => {
                    println!("{}", format!("Gas used: {}", result.gas_used).blue());
                    if result.reverted {
                        println!("{}", "Verification failed".red())
                    } else {
                        println!("{}", "Verification success".green())
                    }
                }
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                }
            }
            println!();

            println!("{}", format!("Calldata (in bytes):").blue().bold());
            println!("{}", format!("{:?}", calldata).white().bold());
        }
        Some(Commands::VerifyProof {
            verification_key,
            proofs,
            public_signals,
            proof_file,
            params,
        }) => {
            println!(
                "{}",
                "Reading circom-plonk verification key, proofs, and public signals"
                    .white()
                    .bold()
            );
            let ((circom_vk, proofs), public_signals) = {
                match prepare_circom_vk(verification_key)
                    .and_then(|prev| {
                        let proofs = prepare_proofs(proofs)?;
                        Ok((prev, proofs))
                    })
                    .and_then(|prev| {
                        let ps = prepare_public_signals(public_signals)?;
                        Ok((prev, ps))
                    }) {
                    Ok(res) => res,
                    Err(e) => {
                        println!("{}", format!("{:#?}", e).red());
                        std::process::exit(1);
                    }
                }
            };
            assert!(proofs.len() == public_signals.len());

            let agg_proof = match std::fs::read_to_string(proof_file.clone())
                .with_context(|| format!("Failed to locate {}", proof_file.to_str().unwrap()))
                .and_then(|proof| {
                    let proof = serde_json::from_str::<Vec<u8>>(&proof)?;
                    Ok(proof)
                }) {
                Ok(proof) => proof,
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                    std::process::exit(1);
                }
            };

            println!("{}", "Reading parameters for the circuit".white().bold());
            let now = Instant::now();
            let params = match prepare_params(params) {
                Ok(params) => params,
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                    std::process::exit(1);
                }
            };
            report_elapsed(now);
            println!();

            println!(
                "{}",
                format!("Building aggregation circuit for {} proofs", proofs.len())
                    .white()
                    .bold()
            );
            let circuit = Accumulation::new(circom_vk.clone(), public_signals, proofs);
            println!();

            println!("{}", "Generating verification key".white().bold());
            let now = Instant::now();
            let vk = gen_vk(&params, &circuit);
            report_elapsed(now);
            println!();

            if check_proof::<_, EvmTranscript<G1Affine, _, _, _>, EvmTranscript<G1Affine, _, _, _>>(
                &params,
                &vk,
                circuit.instances(),
                agg_proof,
            ) {
                println!("{}", "Verification success".green())
            } else {
                println!("{}", "Verification failed".red())
            }
        }
        Some(Commands::CreateParams { k, output_dir }) => {
            println!(
                "{}",
                "Warning! Please don't use generated Params in production.".yellow()
            );
            let now = Instant::now();
            match create_and_save_srs(output_dir, k) {
                Ok(_) => {
                    report_elapsed(now);
                    println!("{}", "Success".green());
                }
                Err(e) => {
                    println!("{}", e.to_string().red());
                    std::process::exit(1);
                }
            }
        }
        Some(Commands::EvmVerifyProof {
            calldata,
            evmbytecode,
        }) => {
            let (calldata, bytecode) = match std::fs::read_to_string(calldata.clone())
                .with_context(|| format!("Failed to locate {}", calldata.to_str().unwrap()))
                .and_then(|calldata| {
                    let bytecode =
                        std::fs::read_to_string(evmbytecode.clone()).with_context(|| {
                            format!("Failed to locate {}", evmbytecode.to_str().unwrap())
                        })?;
                    Ok((calldata, bytecode))
                })
                .and_then(|(calldata, bytecode)| {
                    let calldata = serde_json::from_str::<Vec<u8>>(&calldata)
                        .with_context(|| "Failed to parse calldata")?;
                    let bytecode = serde_json::from_str::<Vec<u8>>(&bytecode)
                        .with_context(|| "Failed to parse evm bytecode")?;
                    Ok((calldata, bytecode))
                }) {
                Ok(res) => res,
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                    std::process::exit(1);
                }
            };

            match evm_verify(bytecode, calldata)
                .with_context(|| "Simulating evm verification failed")
            {
                Ok(result) => {
                    println!("{}", format!("Gas used: {}", result.gas_used).blue());
                    if result.reverted {
                        println!("{}", "Verification failed".red())
                    } else {
                        println!("{}", "Verification success".green())
                    }
                }
                Err(e) => {
                    println!("{}", format!("{:#?}", e).red());
                }
            }
        }
        None => {}
    };

    std::process::exit(0);
}

#[cfg(test)]
mod tests {
    // use super::*;

    // fn accumulation() {
    // let vk =
    // Accumulation::new(params, vk, public_signals, proofs)
    // }
}
