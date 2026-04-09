pub mod consts;
#[cfg(test)]
mod tests;

use std::cmp::max;
use std::error::Error;
use std::fs::read_to_string;
use std::rc::Rc;
use std::sync::{Arc, Mutex};

use anyhow::Result;
use cairo_program_runner_lib::types::HashFunc;
use cairo_program_runner_lib::types::{PrivacySimpleBootloaderInput, SimpleBootloaderInput};
use cairo_program_runner_lib::{cairo_run_program, ProgramInput, Task, TaskSpec};
use cairo_vm::vm::runners::cairo_pie::CairoPie;
use circuit_air::verify::CircuitConfig;
use circuit_cairo_air::verify::build_cairo_verifier_circuit;
use circuit_cairo_air::verify::build_fixed_cairo_circuit_with_capacities;
use circuit_cairo_air::verify::prepare_cairo_proof_for_circuit_verifier;
use circuit_cairo_air::verify::CairoVerifierConfig;
use circuit_common::finalize::{add_zk_blinding, finalize_context};
use circuit_common::preprocessed::PreprocessedCircuit;
use circuit_prover::prover::{
    prepare_circuit_proof_for_circuit_verifier, prove_circuit_with_precompute,
};
use circuit_serialize::serialize::CircuitSerialize;
use circuits::context::ContextCapacities;
use circuits_stark_verifier::proof::ProofConfig;
use itertools::chain;
use privacy_circuit_verify::consts::{CAIRO_PCS_CONFIG, CIRCUIT_FRI_CONFIG, CIRCUIT_PCS_CONFIG};
use privacy_circuit_verify::{
    compute_privacy_bootloader_output, get_cairo_proof_config, get_cairo_verifier_config,
    get_privacy_bootloader_program, get_proof_config, get_recursive_circuit_config,
    PrivacyProofOutput,
};
use serde_json::from_str;
use starknet_types_core::felt::Felt;
use stwo::core::poly::circle::CanonicCoset;
use stwo::core::utils::MaybeOwned;
use stwo::core::vcs_lifted::blake2_merkle::Blake2sM31MerkleChannel;
use stwo::prover::backend::simd::SimdBackend;
use stwo::prover::mempool::BaseColumnPool;
use stwo::prover::poly::circle::PolyOps;
use stwo::prover::poly::twiddles::TwiddleTree;
use stwo::prover::{CommitmentTreeProver, ProverMemoryMode};
use stwo_cairo_adapter::adapter::adapt;
use stwo_cairo_adapter::ProverInput;
use stwo_cairo_common::preprocessed_columns::preprocessed_trace::PreProcessedTrace;
use stwo_cairo_prover::prover::{prove_cairo, prove_cairo_with_precompute};
use stwo_cairo_prover::witness::preprocessed_trace::gen_trace;
use tempfile::NamedTempFile;
use tracing::{info, span, Level};

use crate::consts::{
    CAIRO_PROVER_PARAMS, CAIRO_RUN_CONFIG, CIRCUIT_STORE_POLYNOMIALS_COEFFICIENTS,
};

pub struct RecursiveProverPrecomputes {
    pub base_column_pool: BaseColumnPool<SimdBackend>,
    pub twiddles: TwiddleTree<SimdBackend>,
    pub cairo_preprocessed_trace: Arc<PreProcessedTrace>,
    pub cairo_preprocessed_tree: Mutex<CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>>,
    pub cairo_verifier_config: CairoVerifierConfig,
    pub cairo_verifier_context_capacities: ContextCapacities,
    pub circuit_preprocessed_tree:
        Mutex<CommitmentTreeProver<SimdBackend, Blake2sM31MerkleChannel>>,
    pub preprocessed_circuit: PreprocessedCircuit,
    pub circuit_config: CircuitConfig,
    pub proof_config: ProofConfig,
    pub memory_mode: ProverMemoryMode,
}

fn compress_proof(proof_bytes: &[u8]) -> Result<Vec<u8>, Box<dyn Error>> {
    Ok(zstd::encode_all(proof_bytes, 3)?)
}

fn recursive_precompute_memory_mode() -> ProverMemoryMode {
    match std::env::var("STWO_PROVER_MEMORY_MODE") {
        Ok(value) => {
            if value.eq_ignore_ascii_case("low_memory")
                || value.eq_ignore_ascii_case("low-memory")
                || value.eq_ignore_ascii_case("lowmemory")
                || value.eq_ignore_ascii_case("checkpointed")
            {
                ProverMemoryMode::LowMemory
            } else {
                ProverMemoryMode::Fast
            }
        }
        Err(_) => ProverMemoryMode::Fast,
    }
}

/// Runs the program and generates a proof for it with params, bootloader and output format suitable
/// for the privacy circuit verifier.
pub fn privacy_prove(pie: CairoPie) -> Result<PrivacyProofOutput, Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_prove").entered();

    info!("Run privacy bootloader and get the prover input and output preimage");
    let (prover_input, output_preimage) = run_privacy_bootloader(pie)?;

    info!("Generate the cairo proof");
    let cairo_proof = prove_cairo::<Blake2sM31MerkleChannel>(prover_input, CAIRO_PROVER_PARAMS)?;

    info!("Prepare the proof for the circuit verifier");
    let proof_config = get_cairo_proof_config();
    let (proof, public_data) =
        prepare_cairo_proof_for_circuit_verifier(&cairo_proof, &proof_config);

    info!("Serialize and compress the proof and public data");
    let (public_claim, _outputs, _program) = public_data.pack_into_u32s();
    let mut proof_bytes: Vec<u8> = vec![];
    proof.serialize(&mut proof_bytes);
    let public_claim_bytes: Vec<u8> = public_claim.iter().flat_map(|x| x.to_le_bytes()).collect();
    let combined_bytes: Vec<u8> = chain!(public_claim_bytes, proof_bytes).collect();
    let compressed = compress_proof(&combined_bytes)?;

    Ok(PrivacyProofOutput {
        proof: compressed,
        output_preimage,
    })
}

pub fn prepare_recursive_prover_precomputes(
) -> Result<Arc<RecursiveProverPrecomputes>, Box<dyn Error>> {
    let _span = span!(Level::INFO, "prepare_privacy_recursiveprover_precomputes").entered();

    let cairo_verifier_config = get_cairo_verifier_config()?;
    let mut novalue_context = build_cairo_verifier_circuit(&cairo_verifier_config);
    add_zk_blinding(&mut novalue_context, [0; 32], CIRCUIT_FRI_CONFIG.n_queries);
    let preprocessed_circuit = PreprocessedCircuit::preprocess_circuit(&mut novalue_context);
    let cairo_verifier_context_capacities = novalue_context.capacities();
    let circuit_config = get_recursive_circuit_config();
    let proof_config = get_proof_config();

    info!("Prepare the twiddles");
    let base_column_pool = BaseColumnPool::<SimdBackend>::new();
    let cairo_lifting_log_size = CAIRO_PROVER_PARAMS
        .pcs_config
        .lifting_log_size
        .ok_or("Lifting log size is not set in Cairo's PcsConfig")?;
    let circuit_lifting_log_size = CIRCUIT_PCS_CONFIG
        .lifting_log_size
        .ok_or("Lifting log size is not set in Circuit's PcsConfig")?;

    // Precompute twiddles.
    let max_domain_size = max(cairo_lifting_log_size, circuit_lifting_log_size);
    let twiddles = SimdBackend::precompute_twiddles(
        CanonicCoset::new(max_domain_size)
            .circle_domain()
            .half_coset,
    );
    let memory_mode = recursive_precompute_memory_mode();

    info!(
        ?memory_mode,
        "Prepare the cairo prover preprocessed trace and tree"
    );
    let cairo_preprocessed_trace = Arc::new(
        CAIRO_PROVER_PARAMS
            .preprocessed_trace
            .to_preprocessed_trace(),
    );
    let cairo_preprocessed_trace_polys =
        SimdBackend::interpolate_columns(gen_trace(cairo_preprocessed_trace.clone()), &twiddles);
    let cairo_preprocessed_tree =
        CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new_with_memory_mode(
            cairo_preprocessed_trace_polys,
            CAIRO_PCS_CONFIG.fri_config.log_blowup_factor,
            &twiddles,
            CAIRO_PROVER_PARAMS.store_polynomials_coefficients,
            Some(cairo_lifting_log_size),
            &base_column_pool,
            memory_mode,
        );

    info!(
        ?memory_mode,
        "Prepare the circuit prover preprocessed trace and tree"
    );
    let circuit_preprocessed_trace = preprocessed_circuit
        .preprocessed_trace
        .get_trace::<SimdBackend>();
    let circuit_preprocessed_trace_polys =
        SimdBackend::interpolate_columns(circuit_preprocessed_trace, &twiddles);
    let circuit_preprocessed_tree =
        CommitmentTreeProver::<SimdBackend, Blake2sM31MerkleChannel>::new_with_memory_mode(
            circuit_preprocessed_trace_polys,
            CIRCUIT_FRI_CONFIG.log_blowup_factor,
            &twiddles,
            CIRCUIT_STORE_POLYNOMIALS_COEFFICIENTS,
            circuit_config.config.lifting_log_size,
            &base_column_pool,
            memory_mode,
        );

    Ok(Arc::new(RecursiveProverPrecomputes {
        base_column_pool,
        twiddles,
        cairo_preprocessed_trace,
        cairo_preprocessed_tree: Mutex::new(cairo_preprocessed_tree),
        cairo_verifier_config,
        cairo_verifier_context_capacities,
        circuit_preprocessed_tree: Mutex::new(circuit_preprocessed_tree),
        preprocessed_circuit,
        circuit_config,
        proof_config,
        memory_mode,
    }))
}

pub fn privacy_recursive_prove(
    pie: CairoPie,
    precomputes: Arc<RecursiveProverPrecomputes>,
) -> Result<PrivacyProofOutput, Box<dyn Error>> {
    let _span = span!(Level::INFO, "privacy_recursive_prove").entered();

    info!("Run privacy bootloader and get the prover input and output preimage");
    let (prover_input, output_preimage) = run_privacy_bootloader(pie)?;

    info!("Generate the cairo proof");
    let cairo_proof = {
        let mut cairo_preprocessed_tree = precomputes
            .cairo_preprocessed_tree
            .lock()
            .map_err(|_| std::io::Error::other("cairo preprocessed tree mutex poisoned"))?;
        cairo_preprocessed_tree.materialize_evaluations_for_reuse(
            &precomputes.twiddles,
            &precomputes.base_column_pool,
        );
        let cairo_proof = prove_cairo_with_precompute(
            &precomputes.base_column_pool,
            &precomputes.twiddles,
            precomputes.cairo_preprocessed_trace.clone(),
            MaybeOwned::Borrowed(&cairo_preprocessed_tree),
            prover_input,
            CAIRO_PROVER_PARAMS,
        )?;
        if precomputes.memory_mode == ProverMemoryMode::LowMemory {
            cairo_preprocessed_tree.release_recomputable_evaluations_low_memory();
        }
        cairo_proof
    };

    info!("Prepare the cairo proof for the cairo-circuit verifier");
    let (proof, public_data) = prepare_cairo_proof_for_circuit_verifier(
        &cairo_proof,
        &precomputes.cairo_verifier_config.proof_config,
    );

    info!("Build the cairo-circuit verifier context");
    let (public_claim, _outputs, _program) = public_data.pack_into_u32s();
    let outputs = compute_privacy_bootloader_output(&output_preimage);
    let mut context = build_fixed_cairo_circuit_with_capacities(
        &precomputes.cairo_verifier_config,
        proof,
        public_claim,
        vec![outputs],
        Some(&precomputes.cairo_verifier_context_capacities),
    );
    if !context.is_circuit_valid() {
        return Err("Circuit is not valid".into());
    };
    let zk_blinding_seed = cairo_proof.extended_stark_proof.proof.commitments.0[1].0;
    add_zk_blinding(
        &mut context,
        zk_blinding_seed,
        precomputes.circuit_config.config.fri_config.n_queries,
    );
    finalize_context(&mut context);
    let context_values = context.values();

    info!("Prove the cairo-circuit verifier");
    let circuit_proof = {
        let mut circuit_preprocessed_tree = precomputes
            .circuit_preprocessed_tree
            .lock()
            .map_err(|_| std::io::Error::other("circuit preprocessed tree mutex poisoned"))?;
        circuit_preprocessed_tree.materialize_evaluations_for_reuse(
            &precomputes.twiddles,
            &precomputes.base_column_pool,
        );
        let circuit_proof = prove_circuit_with_precompute(
            &precomputes.base_column_pool,
            &precomputes.twiddles,
            &precomputes.preprocessed_circuit,
            MaybeOwned::Borrowed(&circuit_preprocessed_tree),
            context_values,
            precomputes.circuit_config.config,
        );
        if precomputes.memory_mode == ProverMemoryMode::LowMemory {
            circuit_preprocessed_tree.release_recomputable_evaluations_low_memory();
        }
        circuit_proof
    };

    info!("Prepare the circuit proof for the circuit verifier");
    let (proof_qm31s, _public_data) =
        prepare_circuit_proof_for_circuit_verifier(circuit_proof, &precomputes.proof_config);

    info!("Serialize and compress the proof");
    let mut proof_bytes: Vec<u8> = vec![];
    proof_qm31s.serialize(&mut proof_bytes);
    let compressed = compress_proof(&proof_bytes)?;

    Ok(PrivacyProofOutput {
        proof: compressed,
        output_preimage,
    })
}

fn run_privacy_bootloader(pie: CairoPie) -> Result<(ProverInput, Vec<Felt>), Box<dyn Error>> {
    let _span = span!(Level::INFO, "get_prover_input").entered();

    let output_preimage_file = NamedTempFile::new()?;
    let output_preimage_path = output_preimage_file.path().to_path_buf();
    let pie_task_spec = TaskSpec {
        task: Rc::new(Task::Pie(pie)),
        program_hash_function: HashFunc::Blake,
    };
    let bootloader_input = PrivacySimpleBootloaderInput {
        simple_bootloader_input: SimpleBootloaderInput {
            fact_topologies_path: None,
            single_page: true,
            tasks: vec![pie_task_spec],
        },
        output_preimage_dump_path: output_preimage_path.clone(),
    };
    let bootloader_program = get_privacy_bootloader_program()?;

    info!("Running the program");
    let runner = cairo_run_program(
        &bootloader_program,
        Some(ProgramInput::Value(Box::new(bootloader_input))),
        CAIRO_RUN_CONFIG,
        None,
    )?;

    info!("Reading the bootloader output preimage");
    let output_preimage_content = read_to_string(&output_preimage_path)?;
    let output_preimage: Vec<Felt> = from_str(&output_preimage_content)?;

    info!("Adapting the runner output for the prover");
    let prover_input = adapt(&runner)?;

    Ok((prover_input, output_preimage))
}
