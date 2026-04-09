#[cfg(feature = "slow-tests")]
pub mod slow_tests {
    use std::ffi::OsString;
    use std::path::PathBuf;

    use cairo_vm::vm::runners::cairo_pie::CairoPie;
    use privacy_circuit_verify::{verify_cairo, verify_recursive_circuit};
    use tracing_subscriber::fmt;

    use crate::{prepare_recursive_prover_precomputes, privacy_prove, privacy_recursive_prove};

    struct MemoryModeGuard {
        previous: Option<OsString>,
    }

    impl Drop for MemoryModeGuard {
        fn drop(&mut self) {
            if let Some(previous) = &self.previous {
                unsafe { std::env::set_var("STWO_PROVER_MEMORY_MODE", previous) };
            } else {
                unsafe { std::env::remove_var("STWO_PROVER_MEMORY_MODE") };
            }
        }
    }

    fn set_memory_mode(value: Option<&str>) -> MemoryModeGuard {
        let previous = std::env::var_os("STWO_PROVER_MEMORY_MODE");
        if let Some(value) = value {
            unsafe { std::env::set_var("STWO_PROVER_MEMORY_MODE", value) };
        } else {
            unsafe { std::env::remove_var("STWO_PROVER_MEMORY_MODE") };
        }
        MemoryModeGuard { previous }
    }

    fn load_privacy_tx_pie() -> CairoPie {
        let project_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let pie_path = project_dir.join("test_data/privacy_tx_cairo_pie.zip");
        CairoPie::read_zip_file(&pie_path).unwrap()
    }

    #[test]
    fn test_privacy_prove_and_verify() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let pie = load_privacy_tx_pie();

        // Prove and verify
        let proof_output = privacy_prove(pie).unwrap();
        verify_cairo(&proof_output).unwrap();
    }

    #[test]
    fn test_privacy_recursive_prove_and_verify() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let pie = load_privacy_tx_pie();

        let precomputes = prepare_recursive_prover_precomputes().unwrap();

        // Prove and verify
        let proof_output = privacy_recursive_prove(pie, precomputes).unwrap();
        verify_recursive_circuit(&proof_output).unwrap();
    }

    #[test]
    fn test_privacy_recursive_proof_matches_low_memory() {
        let _ = fmt().with_max_level(tracing::Level::INFO).try_init();

        let fast_output = {
            let _guard = set_memory_mode(Some("fast"));
            let precomputes = prepare_recursive_prover_precomputes().unwrap();
            privacy_recursive_prove(load_privacy_tx_pie(), precomputes).unwrap()
        };

        let low_memory_output = {
            let _guard = set_memory_mode(Some("low_memory"));
            let precomputes = prepare_recursive_prover_precomputes().unwrap();
            privacy_recursive_prove(load_privacy_tx_pie(), precomputes).unwrap()
        };

        assert_eq!(
            fast_output.proof, low_memory_output.proof,
            "recursive proof bytes differ between fast and low-memory modes"
        );
        assert_eq!(
            fast_output.output_preimage, low_memory_output.output_preimage,
            "recursive proof output preimage differs between fast and low-memory modes"
        );
    }
}
