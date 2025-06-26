#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::env;
use std::path::PathBuf;

/// Source: <https://github.com/rust-lang/miri/blob/master/tests/compiletest.rs>
use compiletest_rs as compiletest;
use test_binary::build_test_binary_once;

fn find_sysroot() -> String {
    // Taken from https://github.com/Manishearth/rust-clippy/pull/911.
    let home = option_env!("RUSTUP_HOME").or(option_env!("MULTIRUST_HOME"));
    let toolchain = option_env!("RUSTUP_TOOLCHAIN").or(option_env!("MULTIRUST_TOOLCHAIN"));

    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{}/toolchains/{}", home, toolchain),
        _ => option_env!("RUST_SYSROOT")
            .or_else(|| {
                option_env!("RUST_SRC_PATH")
                    .map(|s| s.strip_suffix("lib/rustlib/rustc-src/rust/compiler/rustc_driver/Cargo.toml"))
                    .flatten()
            })
            .expect(
                "Need to specify RUST_SYSROOT or RUST_SRC_PATH environment variables, or use rustup or multirust",
            )
            .to_owned(),
    }
}

fn run_tests(mode: &str, path: &str, custom_args: Vec<String>) {
    let mut config = compiletest::Config::default();

    build_test_binary_once!(analysis_driver, "testbins");

    let mut flags = Vec::new();
    flags.push("--edition 2024".to_owned());
    flags.push(format!("--sysroot {}", find_sysroot()));
    flags.extend(custom_args);
    config.target_rustcflags = Some(flags.join(" "));
    config.mode = mode.parse().expect("Invalid mode");
    config.rustc_path = path_to_analysis_driver().into();
    config.src_base = PathBuf::from(path);
    assert!(config.src_base.is_dir());

    // Filter the tests to run
    if let Some(filter) = env::args().nth(1) {
        config.filters.push(filter);
    }

    if let Some(lib_path) = option_env!("RUSTC_LIB_PATH") {
        config.run_lib_path = PathBuf::from(lib_path);
        config.compile_lib_path = PathBuf::from(lib_path);
    }

    compiletest::run_tests(&config);
}

fn test_runner(_tests: &[&()]) {
    // Safety: Test is single-threaded
    unsafe {
        env::set_var("RUST_BACKTRACE", "1");
    }

    run_tests("ui", "tests/test_cases/definitely_initialized", vec![
        "--analysis=DefinitelyInitializedAnalysis".into(),
    ]);
}
