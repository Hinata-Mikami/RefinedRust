#![feature(custom_test_frameworks)]
#![test_runner(test_runner)]

use std::path::PathBuf;
use std::{env, process};

use compiletest_rs as compiletest;

static BIN_NAME: &str = "analysis_driver";
static BIN_DIR: &str = "testbins";

fn build_analysis() {
    let path = format!("{BIN_DIR}/{BIN_NAME}/Cargo.toml");
    let mut cargo = process::Command::new("cargo");
    cargo.args(["build", "-q", "--manifest-path", &path, "--bin", BIN_NAME]);

    assert!(cargo.status().expect("Failed to build analysis binary").success());
}

fn run_tests(path: &str, arg: &str) {
    compiletest::run_tests(&compiletest::Config {
        mode: "ui".parse().expect("Invalid mode"),
        src_base: PathBuf::from(path),
        target_rustcflags: Some(["--edition 2024", arg].join(" ")),
        rustc_path: format!("{BIN_DIR}/{BIN_NAME}/target/debug/{BIN_NAME}").into(),
        ..Default::default()
    });
}

fn test_runner(_: &[&()]) {
    // Safety: Test is single-threaded
    unsafe {
        env::set_var("RUST_BACKTRACE", "1");
    }

    build_analysis();
    run_tests("tests/test_cases/definitely_initialized", "--analysis=DefinitelyInitializedAnalysis");
}
