use std::env;
use std::path::PathBuf;
use std::process::Command;

use compiletest_rs as compiletest;

const BIN_NAME: &str = "mir_mapper_driver";

fn rustc_host() -> String {
    let output = Command::new("rustc").arg("-vV").output().expect("Failed to run rustc -vV");
    assert!(output.status.success());
    let stdout = String::from_utf8(output.stdout).expect("rustc -vV produced non-utf8 output");
    stdout
        .lines()
        .find_map(|line| line.strip_prefix("host: ").map(ToOwned::to_owned))
        .expect("Failed to parse rustc host triple")
}

fn configure_rustc_dylib_path() {
    let output = Command::new("rustc")
        .args(["--print", "sysroot"])
        .output()
        .expect("Failed to run rustc --print sysroot");
    assert!(output.status.success());
    let sysroot = String::from_utf8(output.stdout)
        .expect("rustc --print sysroot produced non-utf8 output")
        .trim()
        .to_owned();
    let host = rustc_host();
    let dylib_path = format!("{sysroot}/lib:{sysroot}/lib/rustlib/{host}/lib");

    // Safety: this test runner is single-threaded for this process.
    unsafe {
        env::set_var("DYLD_FALLBACK_LIBRARY_PATH", dylib_path);
    }
}

fn build_driver() {
    let manifest_path = "testbins/mir_mapper_driver/Cargo.toml";
    let mut cargo = Command::new("cargo");
    cargo.env("CARGO_INCREMENTAL", "0");
    cargo.args(["build", "-q", "--manifest-path", manifest_path, "--bin", BIN_NAME]);

    assert!(cargo.status().expect("Failed to build MIR mapper driver").success());
}

fn run_tests(path: &str) {
    compiletest::run_tests(&compiletest::Config {
        mode: "ui".parse().expect("Invalid mode"),
        src_base: PathBuf::from(path),
        target_rustcflags: Some("--edition 2024 --crate-type=lib".to_owned()),
        rustc_path: format!("testbins/{BIN_NAME}/target/debug/{BIN_NAME}").into(),
        ..Default::default()
    });
}

#[test]
fn mir_mapper() {
    configure_rustc_dylib_path();
    build_driver();
    run_tests("tests/test_cases/mir_mapper");
}
