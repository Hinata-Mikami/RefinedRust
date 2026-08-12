#![feature(rustc_private)]

use std::{env, path, process};

const TARGET_DIR: &str = if cfg!(debug_assertions) { "debug" } else { "release" };

fn build_refinedrust() {
    let mut cargo = process::Command::new("cargo");
    cargo.arg("build");

    let status = cargo.status().expect("failed to build refinedrust project");
    assert!(status.success());
}

fn build_subproject(project_path: &str) {
    build_subproject_with_env(project_path, &[]);
}

fn build_subproject_with_env(project_path: &str, envs: &[(&str, &str)]) {
    let Ok(crate_dir) = env::var("CARGO_MANIFEST_DIR") else {
        panic!("CARGO_MANIFEST_DIR must be set to find the home of the crate");
    };

    let Some(workspace_dir) = path::Path::new(&crate_dir).parent() else {
        unreachable!("The crate `refinedrust_frontend` is inside a workspace");
    };

    let target_dir = workspace_dir.join("target").join(TARGET_DIR);
    let path = format!("{}:{}", target_dir.display(), env::var("PATH").unwrap_or_default());

    let mut cargo = process::Command::new("cargo");
    cargo.env("PATH", path);
    cargo.envs(envs.iter().copied());
    cargo.args(["-Z", "unstable-options"]).args(["-C", project_path]);
    cargo.arg("refinedrust");

    let status = cargo.status().expect(project_path);
    assert!(status.success());
}

#[cfg(test)]
#[expect(clippy::inline_modules)]
mod tests {
    use std::fs;

    use super::*;

    struct GeneratedOutput {
        path: Option<path::PathBuf>,
    }

    impl GeneratedOutput {
        fn new(path: path::PathBuf) -> Self {
            Self::remove_path(&path).expect("failed to remove stale generated test output");
            Self { path: Some(path) }
        }

        fn path(&self) -> &path::Path {
            self.path.as_deref().expect("generated test output already removed")
        }

        fn cleanup(mut self) {
            self.remove().expect("failed to remove generated test output");
        }

        fn remove(&mut self) -> std::io::Result<()> {
            let Some(path) = self.path.as_deref() else {
                return Ok(());
            };
            Self::remove_path(path)?;
            self.path = None;
            Ok(())
        }

        fn remove_path(path: &path::Path) -> std::io::Result<()> {
            match fs::remove_dir_all(path) {
                Ok(()) => Ok(()),
                Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
                Err(err) => Err(err),
            }
        }
    }

    impl Drop for GeneratedOutput {
        fn drop(&mut self) {
            drop(self.remove());
        }
    }

    #[test]
    fn run_deps_build() {
        build_refinedrust();
        build_subproject("./tests/deps_build/");
    }

    #[test]
    fn panic_abort_links_abort_config() {
        let project = path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/panic_abort");
        let output = GeneratedOutput::new(project.join("target/verify"));
        let config = project.join("RefinedRust.toml");

        build_refinedrust();
        build_subproject_with_env("./tests/panic_abort/", &[
            ("RUSTFLAGS", "-Cpanic=abort"),
            ("RR_CONFIG", config.to_str().expect("panic-abort config path is not UTF-8")),
        ]);

        let generated =
            fs::read_to_string(output.path().join("panic_abort/generated/generated_code_panic_abort.v"))
                .expect("missing generated panic-abort code");
        assert!(!generated.contains("panic_shim_loc"));
        assert!(generated.contains("StuckS"));

        let template =
            fs::read_to_string(output.path().join("panic_abort/generated/generated_template_checked_div.v"))
                .expect("missing generated panic-abort proof template");
        assert!(template.contains("radium_panic_strategy_of = PanicAbort →"));

        let template =
            fs::read_to_string(output.path().join("panic_abort/generated/generated_template_checked_rem.v"))
                .expect("missing generated conservative panic-abort proof template");
        assert!(!template.contains("radium_panic_strategy_of = PanicAbort →"));

        output.cleanup();

        let output = GeneratedOutput::new(project.join("target/verify"));
        let config = project.join("RefinedRustPermissive.toml");
        build_subproject_with_env("./tests/panic_abort/", &[
            ("RUSTFLAGS", "-Cpanic=abort"),
            ("RR_CONFIG", config.to_str().expect("permissive panic-abort config path is not UTF-8")),
        ]);

        let generated =
            fs::read_to_string(output.path().join("panic_abort/generated/generated_code_panic_abort.v"))
                .expect("missing permissive panic-abort code");
        assert!(generated.contains("CallS panic_shim_loc"));

        let template =
            fs::read_to_string(output.path().join("panic_abort/generated/generated_template_checked_rem.v"))
                .expect("missing permissive panic-abort proof template");
        assert!(template.contains("radium_panic_strategy_of = PanicAbort →"));

        output.cleanup();
    }
}
