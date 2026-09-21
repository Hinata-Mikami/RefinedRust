#![feature(rustc_private)]

use std::{env, io, path, process};

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

        fn remove(&mut self) -> io::Result<()> {
            let Some(path) = self.path.as_deref() else {
                return Ok(());
            };
            Self::remove_path(path)?;
            self.path = None;
            Ok(())
        }

        fn remove_path(path: &path::Path) -> io::Result<()> {
            match fs::remove_dir_all(path) {
                Ok(()) => Ok(()),
                Err(err) if err.kind() == io::ErrorKind::NotFound => Ok(()),
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

    #[test]
    fn concrete_projection_preserves_type_dependencies() {
        let project = path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/projection_deps");
        let output = GeneratedOutput::new(project.join("target/verify"));

        build_refinedrust();
        build_subproject("./tests/projection_deps/");

        let template =
            fs::read_to_string(output.path().join("projection_deps/generated/generated_template_call.v"))
                .expect("missing concrete-projection proof template");
        let specialized_call = template
            .lines()
            .find(|line| line.contains("consume_WrapperT_loc ◁"))
            .expect("missing specialized consume call");
        assert!(
            specialized_call.contains("(Wrapper_ty ((T_rt)) -[] -[T_ty])"),
            "normalized Wrapper<T> call did not retain its T dependency: {specialized_call}"
        );

        let symbolic_template = fs::read_to_string(
            output.path().join("projection_deps/generated/generated_template_call_symbolic.v"),
        )
        .expect("missing symbolic-projection proof template");
        assert!(symbolic_template.contains("Assoc_T_spec :"));
        assert!(symbolic_template.contains("( *[Assoc_T_Output_ty])"));
        assert!(symbolic_template.contains("syn_type_is_layoutable (Assoc_T_Output_st)"));

        let associated_bound_template = fs::read_to_string(
            output
                .path()
                .join("projection_deps/generated/generated_template_call_with_associated_bound.v"),
        )
        .expect("missing associated-bound proof template");
        assert!(associated_bound_template.contains("IntoSource_T_spec :"));
        assert!(associated_bound_template.contains("ItemSource_TasIntoSource_Source_spec :"));
        assert!(
            associated_bound_template
                .contains("ItemSource_spec (RRGS:=RRGS) (IntoSource_T_Source_rt) (IntoSource_T_Item_rt)")
        );

        let associated_bound_attrs_template = fs::read_to_string(
            output
                .path()
                .join("projection_deps/generated/generated_template_call_with_associated_bound_attrs.v"),
        )
        .expect("missing associated-bound attrs proof template");
        assert!(associated_bound_attrs_template.contains("IntoSource_T_spec_attrs :"));
        assert!(associated_bound_attrs_template.contains("ItemSource_TasIntoSource_Source_spec_attrs :"));
        let into_source_attrs = associated_bound_attrs_template
            .lines()
            .find(|line| line.contains("IntoSource_T_spec_attrs :"))
            .expect("missing IntoSource attrs parameter");
        assert!(
            into_source_attrs.contains(
                "IntoSource_spec_attrs (RRGS:=RRGS) (T_rt) (IntoSource_T_Item_rt) (IntoSource_T_Source_rt)"
            ),
            "IntoSource attrs record has unexpected parameters: {into_source_attrs}"
        );
        let consume_source_call = associated_bound_attrs_template
            .lines()
            .find(|line| line.contains("consume_source") && line.contains("spec"))
            .unwrap_or_else(|| panic!("missing consume_source call:\n{associated_bound_attrs_template}"));
        assert!(consume_source_call.contains("ItemSource_TasIntoSource_Source_spec_attrs"));
        assert!(consume_source_call.contains("IntoSource_T_spec_attrs"));

        let nested_bound_template = fs::read_to_string(
            output
                .path()
                .join("projection_deps/generated/generated_template_call_with_nested_associated_bound.v"),
        )
        .expect("missing nested associated-bound proof template");
        assert!(nested_bound_template.contains("NestedSource_T_spec :"));
        assert!(nested_bound_template.contains("IntoSource_TasNestedSource_Inner_spec :"));
        assert!(nested_bound_template.contains("ItemSource_TasNestedSource_InnerasIntoSource_Source_spec :"));
        assert!(nested_bound_template.contains("syn_type_is_layoutable (NestedSource_T_Inner_st)"));
        assert!(
            nested_bound_template
                .contains("syn_type_is_layoutable (IntoSource_TasNestedSource_Inner_Source_st)")
        );
        assert!(
            nested_bound_template
                .contains("syn_type_is_layoutable (IntoSource_TasNestedSource_Inner_Item_st)")
        );

        output.cleanup();
    }
}
