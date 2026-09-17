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
    fn mutable_field_reborrow_uses_known_loan_support() {
        let project = path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/loan_supports");
        let output = GeneratedOutput::new(project.join("target/verify"));

        build_refinedrust();
        build_subproject("./tests/loan_supports/");

        let generated =
            fs::read_to_string(output.path().join("loan_supports/generated/generated_code_loan_supports.v"))
                .expect("missing generated loan-support code");
        let definition = |name: &str| {
            let marker = format!("Program Definition {name}_def");
            let start = generated.find(&marker).unwrap_or_else(|| panic!("missing {marker}"));
            let body = &generated[start..];
            let end = body[marker.len()..]
                .find("\nProgram Definition")
                .map_or(body.len(), |offset| marker.len() + offset);
            &body[..end]
        };
        let lifetime_initialized_from = |body: &str, source: &str| {
            let source = format!("\"{source}\"");
            body.lines()
                .find(|line| line.contains("CopyLftNameAnnot") && line.contains(&source))
                .and_then(|line| line.split('"').nth(1))
                .unwrap_or_else(|| panic!("missing lifetime initialized from {source} in:\n{body}"))
                .to_owned()
        };

        let loop_definition = definition("reborrow_in_loop");
        let starts: Vec<_> = loop_definition.lines().filter(|line| line.contains("StartLftAnnot")).collect();
        assert!(!starts.is_empty(), "missing loan initializations");
        assert!(
            starts.iter().all(|line| !line.contains("\"_flft\"")),
            "mutable reborrows fell back to the function lifetime: {starts:?}"
        );

        let shared_definition = definition("nested_shared_reborrow");
        let shared_inner = lifetime_initialized_from(shared_definition, "ulft_a");
        assert!(
            shared_definition
                .contains(&format!("CopyLftNameAnnot \"vlft4\" \"{shared_inner}\"; (* borrow *)")),
            "nested shared reborrow did not use the inner shared lifetime:\n{shared_definition}"
        );

        let mutable_definition = definition("nested_mut_reborrow");
        let mutable_outer = lifetime_initialized_from(mutable_definition, "ulft_b");
        let mutable_inner = lifetime_initialized_from(mutable_definition, "ulft_a");
        assert!(
            mutable_definition.contains(&format!(
                "AliasLftAnnot \"vlft4\" [\"{mutable_outer}\"; \"{mutable_inner}\"]; (* borrow *)"
            )),
            "nested mutable reborrow did not use the intersection of both lifetimes:\n{mutable_definition}"
        );

        let call_definition = definition("call_choose_mut_lifetime");
        let unconstrained_line = call_definition
            .lines()
            .find(|line| line.contains("UnconstrainedLftAnnot"))
            .unwrap_or_else(|| panic!("missing unconstrained call lifetime annotation:\n{call_definition}"));
        let unconstrained_lft =
            unconstrained_line.split('"').nth(1).expect("malformed unconstrained lifetime annotation");
        let annotation_position = call_definition
            .find(unconstrained_line)
            .expect("unconstrained lifetime annotation disappeared");
        let call_position = call_definition
            .find("CallS")
            .unwrap_or_else(|| panic!("missing generated call:\n{call_definition}"));
        assert!(annotation_position < call_position, "unconstrained lifetime was initialized after the call");
        let call_line = call_definition[call_position..].lines().next().expect("missing generated call line");
        assert!(
            call_line.contains(&format!("\"{unconstrained_lft}\"")),
            "unconstrained lifetime is absent from the call instantiation: {call_line}"
        );

        let call_template = fs::read_to_string(
            output
                .path()
                .join("loan_supports/generated/generated_template_call_choose_mut_lifetime.v"),
        )
        .expect("missing unconstrained-call proof template");
        assert!(
            call_template.contains(&format!("check_unconstrained_lft \"{unconstrained_lft}\";")),
            "proof prelude does not check the unconstrained call lifetime:\n{call_template}"
        );

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
