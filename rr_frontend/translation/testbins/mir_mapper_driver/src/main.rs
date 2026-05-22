#![feature(rustc_private)]
#![feature(exitcode_exit_method)]
#![feature(default_field_values)]

use std::env;

use rr_rustc_interface::driver::*;
use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::interface::{Config, interface};
use rr_rustc_interface::middle::{ty, util};
use rr_rustc_interface::session::{self, EarlyDiagCtxt, Session};

struct OurCompilerCalls;

fn get_attributes(tcx: ty::TyCtxt<'_>, def_id: DefId) -> &[hir::Attribute] {
    #[expect(deprecated)]
    tcx.get_all_attrs(def_id)
}

fn get_attribute<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    def_id: DefId,
    segment1: &str,
    segment2: &str,
) -> Option<&'tcx hir::Attribute> {
    get_attributes(tcx, def_id).iter().find(|attr| match attr {
        hir::Attribute::Unparsed(normal_attr) => match normal_attr.as_ref() {
            hir::AttrItem {
                path: hir::AttrPath { segments, .. },
                args: hir::AttrArgs::Empty,
                ..
            } => segments.len() == 2 && segments[0].as_str() == segment1 && segments[1].as_str() == segment2,
            _ => false,
        },
        _ => false,
    })
}

fn override_queries(_session: &Session, local: &mut util::Providers) {
    local.queries.mir_borrowck = translation::mir_borrowck;
}

impl Callbacks for OurCompilerCalls {
    fn config(&mut self, config: &mut Config) {
        assert!(config.override_queries.is_none());
        config.override_queries = Some(override_queries);
    }

    fn after_analysis(&mut self, _compiler: &interface::Compiler, tcx: ty::TyCtxt<'_>) -> Compilation {
        let mut local_def_ids: Vec<_> = tcx
            .mir_keys(())
            .iter()
            .copied()
            .filter(|id| get_attribute(tcx, id.to_def_id(), "mapper", "run").is_some())
            .collect();

        local_def_ids
            .sort_unstable_by_key(|id| get_attribute(tcx, id.to_def_id(), "mapper", "run").unwrap().span());

        for (index, local_def_id) in local_def_ids.iter().copied().enumerate() {
            if index > 0 {
                println!();
            }

            println!("Mapping for function {}:", tcx.item_name(local_def_id.to_def_id()));

            let bc =
                translation::borrowck_mir_body(tcx, local_def_id).expect("MIR body should have been stored");
            let de = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
            let de = de.borrow();
            let mapping = translation::map_drop_elaborated_to_borrow_checked(tcx, bc, &de);
            println!("{}", translation::format_mapping(bc, &de, &mapping));
            if get_attribute(tcx, local_def_id.to_def_id(), "mapper", "points").is_some() {
                let points = translation::format_inserted_terminator_point_mappings(bc, &de, &mapping);
                if !points.is_empty() {
                    println!();
                    println!("Inserted terminator point mappings:");
                    println!("{points}");
                }
            }
            drop(de);
        }

        Compilation::Stop
    }
}

fn main() {
    env_logger::init();
    let error_handler = EarlyDiagCtxt::new(session::config::ErrorOutputType::HumanReadable { .. });
    init_rustc_env_logger(&error_handler);

    let mut compiler_args: Vec<_> = env::args().collect();
    compiler_args.push("-Zpolonius".to_owned());
    compiler_args.push("-Zalways-encode-mir".to_owned());
    compiler_args.push("-Zcrate-attr=feature(register_tool)".to_owned());
    compiler_args.push("-Zcrate-attr=register_tool(mapper)".to_owned());

    let mut callbacks = OurCompilerCalls;
    let exit_code = catch_with_exit_code(move || {
        run_compiler(&compiler_args, &mut callbacks);
    });
    exit_code.exit_process()
}
