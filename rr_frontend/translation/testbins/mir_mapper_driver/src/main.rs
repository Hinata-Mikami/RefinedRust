#![feature(rustc_private)]
#![feature(exitcode_exit_method)]
#![feature(default_field_values)]

use std::cell::RefCell;
use std::env;
use std::mem;

use rr_rustc_interface::borrowck;
use rr_rustc_interface::borrowck::consumers::{self, BodyWithBorrowckFacts};
use rr_rustc_interface::data_structures::fx::FxHashMap;
use rr_rustc_interface::driver::*;
use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::{DefId, LocalDefId};
use rr_rustc_interface::interface::{Config, interface};
use rr_rustc_interface::middle::query::Providers;
use rr_rustc_interface::middle::queries::mir_borrowck::ProvidedValue;
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

mod mir_storage {
    use super::*;

    thread_local! {
        static MIR_BODIES:
            RefCell<FxHashMap<LocalDefId, BodyWithBorrowckFacts<'static>>> =
            RefCell::new(FxHashMap::default());
    }

    pub(crate) unsafe fn store_mir_body<'tcx>(
        _tcx: ty::TyCtxt<'tcx>,
        def_id: LocalDefId,
        body_with_facts: BodyWithBorrowckFacts<'tcx>,
    ) {
        let body_with_facts: BodyWithBorrowckFacts<'static> = unsafe { mem::transmute(body_with_facts) };

        MIR_BODIES.with(|state| {
            let mut map = state.borrow_mut();
            assert!(map.insert(def_id, body_with_facts).is_none());
        });
    }

    pub(crate) unsafe fn retrieve_mir_body<'tcx>(
        _tcx: ty::TyCtxt<'tcx>,
        def_id: LocalDefId,
    ) -> BodyWithBorrowckFacts<'tcx> {
        let body_with_facts: BodyWithBorrowckFacts<'static> = MIR_BODIES.with(|state| {
            let mut map = state.borrow_mut();
            map.remove(&def_id).unwrap()
        });

        unsafe { mem::transmute(body_with_facts) }
    }
}

fn mir_borrowck<'tcx>(tcx: ty::TyCtxt<'tcx>, def_id: LocalDefId) -> ProvidedValue<'tcx> {
    let bodies_with_facts = consumers::get_bodies_with_borrowck_facts(tcx, def_id, consumers::ConsumerOptions::PoloniusInputFacts);

    #[expect(clippy::iter_over_hash_type)]
    for (did, body) in bodies_with_facts {
        unsafe {
            mir_storage::store_mir_body(tcx, did, body);
        }
    }

    let mut providers = Providers::default();
    borrowck::provide(&mut providers);
    let original_mir_borrowck = providers.mir_borrowck;
    original_mir_borrowck(tcx, def_id)
}

fn override_queries(_session: &Session, local: &mut util::Providers) {
    local.queries.mir_borrowck = mir_borrowck;
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

        local_def_ids.sort_unstable_by_key(|id| get_attribute(tcx, id.to_def_id(), "mapper", "run").unwrap().span());

        for (index, local_def_id) in local_def_ids.iter().copied().enumerate() {
            if index > 0 {
                println!();
            }

            println!("Mapping for function {}:", tcx.item_name(local_def_id.to_def_id()));

            let body_with_facts = unsafe { mir_storage::retrieve_mir_body(tcx, local_def_id) };
            let bc = &body_with_facts.body;
            let de = tcx.mir_drops_elaborated_and_const_checked(local_def_id);
            let de = de.borrow();
            let mapping = translation::map_drop_elaborated_to_borrow_checked(bc, &de);
            println!("{}", translation::format_mapping(bc, &de, &mapping));
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
