use log::trace;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::{hir, middle};

use crate::environment::Environment;

pub(crate) struct CollectClosureDefsVisitor<'env, 'tcx> {
    env: &'env Environment<'tcx>,
    result: Vec<LocalDefId>,
}

impl<'env, 'tcx> CollectClosureDefsVisitor<'env, 'tcx> {
    pub(crate) const fn new(env: &'env Environment<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            env,
            result: Vec::new(),
        }
    }

    pub(crate) fn get_closure_defs(self) -> Vec<LocalDefId> {
        self.result
    }
}

impl<'tcx> hir::intravisit::Visitor<'tcx> for CollectClosureDefsVisitor<'_, 'tcx> {
    type NestedFilter = middle::hir::nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.env.tcx()
    }

    fn visit_expr(&mut self, ex: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(hir::Closure {
            def_id: local_def_id,
            ..
        }) = ex.kind
        {
            let _tcx = self.env.tcx();
            let item_def_path = self.env.get_item_def_path(local_def_id.to_def_id());
            trace!("Add closure {} to result", item_def_path);
            self.result.push(*local_def_id);
        }

        hir::intravisit::walk_expr(self, ex);
    }
}
