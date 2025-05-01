use log::trace;
use rr_rustc_interface::hir::def_id::LocalDefId;
use rr_rustc_interface::{hir, middle};

use crate::environment::Environment;

pub struct CollectClosureDefsVisitor<'env, 'tcx: 'env> {
    env: &'env Environment<'tcx>,
    map: middle::hir::map::Map<'tcx>,
    result: Vec<LocalDefId>,
}

impl<'env, 'tcx> CollectClosureDefsVisitor<'env, 'tcx> {
    pub fn new(env: &'env Environment<'tcx>) -> Self {
        CollectClosureDefsVisitor {
            env,
            map: env.tcx().hir(),
            result: Vec::new(),
        }
    }

    pub fn get_closure_defs(self) -> Vec<LocalDefId> {
        self.result
    }
}

impl<'env, 'tcx> hir::intravisit::Visitor<'tcx> for CollectClosureDefsVisitor<'env, 'tcx> {
    type Map = middle::hir::map::Map<'tcx>;
    type NestedFilter = middle::hir::nested_filter::OnlyBodies;

    fn nested_visit_map(&mut self) -> Self::Map {
        self.map
    }

    fn visit_expr(&mut self, expr: &'tcx hir::Expr<'tcx>) {
        if let hir::ExprKind::Closure(hir::Closure {
            def_id: local_def_id,
            ..
        }) = expr.kind
        {
            let _tcx = self.env.tcx();
            let item_def_path = self.env.get_item_def_path(local_def_id.to_def_id());
            trace!("Add closure {} to result", item_def_path);
            self.result.push(*local_def_id);
        }

        hir::intravisit::walk_expr(self, expr);
    }
}
