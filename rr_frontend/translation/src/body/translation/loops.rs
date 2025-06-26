// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;
use rr_rustc_interface::hir::def_id::DefId;
use rr_rustc_interface::middle::mir;

use super::TX;
use crate::attrs;
use crate::base::*;
use crate::environment::mir_analyses::initialization;
use crate::spec_parsers::loop_attr_parser::{LoopAttrParser as _, VerboseLoopAttrParser};

impl<'a, 'def: 'a, 'tcx: 'def> TX<'a, 'def, 'tcx> {
    /// Parse the attributes on spec closure `did` as loop annotations and add it as an invariant
    /// to the generated code.
    pub(crate) fn parse_attributes_on_loop_spec_closure(
        &self,
        loop_head: mir::BasicBlock,
        did: Option<DefId>,
    ) -> Result<radium::LoopSpec, TranslationError<'tcx>> {
        // determine invariant on initialization:
        // - we need this both for the refinement invariant (though this could be removed if we make uninit
        //   generic over the refinement)
        // - in order to establish the initialization invariant in each loop iteration, since we don't have
        //   proper subtyping for uninit => maybe we could fix this too by making uninit variant in the
        //   refinement type? then we could have proper subtyping lemmas.
        //  + to bring it to the right refinement type initially, maybe have some automation /
        //  annotation
        // TODO: consider changing it like that.
        //
        // Note that StorageDead will not help us for determining initialization/ making it invariant, since
        // it only applies to full stack slots, not individual paths. one thing that makes it more
        // complicated in the frontend: initialization may in practice also be path-dependent.
        //  - this does not cause issues with posing a too strong loop invariant,
        //  - but this poses an issue for annotations
        //

        let init_result = initialization::compute_definitely_initialized(
            self.proc.get_id(),
            self.proc.get_mir(),
            self.env.tcx(),
        );
        let init_places = init_result.get_before_block(loop_head);

        // get locals
        let mut locals_with_initialization: Vec<(String, radium::LocalKind, bool, radium::Type<'def>)> =
            Vec::new();

        for (local, kind, name, ty) in &self.fn_locals {
            let place = mir::Place::from(*local);
            let initialized = init_places.contains(place);

            locals_with_initialization.push((name.to_owned(), kind.to_owned(), initialized, ty.to_owned()));
        }

        let scope = self.ty_translator.scope.borrow();
        let mut parser = VerboseLoopAttrParser::new(locals_with_initialization, &*scope);

        if let Some(did) = did {
            let attrs = self.env.get_attributes(did);
            let attrs = attrs::filter_for_tool(attrs);
            info!("attrs for loop {:?}: {:?}", loop_head, attrs);
            parser.parse_loop_attrs(attrs.as_slice()).map_err(TranslationError::LoopSpec)
        } else {
            parser.parse_loop_attrs(&[]).map_err(TranslationError::LoopSpec)
        }
    }

    /// Find the optional `DefId` of the closure giving the invariant for the loop with head `head_bb`.
    pub(crate) fn find_loop_spec_closure(
        &self,
        head_bb: mir::BasicBlock,
    ) -> Result<Option<DefId>, TranslationError<'tcx>> {
        let bodies = self.proc.loop_info().get_loop_body(head_bb);
        let basic_blocks = &self.proc.get_mir().basic_blocks;

        // we go in order through the bodies in order to not stumble upon an annotation for a
        // nested loop!
        for body in bodies {
            // check that we did not go below a nested loop
            if self.proc.loop_info().get_loop_head(*body) == Some(head_bb) {
                // check the statements for an assignment
                let data = basic_blocks.get(*body).unwrap();
                for stmt in &data.statements {
                    if let mir::StatementKind::Assign(box (pl, _)) = stmt.kind
                        && let Some(did) = self.is_spec_closure_local(pl.local)?
                    {
                        return Ok(Some(did));
                    }
                }
            }
        }

        Ok(None)
    }
}
