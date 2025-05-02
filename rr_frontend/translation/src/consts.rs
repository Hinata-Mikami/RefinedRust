// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashMap;

use rr_rustc_interface::hir::def_id::DefId;

use crate::base::*;

/// Scope of consts that are available
pub struct Scope<'def> {
    // statics are explicitly declared
    statics: HashMap<DefId, radium::StaticMeta<'def>>,
    // const places are constants that lie in a static memory segment because they are referred to
    // by-ref
    const_places: HashMap<DefId, radium::ConstPlaceMeta<'def>>,
}

impl<'def> Scope<'def> {
    /// Create a new const scope.
    pub fn empty() -> Self {
        Self {
            statics: HashMap::new(),
            const_places: HashMap::new(),
        }
    }

    /// Register a static
    pub fn register_static(&mut self, did: DefId, meta: radium::StaticMeta<'def>) {
        self.statics.insert(did, meta);
    }

    /// Register a const place
    pub fn register_const_place(&mut self, did: DefId, meta: radium::ConstPlaceMeta<'def>) {
        self.const_places.insert(did, meta);
    }

    pub fn get_static<'tcx>(&self, did: DefId) -> Result<&radium::StaticMeta<'def>, TranslationError<'tcx>> {
        self.statics.get(&did).ok_or_else(|| {
            TranslationError::UnknownError(format!(
                "Did not find a registered static for did {did:?}; registered: {:?}",
                self.statics
            ))
        })
    }
}
