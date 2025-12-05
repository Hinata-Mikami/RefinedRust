// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::BTreeMap;

use radium::code;

use crate::base::*;

/// Scope of consts that are available
pub(crate) struct Scope<'def> {
    // statics are explicitly declared
    statics: BTreeMap<OrderedDefId, code::StaticMeta<'def>>,
}

impl<'def> Scope<'def> {
    /// Create a new const scope.
    pub(crate) const fn empty() -> Self {
        Self {
            statics: BTreeMap::new(),
        }
    }

    /// Register a static
    pub(crate) fn register_static(&mut self, did: OrderedDefId, meta: code::StaticMeta<'def>) {
        self.statics.insert(did, meta);
    }

    pub(crate) fn get_static<'tcx>(
        &self,
        did: OrderedDefId,
    ) -> Result<&code::StaticMeta<'def>, TranslationError<'tcx>> {
        self.statics.get(&did).ok_or_else(|| {
            TranslationError::UnknownError(format!(
                "Did not find a registered static for did {did:?}; registered: {:?}",
                self.statics
            ))
        })
    }
}
