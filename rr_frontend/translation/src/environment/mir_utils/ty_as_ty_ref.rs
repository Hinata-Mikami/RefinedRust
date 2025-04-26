// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rr_rustc_interface::middle::{mir, ty};

pub trait TyAsRef<'tcx> {
    fn as_ty_ref(&self) -> Option<(ty::Region<'tcx>, ty::Ty<'tcx>, mir::terminator::Mutability)>;
}

impl<'tcx> TyAsRef<'tcx> for ty::Ty<'tcx> {
    fn as_ty_ref(&self) -> Option<(ty::Region<'tcx>, ty::Ty<'tcx>, mir::terminator::Mutability)> {
        match self.kind() {
            ty::TyKind::Ref(region, ty, mutability) => Some((*region, *ty, *mutability)),
            _ => None,
        }
    }
}
