use std::mem;

use rr_rustc_interface::middle::ty;

pub(crate) trait RegionBiFolder<'tcx> {
    fn tcx(&self) -> ty::TyCtxt<'tcx>;

    fn typing_env(&self) -> &ty::TypingEnv<'tcx>;

    fn map_regions(&mut self, r1: ty::Region<'tcx>, r2: ty::Region<'tcx>);

    fn map_tys(&mut self, ty1: ty::Ty<'tcx>, mut ty2: ty::Ty<'tcx>) {
        // normalize
        // Probably we should normalize the original thing before folding instead.
        // But problem: the normalization can also not deal with Polonius variables, which I will
        // encounter.
        //ty::Binder::rebind(
        //let ty1 = normalize_type(self.tcx(), self.param_env(), ty1).unwrap_or(ty1);
        //let ty2 = normalize_type(self.tcx(), self.param_env(), ty2).unwrap_or(ty2);

        // TODO: we need to handle the case that one of them is more normalized than the other.
        // Figure out how to handle that while not normalizing away the regions.
        // We could normalize erasing regions below, resolve, and then recursively restore the
        // regions?

        if mem::discriminant(ty1.kind()) != mem::discriminant(ty2.kind()) {
            // Hack right now. Figure out how to do this properly...
            ty2 = self.tcx().try_normalize_erasing_regions(*self.typing_env(), ty2).unwrap();
        }
        assert_eq!(mem::discriminant(ty1.kind()), mem::discriminant(ty2.kind()));

        match ty1.kind() {
            ty::TyKind::Ref(r1, ty1, _) => {
                let ty::TyKind::Ref(r2, ty2, _) = ty2.kind() else {
                    unreachable!();
                };

                self.map_regions(*r1, *r2);
                self.map_tys(*ty1, *ty2);
            },
            ty::TyKind::Adt(def1, args1) => {
                let ty::TyKind::Adt(def2, args2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(def1, def2);
                self.map_generic_args(args1, args2);
            },
            ty::TyKind::Param(p1) => {
                let ty::TyKind::Param(p2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(p1, p2);
            },
            ty::TyKind::Alias(k1, a1) => {
                let ty::TyKind::Alias(k2, a2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(k1, k2);
                assert_eq!(a1.def_id, a2.def_id);
                self.map_generic_args(a1.args, a2.args);
            },
            ty::TyKind::Int(it1) => {
                let ty::TyKind::Int(it2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(it1, it2);
            },
            ty::TyKind::Uint(it1) => {
                let ty::TyKind::Uint(it2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(it1, it2);
            },
            ty::TyKind::Tuple(t1) => {
                let ty::TyKind::Tuple(t2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(t1.len(), t2.len());
                for (ty1, ty2) in t1.iter().zip(t2.iter()) {
                    self.map_tys(ty1, ty2);
                }
            },
            ty::TyKind::Slice(ty1) => {
                let ty::TyKind::Slice(ty2) = ty2.kind() else {
                    unreachable!();
                };
                self.map_tys(*ty1, *ty2);
            },
            ty::TyKind::Closure(_, args1) => {
                let ty::TyKind::Closure(_, args2) = ty2.kind() else {
                    unreachable!();
                };
                let args1 = args1.as_closure();
                let args2 = args2.as_closure();
                let upvars1 = args1.upvar_tys();
                let upvars2 = args2.upvar_tys();
                assert_eq!(upvars1.len(), upvars2.len());
                for (ty1, ty2) in upvars1.iter().zip(upvars2.iter()) {
                    self.map_tys(ty1, ty2);
                }
            },

            ty::TyKind::RawPtr(ty1, mut1) => {
                let ty::TyKind::RawPtr(ty2, mut2) = ty2.kind() else {
                    unreachable!();
                };
                assert_eq!(mut1, mut2);

                self.map_tys(*ty1, *ty2);
            },

            ty::TyKind::Array(ty1, _len1) => {
                let ty::TyKind::Array(ty2, _len2) = ty2.kind() else {
                    unreachable!();
                };

                self.map_tys(*ty1, *ty2);
            },

            ty::TyKind::Never
            | ty::TyKind::Float(_)
            | ty::TyKind::Char
            | ty::TyKind::Bool
            | ty::TyKind::Str => {},

            _ => unimplemented!("implement RegionBiFolder::map_tys for {ty1:}"),
        }
    }

    fn map_generic_arg(&mut self, a1: ty::GenericArg<'tcx>, a2: ty::GenericArg<'tcx>) {
        match a1.kind() {
            ty::GenericArgKind::Lifetime(r1) => {
                let r2 = a2.expect_region();
                self.map_regions(r1, r2);
            },
            ty::GenericArgKind::Type(ty1) => {
                let ty2 = a2.expect_ty();
                self.map_tys(ty1, ty2);
            },
            _ => (),
        }
    }

    fn map_generic_args(&mut self, a1: ty::GenericArgsRef<'tcx>, a2: ty::GenericArgsRef<'tcx>) {
        for (a1, a2) in a1.iter().zip(a2.iter()) {
            self.map_generic_arg(a1, a2);
        }
    }
}
