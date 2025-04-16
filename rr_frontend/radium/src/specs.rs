// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Provides the Spec AST and utilities for interfacing with it.

use std::cell::RefCell;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::fmt;
use std::fmt::Write as fmtWrite;
use std::marker::PhantomData;
use std::ops::Add;

use derive_more::{Constructor, Display};
use indent_write::fmt::IndentWriter;
use itertools::Itertools;
use log::trace;

use crate::{coq, display_list, model, push_str_list, write_list, BASE_INDENT};

#[derive(Clone, Debug)]
/// Encodes a RR type with an accompanying refinement.
pub struct TypeWithRef<'def>(pub Type<'def>, pub String);

impl<'def> Display for TypeWithRef<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "{} :@: {}", self.1, self.0)
    }
}

impl<'def> TypeWithRef<'def> {
    #[must_use]
    pub const fn new(ty: Type<'def>, rfn: String) -> Self {
        TypeWithRef(ty, rfn)
    }

    #[must_use]
    fn make_unit() -> Self {
        TypeWithRef(Type::Unit, "()".to_owned())
    }
}

pub type Lft = String;

/// A universal lifetime that is not locally owned.
#[derive(Clone, Debug)]
pub enum UniversalLft {
    Function,
    Static,
    Local(Lft),
    External(Lft),
}

impl Display for UniversalLft {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::Function => write!(f, "ϝ"),
            Self::Static => write!(f, "static"),
            Self::Local(lft) | Self::External(lft) => write!(f, "{}", lft),
        }
    }
}

/// A lifetime constraint enforces a relation between two external lifetimes.
type ExtLftConstr = (UniversalLft, UniversalLft);

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub enum IntType {
    I8,
    I16,
    I32,
    I64,
    I128,
    U8,
    U16,
    U32,
    U64,
    U128,
    ISize,
    USize,
}

impl Display for IntType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::I8 => write!(f, "I8"),
            Self::I16 => write!(f, "I16"),
            Self::I32 => write!(f, "I32"),
            Self::I64 => write!(f, "I64"),
            Self::I128 => write!(f, "I128"),

            Self::U8 => write!(f, "U8"),
            Self::U16 => write!(f, "U16"),
            Self::U32 => write!(f, "U32"),
            Self::U64 => write!(f, "U64"),
            Self::U128 => write!(f, "U128"),

            Self::ISize => write!(f, "ISize"),
            Self::USize => write!(f, "USize"),
        }
    }
}

/// Representation of Caesium's optypes.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum OpType {
    Int(IntType),
    Bool,
    Char,
    Ptr,
    // a term for the struct_layout, and optypes for the individual fields
    Struct(coq::term::App<String, String>, Vec<OpType>),
    Untyped(Layout),
    Literal(coq::term::App<String, String>),
}

impl Display for OpType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "BoolOp"),
            Self::Char => write!(f, "CharOp"),
            Self::Int(it) => write!(f, "IntOp {}", it),
            Self::Ptr => write!(f, "PtrOp"),
            Self::Struct(sl, ops) => {
                write!(f, "StructOp {} [", sl)?;
                write_list!(f, ops, "; ")?;
                write!(f, "]")
            },
            Self::Untyped(ly) => write!(f, "UntypedOp ({})", ly),
            Self::Literal(ca) => write!(f, "{}", ca),
        }
    }
}

// NOTE: see ty::layout::layout_of_uncached for the rustc description of this.
pub(crate) static BOOL_REPR: IntType = IntType::U8;

/// A syntactic `RefinedRust` type.
/// Every semantic `RefinedRust` type has a corresponding syntactic type that determines its
/// representation in memory.
/// A syntactic type does not necessarily specify a concrete layout. A layout is only fixed once
/// a specific layout algorithm that resolves the non-deterministic choice of the compiler.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum SynType {
    Int(IntType),
    Bool,
    Char,
    Ptr,
    FnPtr,
    Untyped(Layout),
    Unit,
    Never,
    /// a Coq term, in case of generics. This Coq term is required to have type "syn_type".
    Literal(String),
    // no struct or enums - these are specified through literals.
}

impl Display for SynType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "BoolSynType"),
            Self::Char => write!(f, "CharSynType"),
            Self::Int(it) => write!(f, "(IntSynType {})", it),

            Self::Ptr => write!(f, "PtrSynType"),
            Self::FnPtr => write!(f, "FnPtrSynType"),

            Self::Untyped(ly) => write!(f, "(UntypedSynType {})", ly),
            Self::Unit | Self::Never => write!(f, "UnitSynType"),

            Self::Literal(ca) => write!(f, "{}", ca),
        }
    }
}

impl From<SynType> for Layout {
    fn from(x: SynType) -> Self {
        Self::from(&x)
    }
}

impl From<&SynType> for Layout {
    /// Get a Coq term for the layout of this syntactic type.
    /// This may call the Coq-level layout algorithm that we assume.
    fn from(x: &SynType) -> Self {
        match x {
            SynType::Bool => Self::Bool,
            SynType::Char => Self::Char,
            SynType::Int(it) => Self::Int(*it),

            SynType::Ptr | SynType::FnPtr => Self::Ptr,

            SynType::Untyped(ly) => ly.clone(),
            SynType::Unit | SynType::Never => Self::Unit,

            SynType::Literal(ca) => {
                let rhs = ca.to_owned();
                Self::Literal(coq::term::App::new("use_layout_alg'".to_owned(), vec![rhs]))
            },
        }
    }
}

impl From<SynType> for OpType {
    fn from(x: SynType) -> Self {
        Self::from(&x)
    }
}
impl From<&SynType> for OpType {
    /// Determine the optype used to access a value of this syntactic type.
    /// Note that we may also always use `UntypedOp`, but this here computes the more specific
    /// `op_type` that triggers more UB on invalid values.
    fn from(x: &SynType) -> Self {
        match x {
            SynType::Bool => Self::Bool,
            SynType::Char => Self::Char,
            SynType::Int(it) => Self::Int(*it),

            SynType::Ptr | SynType::FnPtr => Self::Ptr,

            SynType::Untyped(ly) => Self::Untyped(ly.clone()),
            SynType::Unit => Self::Struct(coq::term::App::new_lhs("unit_sl".to_owned()), Vec::new()),
            SynType::Never => Self::Untyped(Layout::Unit),

            SynType::Literal(ca) => {
                let rhs = ca.to_owned();
                Self::Literal(coq::term::App::new("use_op_alg'".to_owned(), vec![rhs]))
            },
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
pub enum TypeIsRaw {
    Yes,
    No,
}

/// Meta information from parsing type annotations
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TypeAnnotMeta {
    /// Used lifetime variables
    escaped_lfts: HashSet<Lft>,
    /// Used type variables
    escaped_tyvars: HashSet<LiteralTyParam>,
}

impl TypeAnnotMeta {
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.escaped_lfts.is_empty() && self.escaped_tyvars.is_empty()
    }

    #[must_use]
    pub fn empty() -> Self {
        Self {
            escaped_lfts: HashSet::new(),
            escaped_tyvars: HashSet::new(),
        }
    }

    pub fn join(&mut self, s: &Self) {
        let lfts: HashSet<_> = self.escaped_lfts.union(&s.escaped_lfts).cloned().collect();
        let tyvars: HashSet<_> = self.escaped_tyvars.union(&s.escaped_tyvars).cloned().collect();

        self.escaped_lfts = lfts;
        self.escaped_tyvars = tyvars;
    }

    pub fn add_lft(&mut self, lft: &Lft) {
        self.escaped_lfts.insert(lft.to_owned());
    }

    pub fn add_type(&mut self, ty: &Type<'_>) {
        if let Type::LiteralParam(lit) = ty {
            self.escaped_tyvars.insert(lit.to_owned());
        }
        // TODO: handle the case that it is unknown
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub struct LiteralType {
    /// Rust name
    pub rust_name: Option<String>,

    /// Rocq name of the type
    pub type_term: String,

    /// the refinement type
    pub refinement_type: coq::term::Type,

    /// the syntactic type
    pub syn_type: SynType,
}

pub type LiteralTypeRef<'def> = &'def LiteralType;

#[derive(Clone, Debug)]
pub struct LiteralTypeUse<'def> {
    /// definition
    pub(crate) def: LiteralTypeRef<'def>,

    /// parameters
    pub(crate) scope_inst: Option<GenericScopeInst<'def>>,
}

impl<'def> LiteralTypeUse<'def> {
    #[must_use]
    pub const fn new(s: LiteralTypeRef<'def>, scope_inst: GenericScopeInst<'def>) -> Self {
        LiteralTypeUse {
            def: s,
            scope_inst: Some(scope_inst),
        }
    }

    #[must_use]
    pub const fn new_with_annot(s: LiteralTypeRef<'def>) -> Self {
        LiteralTypeUse {
            def: s,
            scope_inst: None,
        }
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    fn get_rfn_type(&self) -> String {
        let ty_inst: Vec<_> = self
            .scope_inst
            .as_ref()
            .unwrap_or(&GenericScopeInst::empty())
            .get_direct_ty_params_with_assocs()
            .into_iter()
            .map(|ty| ty.get_rfn_type())
            .collect();

        let rfn_type = self.def.refinement_type.to_string();
        let applied = coq::term::App::new(rfn_type, ty_inst);
        applied.to_string()
    }

    /// Get the `syn_type` term for this struct use.
    #[must_use]
    pub fn generate_raw_syn_type_term(&self) -> SynType {
        let ty_inst: Vec<SynType> = self
            .scope_inst
            .as_ref()
            .unwrap_or(&GenericScopeInst::empty())
            .get_direct_ty_params_with_assocs()
            .into_iter()
            .map(Into::into)
            .collect();
        let specialized_spec = coq::term::App::new(self.def.syn_type.clone(), ty_inst);
        SynType::Literal(specialized_spec.to_string())
    }

    #[must_use]
    pub fn generate_syn_type_term(&self) -> SynType {
        let ty_inst: Vec<SynType> = self
            .scope_inst
            .as_ref()
            .unwrap_or(&GenericScopeInst::empty())
            .get_direct_ty_params_with_assocs()
            .into_iter()
            .map(Into::into)
            .collect();
        let specialized_spec = coq::term::App::new(self.def.syn_type.clone(), ty_inst);
        SynType::Literal(format!("({specialized_spec} : syn_type)"))
    }

    /// Generate a string representation of this struct use.
    #[must_use]
    fn generate_type_term(&self) -> String {
        if let Some(scope_inst) = self.scope_inst.as_ref() {
            let rt_inst = scope_inst
                .get_all_ty_params_with_assocs()
                .iter()
                .map(|ty| format!("({})", ty.get_rfn_type()))
                .join(" ");
            format!("({} {rt_inst} {})", self.def.type_term, scope_inst.instantiation())
        } else {
            self.def.type_term.clone()
        }
    }
}

/// The origin of a type parameter.
#[derive(Clone, Copy, Eq, PartialEq, Hash, Debug)]
pub enum TyParamOrigin {
    /// Declared in a surrounding trait declaration.
    SurroundingTrait,
    /// Declared in a surrounding trait impl
    SurroundingImpl,
    /// A direct parameter of a method or impl.
    Direct,
    AssocConstraint,
}

#[derive(Clone, Eq, PartialEq, Hash, Debug)]
#[allow(clippy::partial_pub_fields)]
pub struct LiteralTyParam {
    /// Rust name
    pub rust_name: String,

    /// Coq name of the type
    pub(crate) type_term: String,

    /// the refinement type
    refinement_type: String,

    /// the syntactic type
    pub syn_type: String,

    /// the declaration site of this type parameter
    origin: TyParamOrigin,
}

impl LiteralTyParam {
    #[must_use]
    pub fn new(rust_name: &str, base: &str) -> Self {
        Self {
            rust_name: rust_name.to_owned(),
            type_term: format!("{base}_ty"),
            refinement_type: format!("{base}_rt"),
            syn_type: format!("{base}_st"),
            origin: TyParamOrigin::Direct,
        }
    }

    pub fn set_origin(&mut self, origin: TyParamOrigin) {
        self.origin = origin;
    }

    #[must_use]
    pub fn new_with_origin(rust_name: &str, base: &str, origin: TyParamOrigin) -> Self {
        let mut x = Self::new(rust_name, base);
        x.origin = origin;
        x
    }

    #[must_use]
    fn make_refinement_param(&self) -> coq::binder::Binder {
        coq::binder::Binder::new(Some(self.refinement_type.clone()), coq::term::Type::Type)
    }

    #[must_use]
    fn make_syntype_param(&self) -> coq::binder::Binder {
        coq::binder::Binder::new(Some(self.syn_type.clone()), model::Type::SynType)
    }

    #[must_use]
    fn make_semantic_param(&self) -> coq::binder::Binder {
        coq::binder::Binder::new(
            Some(self.type_term.clone()),
            model::Type::Ttype(Box::new(coq::term::Type::Literal(self.refinement_type.clone()))),
        )
    }
}

/// Representation of (semantic) `RefinedRust` types.
/// 'def is the lifetime of the frontend for referencing struct definitions.
#[derive(Clone, Debug)]
pub enum Type<'def> {
    Int(IntType),
    Bool,
    Char,
    MutRef(Box<Type<'def>>, Lft),
    ShrRef(Box<Type<'def>>, Lft),
    BoxType(Box<Type<'def>>),
    /// a struct type, potentially instantiated with some type parameters
    /// the boolean indicates
    Struct(AbstractStructUse<'def>),
    /// an enum type, potentially instantiated with some type parameters
    Enum(AbstractEnumUse<'def>),
    /// literal types embedded as strings
    Literal(LiteralTypeUse<'def>),
    /// literal type parameters
    LiteralParam(LiteralTyParam),
    /// the uninit type given to uninitialized values
    Uninit(SynType),
    /// the unit type
    Unit,
    /// the Never type
    Never,
    /// dummy type that should be overridden by an annotation
    RawPtr,
}

impl<'def> Display for Type<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Bool => write!(f, "bool_t"),
            Self::Char => write!(f, "char_t"),
            Self::Int(it) => write!(f, "(int {})", it),

            Self::MutRef(ty, lft) => write!(f, "(mut_ref {} {})", lft, ty),
            Self::ShrRef(ty, lft) => write!(f, "(shr_ref {} {})", lft, ty),
            Self::BoxType(ty) => write!(f, "(box {})", ty),
            Self::RawPtr => write!(f, "alias_ptr_t"),

            Self::Struct(su) => write!(f, "{}", su.generate_type_term()),
            Self::Enum(su) => write!(f, "{}", su.generate_type_term()),

            Self::Literal(lit) => write!(f, "{}", lit.generate_type_term()),
            Self::LiteralParam(p) => write!(f, "{}", p.type_term),

            Self::Uninit(ly) => write!(f, "(uninit ({}))", ly),
            Self::Unit => write!(f, "unit_t"),
            Self::Never => write!(f, "never_t"),
        }
    }
}

impl<'def> From<Type<'def>> for SynType {
    fn from(x: Type<'def>) -> Self {
        Self::from(&x)
    }
}
impl<'def> From<&Type<'def>> for SynType {
    /// Get the layout of a type.
    fn from(x: &Type<'def>) -> Self {
        match x {
            Type::Bool => Self::Bool,
            Type::Char => Self::Char,
            Type::Int(it) => Self::Int(*it),

            Type::MutRef(..) | Type::ShrRef(..) | Type::BoxType(..) | Type::RawPtr => Self::Ptr,

            Type::Struct(s) => s.generate_syn_type_term(),
            Type::Enum(s) => s.generate_syn_type_term(),

            Type::Literal(lit) => lit.generate_syn_type_term(),
            Type::Uninit(st) => st.clone(),

            Type::Unit => Self::Unit,
            // NOTE: for now, just treat Never as a ZST
            Type::Never => Self::Never,

            Type::LiteralParam(lit) => Self::Literal(lit.syn_type.clone()),
        }
    }
}

impl<'def> Type<'def> {
    /// Make the first type in the type tree having an invariant not use the invariant.
    pub fn make_raw(&mut self) {
        match self {
            Self::Struct(su) => su.make_raw(),
            Self::MutRef(box ty, _) | Self::ShrRef(box ty, _) | Self::BoxType(box ty) => ty.make_raw(),
            _ => (),
        }
    }

    /// Determines the type this type is refined by.
    #[must_use]
    pub fn get_rfn_type(&self) -> coq::term::Type {
        match self {
            Self::Bool => coq::term::Type::Bool,
            Self::Char | Self::Int(_) => coq::term::Type::Z,

            Self::MutRef(box ty, _) => coq::term::Type::Prod(vec![
                model::Type::PlaceRfn(Box::new(ty.get_rfn_type())).into(),
                model::Type::Gname.into(),
            ]),

            Self::ShrRef(box ty, _) | Self::BoxType(box ty) => {
                model::Type::PlaceRfn(Box::new(ty.get_rfn_type())).into()
            },

            Self::RawPtr => model::Type::Loc.into(),

            Self::LiteralParam(lit) => coq::term::Type::Literal(lit.refinement_type.clone()),
            Self::Literal(lit) => coq::term::Type::Literal(lit.get_rfn_type()),

            Self::Struct(su) => {
                // NOTE: we don't need to subst, due to our invariant that the instantiations for
                // struct uses are already fully substituted
                coq::term::Type::Literal(su.get_rfn_type())
            },
            Self::Enum(su) => {
                // similar to structs, we don't need to subst
                coq::term::Type::Literal(su.get_rfn_type())
            },

            Self::Unit | Self::Never | Self::Uninit(_) => {
                // NOTE: could also choose to use an uninhabited type for Never
                coq::term::Type::Unit
            },
        }
    }
}

/// Specification for location ownership of a type.
#[derive(Clone, PartialEq, Eq, Debug)]
pub struct TyOwnSpec {
    loc: String,
    with_later: bool,
    rfn: String,
    /// type, with generics already fully substituted
    ty: String,
    /// literal lifetimes and types escaped in the annotation parser
    annot_meta: TypeAnnotMeta,
}

impl TyOwnSpec {
    #[must_use]
    pub const fn new(
        loc: String,
        rfn: String,
        ty: String,
        with_later: bool,
        annot_meta: TypeAnnotMeta,
    ) -> Self {
        Self {
            loc,
            with_later,
            rfn,
            ty,
            annot_meta,
        }
    }

    #[must_use]
    pub fn fmt_owned(&self, tid: &str) -> String {
        format!("{} ◁ₗ[{}, Owned {}] #({}) @ (◁ {})", self.loc, tid, self.with_later, self.rfn, self.ty)
    }

    #[must_use]
    fn fmt_shared(&self, tid: &str, lft: &str) -> String {
        if self.with_later {
            format!("guarded ({} ◁ₗ[{}, Shared {}] #({}) @ (◁ {}))", self.loc, tid, lft, self.rfn, self.ty)
        } else {
            format!("{} ◁ₗ[{}, Shared {}] #({}) @ (◁ {})", self.loc, tid, lft, self.rfn, self.ty)
        }
    }
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum InvariantSpecFlags {
    /// fully persistent and timeless invariant
    Persistent,
    /// invariant with own sharing predicate,
    Plain,
    NonAtomic,
    Atomic,
}

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum InvariantMode {
    All,
    OnlyShared,
    OnlyOwned,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct InvariantSpec {
    /// the name of the type definition
    type_name: String,
    flags: InvariantSpecFlags,

    /// name for the sharing lifetime that is used in the invariant specifications
    shr_lft_binder: String,

    /// the refinement type of this struct
    rfn_type: coq::term::Type,
    /// the xt type
    xt_type: coq::term::Type,
    /// the injection from xt to rfn
    xt_injection: String,
    /// the binding pattern for the refinement of this type
    rfn_pat: coq::binder::Pattern,

    /// existentials that are introduced in the invariant
    existentials: Vec<coq::binder::Binder>,

    /// an optional invariant as a separating conjunction,
    invariants: Vec<(IProp, InvariantMode)>,
    /// additional type ownership
    ty_own_invariants: Vec<TyOwnSpec>,

    /// the specification of the abstracted refinement under a context where rfn_pat is bound
    abstracted_refinement: Option<coq::binder::Pattern>,

    // TODO add stuff for non-atomic/atomic invariants
    /// name, type, implicit or not
    coq_params: Vec<coq::binder::Binder>,
}

impl InvariantSpec {
    #[must_use]
    pub fn new(
        type_name: String,
        flags: InvariantSpecFlags,
        shr_lft_binder: String,
        rfn_type: coq::term::Type,
        xt_type: coq::term::Type,
        xt_injection: String,
        rfn_pat: coq::binder::Pattern,
        existentials: Vec<coq::binder::Binder>,
        invariants: Vec<(IProp, InvariantMode)>,
        ty_own_invariants: Vec<TyOwnSpec>,
        abstracted_refinement: Option<coq::binder::Pattern>,
        coq_params: Vec<coq::binder::Binder>,
    ) -> Self {
        if flags == InvariantSpecFlags::Persistent {
            assert!(invariants.iter().all(|it| it.1 == InvariantMode::All) && ty_own_invariants.is_empty());
        }

        Self {
            type_name,
            flags,
            shr_lft_binder,
            rfn_type,
            xt_type,
            xt_injection,
            rfn_pat,
            existentials,
            invariants,
            ty_own_invariants,
            abstracted_refinement,
            coq_params,
        }
    }

    /// Add the abstracted refinement, if it was not already provided.
    pub fn provide_abstracted_refinement(&mut self, abstracted_refinement: coq::binder::Pattern) {
        if self.abstracted_refinement.is_some() {
            panic!("abstracted refinement for {} already provided", self.type_name);
        }
        self.abstracted_refinement = Some(abstracted_refinement);
    }

    fn make_existential_binders(&self) -> String {
        if self.existentials.is_empty() {
            return String::new();
        }

        format!("∃ {}, ", display_list!(&self.existentials, " "))
    }

    /// Assemble the owned invariant predicate for the plain mode.
    fn assemble_plain_owned_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π inner_rfn '{}, {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();

        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", IProp::Atom(own.fmt_owned("π"))).unwrap();
        }

        for (inv, mode) in &self.invariants {
            match mode {
                InvariantMode::All | InvariantMode::OnlyOwned => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the sharing invariant predicate for the plain mode.
    fn assemble_plain_shared_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        write!(
            out,
            "λ π {} inner_rfn '{}, {}⌜inner_rfn = {}⌝ ∗ ",
            &self.shr_lft_binder,
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for own in &self.ty_own_invariants {
            write!(out, "{} ∗ ", IProp::Atom(own.fmt_shared("π", &self.shr_lft_binder))).unwrap();
        }
        for (inv, mode) in &self.invariants {
            match mode {
                InvariantMode::All | InvariantMode::OnlyShared => {
                    write!(out, "{} ∗ ", inv).unwrap();
                },
                _ => (),
            }
        }
        write!(out, "True").unwrap();

        out
    }

    /// Assemble the list of lifetimes the invariant requires to be alive.
    fn assemble_ty_lfts(&self) -> String {
        let mut out = String::with_capacity(200);

        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_lfts ({}))", ty.type_term).unwrap();
            }
            for lft in &spec.annot_meta.escaped_lfts {
                write!(out, " ++ [{}]", lft).unwrap();
            }
        }

        out
    }

    /// Assemble the lifetime constraints that this type requires.
    fn assemble_ty_wf_elctx(&self) -> String {
        let mut out = String::with_capacity(200);
        write!(out, "[]").unwrap();

        // go over all the types and concat their lfts
        for spec in &self.ty_own_invariants {
            for ty in &spec.annot_meta.escaped_tyvars {
                write!(out, " ++ (ty_wf_E ({}))", ty.type_term).unwrap();
            }
        }

        out
    }

    /// Assemble the invariant for the persistent mode.
    fn assemble_pers_invariant(&self) -> String {
        let mut out = String::with_capacity(200);

        let ex = self.make_existential_binders();
        // TODO: maybe use some other formulation, the destructing let will make the
        // persistence/timeless inference go nuts.
        write!(
            out,
            "λ inner_rfn '{}, {}⌜inner_rfn = {}⌝ ∗ ",
            self.rfn_pat,
            ex,
            self.abstracted_refinement.as_ref().unwrap()
        )
        .unwrap();
        for (inv, _) in &self.invariants {
            write!(out, "{} ∗ ", inv).unwrap();
        }
        write!(out, "True").unwrap();

        out
    }

    #[must_use]
    fn spec_name(&self) -> String {
        format!("{}_inv_spec", self.type_name)
    }

    fn generate_coq_invariant_def(&self, scope: &GenericScope<'_>, base_rfn_type: &str) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate the spec definition
        let spec_name = self.spec_name();

        match self.flags {
            InvariantSpecFlags::NonAtomic => {
                #[allow(deprecated)]
                write!(
                    out,
                    "{indent}Program Definition {} : {} (na_ex_inv_def ({}) ({})) := ",
                    spec_name,
                    scope.get_all_type_term(),
                    base_rfn_type,
                    self.rfn_type,
                )
                .unwrap();
            },
            _ => {
                #[allow(deprecated)]
                write!(
                    out,
                    "{indent}Program Definition {} : {} (ex_inv_def ({}) ({})) := ",
                    spec_name,
                    scope.get_all_type_term(),
                    base_rfn_type,
                    self.rfn_type,
                )
                .unwrap();
            },
        }

        match self.flags {
            InvariantSpecFlags::Persistent => {
                let inv = self.assemble_pers_invariant();
                write!(
                    out,
                    "{scope} mk_pers_ex_inv_def\n\
                       {indent}{indent}({})%type\n\
                       {indent}{indent}({})\n\
                       {indent}{indent}({inv})%I _ _\n\
                       {indent}.\n",
                    self.xt_type, self.xt_injection,
                )
                .unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_timeless. Qed.\n").unwrap();
            },
            InvariantSpecFlags::Plain => {
                let own_inv = self.assemble_plain_owned_invariant();
                let shr_inv = self.assemble_plain_shared_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                write!(
                    out,
                    "{scope} mk_ex_inv_def\n\
                    {indent}{indent}({})%type\n\
                    {indent}{indent}({})\n\
                    {indent}{indent}({own_inv})%I\n\
                    {indent}{indent}({shr_inv})%I\n\
                    {indent}{indent}({lft_outlives})\n\
                    {indent}{indent}({lft_wf_elctx})\n\
                    {indent}{indent}_ _ _\n\
                    {indent}.\n",
                    self.xt_type, self.xt_injection
                )
                .unwrap();
                write!(out, "{indent}Next Obligation. ex_t_solve_persistent. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_plain_t_solve_shr_mono. Qed.\n").unwrap();
                write!(out, "{indent}Next Obligation. ex_plain_t_solve_shr. Qed.\n").unwrap();
            },
            InvariantSpecFlags::NonAtomic => {
                let own_inv = self.assemble_plain_owned_invariant();
                let lft_outlives = self.assemble_ty_lfts();
                let lft_wf_elctx = self.assemble_ty_wf_elctx();

                write!(
                    out,
                    "{scope} na_mk_ex_inv_def\n\
                    {indent}{indent}({})%type\n\
                    {indent}{indent}({})\n\
                    {indent}{indent}({own_inv})%I\n\
                    {indent}{indent}({lft_outlives})\n\
                    {indent}{indent}({lft_wf_elctx})\n\
                    {indent}.\n",
                    self.xt_type, self.xt_injection
                )
                .unwrap();
            },
            _ => {
                panic!("unimplemented invariant spec flag: {:?}", self.flags);
            },
        }
        write!(out, "\n").unwrap();

        out
    }

    /// Generate the Coq definition of the type, without the surrounding context assumptions.
    fn generate_coq_type_def_core(
        &self,
        base_type: &str,
        base_rfn_type: &str,
        generics_rts: &coq::term::TermList,
        scope: &GenericScope<'_>,
        context_names: &[String],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // generate the spec definition
        let spec_name = self.spec_name();

        write!(out, "{}", self.generate_coq_invariant_def(scope, base_rfn_type)).unwrap();

        // generate the definition itself.
        if InvariantSpecFlags::NonAtomic == self.flags {
            #[allow(deprecated)]
            write!(
                out,
                "{indent}Definition {} : {} (type ({})) :=\n\
                {indent}{indent}{scope} na_ex_plain_t _ _ ({spec_name} {}) {}.\n",
                self.type_name,
                scope.get_all_type_term(),
                self.rfn_type,
                scope.identity_instantiation(),
                base_type
            )
            .unwrap();
        } else {
            #[allow(deprecated)]
            write!(
                out,
                "{indent}Definition {} : {} (type ({})) :=\n\
                {indent}{indent}{scope} ex_plain_t _ _ ({spec_name} {}) {}.\n",
                self.type_name,
                scope.get_all_type_term(),
                self.rfn_type,
                scope.identity_instantiation(),
                base_type
            )
            .unwrap();
        }
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.type_name).unwrap();
        write!(out, "{indent}Definition {}_rt : Type.\n", self.type_name).unwrap();
        write!(
            out,
            "{indent}Proof using {generics_rts} {}. let __a := normalized_rt_of_spec_ty {} in exact __a. Defined.\n",
            context_names.join(" "),
            self.type_name
        )
        .unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}_rt.\n", self.type_name).unwrap();

        out
    }

    /// Generate the definition of the Coq type, including introduction of type parameters to the
    /// context.
    fn generate_coq_type_def(
        &self,
        base_type_name: &str,
        base_rfn_type: &str,
        scope: &GenericScope<'_>,
    ) -> String {
        let mut out = String::with_capacity(200);

        assert!(self.abstracted_refinement.is_some());

        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.type_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        let all_ty_params = scope.get_all_ty_params_with_assocs();

        // add type parameters
        if !all_ty_params.params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in &all_ty_params.params {
                write!(out, " ({} : Type)", names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }

        let (context_names, dep_sigma) = format_extra_context_items(&self.coq_params, &mut out).unwrap();

        // get the applied base_rfn_type
        let rt_instantiations = all_ty_params.get_coq_ty_rt_params().make_using_terms();
        let applied_base_rt = coq::term::App::new(base_rfn_type, rt_instantiations.0.clone());

        // get the applied base type
        let applied_base_type = coq::term::App::new(base_type_name, rt_instantiations.0.clone());
        let applied_base_type = format!("({applied_base_type} {})", scope.identity_instantiation());

        write!(
            out,
            "{}",
            self.generate_coq_type_def_core(
                &applied_base_type,
                applied_base_rt.to_string().as_str(),
                &rt_instantiations,
                scope,
                &context_names
            )
        )
        .unwrap();

        // finish
        write!(out, "End {}.\n", self.type_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.rt_def_name()).unwrap();
        if !context_names.is_empty() {
            let dep_sigma_str = if dep_sigma { "{_} " } else { "" };

            write!(
                out,
                "Global Arguments {} {}{} {{{}}}.\n",
                self.rt_def_name(),
                dep_sigma_str,
                "_ ".repeat(all_ty_params.params.len()),
                "_ ".repeat(context_names.len())
            )
            .unwrap();
        }

        out
    }

    #[must_use]
    fn rt_def_name(&self) -> String {
        format!("{}_rt", self.type_name)
    }
}

/// Representation options for structs.
#[derive(Copy, Clone, Eq, PartialEq, Debug)]
/// Struct representation options supported by Radium
pub enum StructRepr {
    ReprRust,
    ReprC,
    ReprTransparent,
}

impl Display for StructRepr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReprRust => write!(f, "StructReprRust"),
            Self::ReprC => write!(f, "StructReprC"),
            Self::ReprTransparent => write!(f, "StructReprTransparent"),
        }
    }
}

#[derive(Copy, Clone, Eq, PartialEq, Debug)]
/// Enum representation options supported by Radium
pub enum EnumRepr {
    ReprRust,
    ReprC,
    ReprTransparent,
}

impl Display for EnumRepr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReprRust => write!(f, "EnumReprRust"),
            Self::ReprC => write!(f, "EnumReprC"),
            Self::ReprTransparent => write!(f, "EnumReprTransparent"),
        }
    }
}

/// Description of a variant of a struct or enum.
#[derive(Clone, Debug)]
pub struct AbstractVariant<'def> {
    /// the fields, closed under a surrounding scope
    fields: Vec<(String, Type<'def>)>,
    /// the struct representation mode
    repr: StructRepr,
    /// the struct's name
    name: String,
    /// the Coq def name for the struct's plain tydef alias (without the optional invariant wrapper)
    plain_ty_name: String,
    /// the Coq def name for the struct's layout spec definition (of type struct_layout_spec)
    sls_def_name: String,
    st_def_name: String,
    /// the Coq def name for the struct's refinement type
    /// (used for using occurrences, but not for the definition itself)
    plain_rt_def_name: String,
}

impl<'def> AbstractVariant<'def> {
    /// Get the name of this variant
    #[must_use]
    fn name(&self) -> &str {
        &self.name
    }

    fn rfn_type(&self) -> coq::term::Type {
        model::Type::PList(
            "place_rfn".to_owned(),
            self.fields.iter().map(|(_, t)| t.get_rfn_type()).collect(),
        )
        .into()
    }

    /// The core of generating the sls definition, without the section + context intro.
    #[must_use]
    fn generate_coq_sls_def_core(&self, typarams: &coq::binder::BinderList) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        // intro to main def
        write!(out, "{indent}Definition {} {typarams} : struct_layout_spec :=\n", self.sls_def_name,)
            .unwrap();
        // for recursive uses
        write!(out, "{indent}{indent}let {} {typarams} := UnitSynType in\n", self.st_def_name,).unwrap();
        write!(out, "{indent}{indent}mk_sls \"{}\" [", self.name).unwrap();

        push_str_list!(out, &self.fields, ";", |(name, ty)| {
            let synty: SynType = ty.into();

            format!("\n{indent}{indent}(\"{name}\", {synty})")
        });

        write!(out, "] {}.\n", self.repr).unwrap();

        // also generate a definition for the syntype
        write!(
            out,
            "{indent}Definition {} {typarams} : syn_type := {} {}.\n",
            self.st_def_name,
            self.sls_def_name.clone(),
            typarams.make_using_terms(),
        )
        .unwrap();

        out
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    fn generate_coq_sls_def(&self, scope: &GenericScope<'def>) -> String {
        let mut out = String::with_capacity(200);

        let indent = "  ";
        write!(out, "Section {}.\n", self.sls_def_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add syntype parameters
        let typarams = scope.get_all_ty_params_with_assocs().get_coq_ty_st_params();
        out.push('\n');

        write!(out, "{}", self.generate_coq_sls_def_core(&typarams)).unwrap();

        // finish
        write!(out, "End {}.\n", self.sls_def_name).unwrap();
        out
    }

    #[must_use]
    #[deprecated(note = "Use `get_coq_type_term` instead")]
    fn generate_coq_type_term(&self, sls_app: Vec<String>) -> String {
        let mut out = String::with_capacity(200);

        out.push_str(&format!("struct_t {} +[", coq::term::App::new(&self.sls_def_name, sls_app)));
        push_str_list!(out, &self.fields, ";", |(_, ty)| ty.to_string());
        out.push(']');

        out
    }

    #[must_use]
    fn get_coq_type_term(&self, sls_app: Vec<coq::term::Term>) -> coq::term::Type {
        let sls = coq::term::App::new(coq::term::Term::Literal(self.sls_def_name.clone()), sls_app);

        let tys = self.fields.iter().map(|(_, ty)| coq::term::Type::Literal(ty.to_string())).collect();

        model::Type::StructT(Box::new(sls).into(), tys).into()
    }

    #[must_use]
    fn generate_coq_type_def_core(
        &self,
        ty_params: &GenericScope<'def>,
        context_names: &[String],
    ) -> coq::Document {
        let mut document = coq::Document::default();

        let all_ty_params = ty_params.get_all_ty_params_with_assocs();

        // Generate terms to apply the sls app to
        let sls_app: Vec<_> = all_ty_params
            .params
            .iter()
            .map(|names| {
                coq::term::Term::RecordProj(
                    Box::new(coq::term::Term::Literal(names.type_term.clone())),
                    "ty_syn_type".to_owned(),
                )
            })
            .collect();

        // Intro to main def
        document.push(coq::command::Definition {
            name: self.plain_ty_name.clone(),
            params: coq::binder::BinderList::empty(),
            ty: Some(
                ty_params
                    .get_spec_all_type_term(Box::new(model::Type::Ttype(Box::new(self.rfn_type()))).into()),
            ),
            body: coq::command::DefinitionBody::Proof(coq::proof::Proof::new_using(
                context_names.join("{}"),
                coq::proof::Terminator::Defined,
                |proof| {
                    proof.push(coq::ltac::LTac::Exact(coq::term::Term::App(Box::new(coq::term::App::new(
                        // TODO: `ty_params` must create a specific Coq object.
                        coq::term::Term::Literal(ty_params.to_string()),
                        vec![coq::term::Term::Literal(self.get_coq_type_term(sls_app).to_string())],
                    )))));
                },
            )),
        });

        // Generate the refinement type definition
        let rt_params = all_ty_params.get_coq_ty_rt_params();
        let using = format!("{} {}", rt_params.make_using_terms(), context_names.join(" "));

        document.push(coq::command::Definition {
            name: self.plain_rt_def_name.clone(),
            params: coq::binder::BinderList::empty(),
            ty: Some(coq::term::Type::Type),
            body: coq::command::DefinitionBody::Proof(coq::proof::Proof::new_using(
                using,
                coq::proof::Terminator::Defined,
                |proof| {
                    proof.push(coq::ltac::LetIn::new(
                        "__a",
                        coq::term::App::new(
                            coq::term::Term::Literal("normalized_rt_of_spec_ty".to_owned()),
                            vec![coq::term::Term::Literal(self.plain_ty_name.clone())],
                        ),
                        coq::ltac::LTac::Exact(coq::term::Term::Literal("__a".to_owned())),
                    ));
                },
            )),
        });

        // Make it Typeclasses Transparent
        let typeclasses_ty = coq::command::Command::TypeclassesTransparent(self.plain_ty_name.clone());
        let typeclasses_rt = coq::command::Command::TypeclassesTransparent(self.plain_rt_def_name.clone());

        document.push(coq::command::CommandAttrs::new(typeclasses_ty).attributes("global"));
        document.push(coq::command::CommandAttrs::new(typeclasses_rt).attributes("global"));

        document
    }

    /// Generate a Coq definition for the struct type alias.
    /// TODO: maybe we should also generate a separate alias def for the refinement type to make
    /// things more readable?
    #[must_use]
    fn generate_coq_type_def(
        &self,
        scope: &GenericScope<'def>,
        extra_context: &[coq::binder::Binder],
    ) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        let all_ty_params = scope.get_all_ty_params_with_assocs();

        // add type parameters, and build a list of terms to apply the sls def to
        if !all_ty_params.params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in &all_ty_params.params {
                write!(out, " ({} : Type)", names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }
        out.push('\n');

        // write coq parameters
        let (context_names, dep_sigma) = format_extra_context_items(extra_context, &mut out).unwrap();

        write!(out, "{}", self.generate_coq_type_def_core(scope, &context_names)).unwrap();

        write!(out, "End {}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_rt_def_name).unwrap();
        if !context_names.is_empty() {
            let dep_sigma_str = if dep_sigma { "{_} " } else { "" };

            write!(
                out,
                "Global Arguments {} {}{} {{{}}}.\n",
                self.plain_rt_def_name,
                dep_sigma_str,
                "_ ".repeat(all_ty_params.params.len()),
                "_ ".repeat(extra_context.len())
            )
            .unwrap();
        }
        out
    }
}

fn format_extra_context_items<F>(
    items: &[coq::binder::Binder],
    f: &mut F,
) -> Result<(Vec<String>, bool), fmt::Error>
where
    F: fmt::Write,
{
    let mut context_names = Vec::new();
    let mut counter = 0;

    let mut depends_on_sigma = false;

    // write coq parameters
    if !items.is_empty() {
        write!(f, "{} (* Additional parameters *)\n", BASE_INDENT)?;
        write!(f, "{}Context ", BASE_INDENT)?;

        for it in items {
            let name = format!("_CTX{}", counter);
            counter += 1;

            write!(f, "{}", it.clone().set_name(name.clone()))?;
            context_names.push(name);
            depends_on_sigma = depends_on_sigma || it.is_dependent_on_sigma();
        }
        write!(f, ".\n")?;
    }
    write!(f, "\n")?;

    Ok((context_names, depends_on_sigma))
}

/// Description of a struct type.
// TODO: mechanisms for resolving mutually recursive types.
#[derive(Clone)]
pub struct AbstractStruct<'def> {
    /// an optional invariant/ existential abstraction for this struct
    invariant: Option<InvariantSpec>,

    /// the actual definition of the variant
    variant_def: AbstractVariant<'def>,

    /// scope this is generic over
    scope: GenericScope<'def>,

    /// true iff this is recursive
    is_recursive: bool,
}

impl<'def> fmt::Debug for AbstractStruct<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        write!(f, "AbstractStruct<name={}>", self.variant_def.name)
    }
}

pub type AbstractStructRef<'def> = &'def RefCell<Option<AbstractStruct<'def>>>;

impl<'def> AbstractStruct<'def> {
    #[must_use]
    pub const fn new(variant_def: AbstractVariant<'def>, scope: GenericScope<'def>) -> Self {
        AbstractStruct {
            invariant: None,
            variant_def,
            scope,
            is_recursive: false,
        }
    }

    /// Register that this type is recursive.
    pub fn set_is_recursive(&mut self) {
        self.is_recursive = true;
    }

    /// Check if an invariant has been declared on this type.
    #[must_use]
    pub const fn has_invariant(&self) -> bool {
        self.invariant.is_some()
    }

    /// Get the name of this struct
    #[must_use]
    fn name(&self) -> &str {
        self.variant_def.name()
    }

    #[must_use]
    fn sls_def_name(&self) -> &str {
        &self.variant_def.sls_def_name
    }

    #[must_use]
    fn st_def_name(&self) -> &str {
        &self.variant_def.st_def_name
    }

    #[must_use]
    pub(crate) fn plain_ty_name(&self) -> &str {
        &self.variant_def.plain_ty_name
    }

    /// Get the name of the struct, or an ADT defined on it, if available.
    #[must_use]
    pub(crate) fn public_type_name(&self) -> &str {
        match &self.invariant {
            Some(inv) => &inv.type_name,
            None => self.plain_ty_name(),
        }
    }

    #[must_use]
    pub fn plain_rt_def_name(&self) -> &str {
        &self.variant_def.plain_rt_def_name
    }

    #[must_use]
    fn public_rt_def_name(&self) -> String {
        match &self.invariant {
            Some(inv) => inv.rt_def_name(),
            None => self.plain_rt_def_name().to_owned(),
        }
    }

    /// Add an invariant specification to this type.
    pub fn add_invariant(&mut self, spec: InvariantSpec) {
        if self.invariant.is_some() {
            panic!("already specified an invariant for type {}", self.name());
        }
        self.invariant = Some(spec);
    }

    /// Generate a Coq definition for the struct layout spec.
    #[must_use]
    pub fn generate_coq_sls_def(&self) -> String {
        self.variant_def.generate_coq_sls_def(&self.scope)
    }

    /// Generate a Coq definition for the struct type alias.
    #[must_use]
    pub fn generate_coq_type_def(&self) -> String {
        if self.is_recursive {
            self.generate_recursive_type_def()
        } else {
            let extra_context = if let Some(inv) = &self.invariant { inv.coq_params.as_slice() } else { &[] };

            // the raw type
            let mut out = self.variant_def.generate_coq_type_def(&self.scope, extra_context);

            // the invariant
            if let Some(spec) = self.invariant.as_ref() {
                let s =
                    spec.generate_coq_type_def(self.plain_ty_name(), self.plain_rt_def_name(), &self.scope);
                out.push_str(&s);
            }

            out
        }
    }

    /// Generate a type definition in case this type is a recursive type.
    fn generate_recursive_type_def(&self) -> String {
        let mut out = String::with_capacity(200);

        // we need an invariant, otherwise we cannot define a recursive type
        if let Some(inv) = self.invariant.as_ref() {
            let all_ty_params = self.scope.get_all_ty_params_with_assocs();

            let Some(_) = &inv.abstracted_refinement else {
                panic!("no abstracted refinement");
            };

            let indent = "  ";
            // the write_str impl will always return Ok.
            write!(out, "Section {}.\n", inv.type_name).unwrap();
            write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

            // add type parameters
            if !all_ty_params.params.is_empty() {
                // first push the (implicit) refinement type parameters
                write!(out, "{}Context", indent).unwrap();
                for names in &all_ty_params.params {
                    write!(out, " ({} : Type)", names.refinement_type).unwrap();
                }
                out.push_str(".\n");
            }

            let (context_names, dep_sigma) = format_extra_context_items(&inv.coq_params, &mut out).unwrap();

            // generate terms to apply the sls app to
            let mut sls_app = Vec::new();
            for names in &all_ty_params.params {
                // TODO this is duplicated with the same processing for Type::Literal...
                let term = format!("(ty_syn_type {})", names.type_term);
                sls_app.push(term);
            }

            // generate the raw rt def
            // we introduce a let binding for the recursive rt type
            write!(out, "{indent}Definition {} : Type :=\n", self.variant_def.plain_rt_def_name).unwrap();
            let ty_rt_uses = all_ty_params.get_coq_ty_rt_params().make_using_terms();
            write!(out, "{indent}{indent}let {} {ty_rt_uses}", inv.rt_def_name()).unwrap();
            write!(out, " := {} in\n", inv.rfn_type).unwrap();
            write!(out, "{indent}{indent}{}.\n", self.variant_def.rfn_type()).unwrap();

            // invariant def
            write!(
                out,
                "{}",
                inv.generate_coq_invariant_def(&self.scope, &self.variant_def.plain_rt_def_name)
            )
            .unwrap();

            // generate the functor itself
            let type_name = &inv.type_name;
            let rfn_type = &inv.rfn_type;
            let spec_name = inv.spec_name();

            write!(
                out,
                "{indent}Definition {type_name}_rec {} ({type_name}_rec' : type ({rfn_type})) : type ({rfn_type}) :=\n",
                all_ty_params.get_semantic_ty_params(),
                ).unwrap();
            write!(
                out,
                "{indent}{indent}let {type_name} {ty_rt_uses} := {} {type_name}_rec' in\n",
                self.scope,
            )
            .unwrap();
            write!(out, "{indent}{indent}let {type_name}_rt {ty_rt_uses} := {rfn_type} in\n").unwrap();
            #[allow(deprecated)]
            write!(
                out,
                "{indent}{indent}ex_plain_t _ _ ({spec_name} {}) ({}).\n",
                self.scope.identity_instantiation(),
                self.variant_def.generate_coq_type_term(sls_app)
            )
            .unwrap();

            // write the fixpoint
            #[allow(deprecated)]
            write!(
                out,
                "{indent}Definition {type_name} : {} (type ({rfn_type})) := {} type_fixpoint ({type_name}_rec {}).\n",
                self.scope.get_all_type_term(),
                self.scope,
                all_ty_params.get_semantic_ty_params().make_using_terms(),
            )
            .unwrap();

            write!(out, "{indent}Global Typeclasses Transparent {}.\n", type_name).unwrap();
            write!(out, "{indent}Definition {}_rt : Type.\n", type_name).unwrap();
            write!(
                out,
                "{indent}Proof using {ty_rt_uses} {}. let __a := normalized_rt_of_spec_ty {} in exact __a. Defined.\n",
                context_names.join(" "),
                type_name
            )
            .unwrap();
            write!(out, "{indent}Global Typeclasses Transparent {}_rt.\n", type_name).unwrap();

            // finish
            write!(out, "End {}.\n", inv.type_name).unwrap();
            write!(out, "Global Arguments {} : clear implicits.\n", inv.rt_def_name()).unwrap();
            if !context_names.is_empty() {
                let dep_sigma_str = if dep_sigma { "{_} " } else { "" };

                write!(
                    out,
                    "Global Arguments {} {}{} {{{}}}.\n",
                    inv.rt_def_name(),
                    dep_sigma_str,
                    "_ ".repeat(all_ty_params.params.len()),
                    "_ ".repeat(context_names.len())
                )
                .unwrap();
            }
        } else {
            panic!("Recursive types need an invariant");
        }
        out
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> LiteralType {
        LiteralType {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name().to_owned(),
            refinement_type: coq::term::Type::Literal(self.public_rt_def_name()),
            syn_type: SynType::Literal(self.sls_def_name().to_owned()),
        }
    }
}

/// A builder for ADT variants without fancy invariants etc.
pub struct VariantBuilder<'def> {
    /// the fields
    fields: Vec<(String, Type<'def>)>,
    /// the variant's representation mode
    repr: StructRepr,
    /// the variants's name
    name: String,
}

impl<'def> VariantBuilder<'def> {
    #[must_use]
    pub fn finish(self) -> AbstractVariant<'def> {
        let sls_def_name: String = format!("{}_sls", &self.name);
        let st_def_name: String = format!("{}_st", &self.name);
        let plain_ty_name: String = format!("{}_ty", &self.name);
        let plain_rt_def_name: String = format!("{}_rt", &self.name);

        AbstractVariant {
            fields: self.fields,
            repr: self.repr,
            name: self.name,
            plain_ty_name,
            sls_def_name,
            st_def_name,
            plain_rt_def_name,
        }
    }

    /// Finish building the struct type and generate an abstract struct definition.
    #[must_use]
    fn finish_as_struct(self, scope: GenericScope<'def>) -> AbstractStruct<'def> {
        let variant = self.finish();
        AbstractStruct {
            variant_def: variant,
            invariant: None,
            scope,
            is_recursive: false,
        }
    }

    /// Initialize a struct builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub fn new(name: String, repr: StructRepr) -> VariantBuilder<'def> {
        VariantBuilder {
            fields: Vec::new(),
            name,
            repr,
        }
    }

    /// Append a field to the struct def.
    pub fn add_field(&mut self, name: &str, ty: Type<'def>) {
        self.fields.push((name.to_owned(), ty));
    }
}

/// Create a struct representation of a tuple with `num_fields`, all of which are generic.
#[must_use]
pub fn make_tuple_struct_repr<'def>(num_fields: usize) -> AbstractStruct<'def> {
    let name = format!("tuple{}", num_fields);

    let mut scope = GenericScope::empty();
    let mut builder = VariantBuilder::new(name, StructRepr::ReprRust);

    for i in 0..num_fields {
        let param_name = format!("T{}", i);
        let lit = LiteralTyParam::new(&param_name, &param_name);
        scope.add_ty_param(lit.clone());

        builder.add_field(&i.to_string(), Type::LiteralParam(lit));
    }

    builder.finish_as_struct(scope)
}

/// A usage of an `AbstractStruct` that instantiates its type parameters.
#[derive(Clone, Debug)]
pub struct AbstractStructUse<'def> {
    /// reference to the struct's definition, or None if unit
    pub(crate) def: Option<AbstractStructRef<'def>>,

    /// Instantiations for type parameters
    pub(crate) scope_inst: GenericScopeInst<'def>,

    /// does this refer to the raw type without invariants?
    raw: TypeIsRaw,
}

impl<'def> AbstractStructUse<'def> {
    #[must_use]
    pub const fn new(s: AbstractStructRef<'def>, scope_inst: GenericScopeInst<'def>, raw: TypeIsRaw) -> Self {
        AbstractStructUse {
            def: Some(s),
            scope_inst,
            raw,
        }
    }

    /// Creates a new use of unit.
    #[must_use]
    pub fn new_unit() -> Self {
        AbstractStructUse {
            def: None,
            scope_inst: GenericScopeInst::empty(),
            raw: TypeIsRaw::Yes,
        }
    }

    #[must_use]
    pub(crate) fn is_raw(&self) -> bool {
        self.raw == TypeIsRaw::Yes
    }

    fn make_raw(&mut self) {
        self.raw = TypeIsRaw::Yes;
    }

    /// Get the refinement type of a struct usage.
    /// This requires that all type parameters of the struct have been instantiated.
    #[must_use]
    fn get_rfn_type(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return coq::term::Type::Unit.to_string();
        };

        let rfn_instantiations: Vec<_> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Type::get_rfn_type).collect();

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        let inv = &def.invariant.as_ref();

        if self.is_raw() || inv.is_none() {
            let rfn_type = def.plain_rt_def_name().to_owned();
            let applied = coq::term::App::new(rfn_type, rfn_instantiations);
            applied.to_string()
        } else {
            let rfn_type = inv.unwrap().rt_def_name();
            let applied = coq::term::App::new(rfn_type, rfn_instantiations);
            applied.to_string()
        }
    }

    /// Get the `syn_type` term for this struct use.
    #[must_use]
    fn generate_syn_type_term(&self) -> SynType {
        let Some(def) = self.def.as_ref() else {
            return SynType::Unit;
        };

        // first get the syntys for the type params
        let param_sts: Vec<SynType> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Into::into).collect();

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        let specialized_spec = coq::term::App::new(def.st_def_name().to_owned(), param_sts);
        SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this struct use.
    #[must_use]
    fn generate_type_term(&self) -> String {
        let Some(def) = self.def.as_ref() else {
            return Type::Unit.to_string();
        };

        let rt_inst = self
            .scope_inst
            .get_all_ty_params_with_assocs()
            .iter()
            .map(|ty| format!("({})", ty.get_rfn_type()))
            .join(" ");

        let def = def.borrow();
        let def = def.as_ref().unwrap();
        if !self.is_raw() && def.invariant.is_some() {
            let Some(inv) = &def.invariant else {
                unreachable!();
            };

            format!("({} {rt_inst} {})", inv.type_name, self.scope_inst.instantiation())
        } else {
            format!("({} {rt_inst} {})", def.plain_ty_name(), self.scope_inst.instantiation())
        }
    }
}

/// Specification of an enum in terms of a Coq type refining it.
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct EnumSpec {
    /// the refinement type of the enum
    pub rfn_type: coq::term::Type,
    /// the surface refinement type of the enum
    pub xt_type: coq::term::Type,
    /// the injection from from xt to rfn
    pub xt_injection: String,
    /// the refinement patterns for each of the variants
    /// eg. for options:
    /// - `(None, [], -[])`
    /// - `(Some, [x], -[x])`
    pub variant_patterns: Vec<(String, Vec<String>, String)>,
    /// true if the map from refinement to variants is partial
    pub is_partial: bool,
}

/// Enum to represent large discriminants
#[derive(Clone, Copy, Display, PartialEq, Debug, Eq)]
pub enum Int128 {
    #[display("{}", _0)]
    Signed(i128),
    #[display("{}", _0)]
    Unsigned(u128),
}
impl Add<u32> for Int128 {
    type Output = Self;

    fn add(self, other: u32) -> Self {
        match self {
            Self::Signed(i) => Self::Signed(i + i128::from(other)),
            Self::Unsigned(i) => Self::Unsigned(i + u128::from(other)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AbstractEnum<'def> {
    /// variants of this enum: name, variant, a mask describing which of the type parameters it uses, and the
    /// discriminant
    variants: Vec<(String, AbstractStructRef<'def>, Int128)>,

    /// specification
    spec: EnumSpec,
    /// the enum's name
    name: String,
    /// the representation of the enum
    repr: EnumRepr,

    /// an optional declaration of a Coq inductive for this enum
    optional_inductive_def: Option<coq::inductive::Inductive>,

    /// name of the plain enum type (without additional invariants)
    plain_ty_name: String,
    plain_rt_name: String,
    /// name of the enum_layout_spec definition
    els_def_name: String,
    st_def_name: String,
    /// name of the enum definition
    enum_def_name: String,

    /// type of the integer discriminant
    discriminant_type: IntType,

    /// these should be the same also across all the variants
    scope: GenericScope<'def>,
}

pub type AbstractEnumRef<'def> = &'def RefCell<Option<AbstractEnum<'def>>>;

impl<'def> AbstractEnum<'def> {
    /// Get the name of this enum.
    #[must_use]
    fn name(&self) -> &str {
        &self.name
    }

    #[must_use]
    pub(crate) fn public_type_name(&self) -> &str {
        &self.plain_ty_name
    }

    #[must_use]
    fn public_rt_def_name(&self) -> &str {
        &self.plain_rt_name
    }

    #[must_use]
    fn els_def_name(&self) -> &str {
        &self.els_def_name
    }

    #[must_use]
    pub fn get_variant(&self, i: usize) -> Option<&(String, AbstractStructRef<'def>, Int128)> {
        self.variants.get(i)
    }

    /// Generate a Coq definition for the enum layout spec, and all the `struct_layout_specs` for the
    /// variants.
    #[must_use]
    pub fn generate_coq_els_def(&self) -> String {
        let indent = "  ";

        let mut out = String::with_capacity(200);

        out.push_str(&format!("Section {}.\n", self.els_def_name));
        out.push_str(&format!("{indent}Context `{{RRGS : !refinedrustGS Σ}}.\n"));
        out.push('\n');

        // add syntype parameters
        let all_ty_st_params = self.scope.get_all_ty_params_with_assocs().get_coq_ty_st_params();
        let all_ty_st_params_uses = all_ty_st_params.make_using_terms();

        // generate all the component structs
        for (_, v, _) in &self.variants {
            let vbor = v.borrow();
            let vbor = vbor.as_ref().unwrap();

            out.push_str(&vbor.variant_def.generate_coq_sls_def_core(&all_ty_st_params));
            out.push('\n');
        }

        // intro to main def
        out.push_str(&format!(
            "{indent}Program Definition {} {all_ty_st_params} : enum_layout_spec := mk_els \"{}\" {} [",
            self.els_def_name, self.name, self.discriminant_type
        ));

        push_str_list!(out, &self.variants, ";", |(name, var, _)| {
            let vbor = var.borrow();
            let vbor = vbor.as_ref().unwrap();

            format!("\n{}{}(\"{}\", {} {all_ty_st_params})", indent, indent, name, vbor.st_def_name())
        });

        // write the repr
        out.push_str(&format!("] {} [", self.repr));

        // now write the tag-discriminant list
        push_str_list!(out, &self.variants, "; ", |(name, _, discr)| format!("(\"{name}\", {discr})"));

        out.push_str("] _ _ _ _.\n");
        out.push_str(&format!("{indent}Next Obligation. repeat first [econstructor | set_solver]. Qed.\n"));
        out.push_str(&format!("{indent}Next Obligation. done. Qed.\n"));
        out.push_str(&format!("{indent}Next Obligation. repeat first [econstructor | set_solver]. Qed.\n"));
        out.push_str(&format!(
            "{indent}Next Obligation. repeat first [econstructor | init_cache; solve_goal]. all: unsafe_unfold_common_caesium_defs; simpl; lia. Qed.\n"
        ));
        out.push_str(&format!("{indent}Global Typeclasses Opaque {}.\n", self.els_def_name));

        // also write an st definition
        out.push_str(&format!(
            "{indent}Definition {} {all_ty_st_params} : syn_type := {} {all_ty_st_params_uses}.\n",
            self.st_def_name, self.els_def_name,
        ));

        // finish
        out.push_str(&format!("End {}.\n", self.els_def_name));

        out
    }

    /// Generate a function that maps the refinement to the tag as a Coq string (`enum_tag`).
    fn generate_enum_tag(&self) -> String {
        let mut out = String::with_capacity(200);

        let spec = &self.spec;
        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((name, _, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            write!(out, "| {} => Some \"{name}\" ", coq::term::App::new(pat, apps.clone())).unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => None ").unwrap();
        }
        write!(out, "end").unwrap();

        out
    }

    /// Generate a function that maps the refinement to the refinement type.
    /// Assumes that the generated code is placed in an environment where all the type parameters
    /// are available and the variant types have been instantiated already.
    fn generate_enum_rt(&self) -> String {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((_, _, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            write!(out, "| {} => _", coq::term::App::new(pat, apps.clone())).unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => unit%type ").unwrap();
        }
        write!(out, " end").unwrap();

        out
    }

    /// Generate a function that maps the refinement to the semantic type.
    fn generate_enum_ty(&self) -> String {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((_, var, _), (pat, apps, _)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            let v = var.borrow();
            let v = v.as_ref().unwrap();
            // we can just use the plain name here, because we assume this is used in an
            // environment where all the type parametes are already instantiated.
            let ty = v.public_type_name();

            write!(
                out,
                "| {} => {ty} {}",
                coq::term::App::new(pat, apps.clone()),
                v.scope.identity_instantiation()
            )
            .unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => unit_t ").unwrap();
        }
        write!(out, " end").unwrap();

        out
    }

    /// Generate a function that maps the refinement to the refinement.
    fn generate_enum_rfn(&self) -> String {
        let mut out = String::with_capacity(200);
        let spec = &self.spec;

        write!(out, "λ rfn, match rfn with ").unwrap();
        for ((_, _, _), (pat, apps, rfn)) in self.variants.iter().zip(spec.variant_patterns.iter()) {
            write!(out, "| {} => {rfn}", coq::term::App::new(pat, apps.clone())).unwrap();
        }
        if spec.is_partial {
            write!(out, "| _ => () ").unwrap();
        }
        write!(out, " end").unwrap();

        out
    }

    /// Generate a function that maps (valid) tags to the corresponding Coq type for the variant.
    fn generate_enum_match(&self) -> String {
        let conditions: Vec<_> = self
            .variants
            .iter()
            .zip(self.spec.variant_patterns.iter())
            .map(|((name, var, _), (pat, apps, rfn))| {
                let v = var.borrow();
                let v = v.as_ref().unwrap();
                let ty = v.public_type_name();

                // injection
                let inj = format!("(λ '( {rfn}), {})", coq::term::App::new(pat, apps.clone()));

                format!(
                    "if (decide (variant = \"{name}\")) then Some $ mk_enum_tag_sem _ ({ty} {}) {inj}",
                    v.scope.identity_instantiation()
                )
            })
            .collect();
        if conditions.is_empty() {
            "λ variant, None".to_owned()
        } else {
            format!("λ variant, {} else None", conditions.join(" else "))
        }
    }

    fn generate_lfts(&self) -> String {
        // TODO: probably should build this up modularly over the fields

        let mut v: Vec<_> = self
            .scope
            .get_all_ty_params_with_assocs()
            .params
            .iter()
            .map(|p| format!("(ty_lfts {})", p.type_term))
            .collect();
        v.push("[]".to_owned());
        v.join(" ++ ")
    }

    fn generate_wf_elctx(&self) -> String {
        // TODO: probably should build this up modularly over the fields
        let mut v: Vec<_> = self
            .scope
            .get_all_ty_params_with_assocs()
            .params
            .iter()
            .map(|p| format!("(ty_wf_E {})", p.type_term))
            .collect();
        v.push("[]".to_owned());
        v.join(" ++ ")
    }

    fn generate_construct_enum(&self) -> String {
        let mut out = String::with_capacity(200);
        let indent = "  ";

        for ((tag, s, _), (pat, args, res)) in self.variants.iter().zip(self.spec.variant_patterns.iter()) {
            write!(
                out,
                "{indent}Global Program Instance construct_enum_{}_{tag} {} {} ",
                self.name,
                self.scope.get_all_ty_params_with_assocs().params.iter().map(|ty| &ty.type_term).join(" "),
                args.join(" ")
            )
            .unwrap();

            // add st constraints on params
            let mut sls_app = Vec::new();
            for ty in &self.scope.get_all_ty_params_with_assocs().params {
                write!(out, "{} `{{!TCDone ({} = ty_syn_type {})}} ", ty.syn_type, ty.syn_type, ty.type_term)
                    .unwrap();
                sls_app.push(ty.syn_type.clone());
            }
            let s = s.borrow();
            let s = s.as_ref().unwrap();
            #[allow(deprecated)]
            let ty_def_term = s.variant_def.generate_coq_type_term(sls_app);

            write!(
                out,
                ": ConstructEnum ({} {}) \"{tag}\" ({ty_def_term}) {res} {} := construct_enum _ _ _ _ _.\n",
                self.enum_def_name,
                self.scope.identity_instantiation(),
                coq::term::App::new(pat, args.clone())
            )
            .unwrap();
            write!(out, "{indent}Next Obligation. done. Defined.\n").unwrap();
            write!(out, "{indent}Next Obligation. intros; unfold TCDone in *; naive_solver. Qed.\n").unwrap();
            write!(out, "{indent}Next Obligation. intros; unfold TCDone in *; naive_solver. Qed.\n").unwrap();
            write!(out, "{indent}Next Obligation. intros; unfold TCDone in *; naive_solver. Qed.\n").unwrap();
        }

        out
    }

    #[must_use]
    pub fn generate_coq_type_def(&self) -> String {
        let mut out = String::with_capacity(200);

        let all_ty_params = self.scope.get_all_ty_params_with_assocs();

        let indent = "  ";
        // the write_str impl will always return Ok.
        write!(out, "Section {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{}Context `{{RRGS : !refinedrustGS Σ}}.\n", indent).unwrap();

        // add type parameters, and build a list of terms to apply the els def to
        if !all_ty_params.params.is_empty() {
            // first push the (implicit) refinement type parameters
            write!(out, "{}Context", indent).unwrap();
            for names in &all_ty_params.params {
                write!(out, " {{{} : Type}}", names.refinement_type).unwrap();
            }
            out.push_str(".\n");
        }
        out.push('\n');

        let rt_param_uses = all_ty_params.get_coq_ty_rt_params().make_using_terms();

        // define types and type abstractions for all the component types.
        // TODO: we should actually use the abstracted types here.
        for (_name, variant, _) in &self.variants {
            let v = variant.borrow();
            let v = v.as_ref().unwrap();
            // TODO: might also need to handle extra context items
            write!(out, "{}\n", v.variant_def.generate_coq_type_def_core(&v.scope, &[])).unwrap();

            if let Some(inv) = &v.invariant {
                let base_type = format!(
                    "({} {})",
                    v.variant_def.plain_ty_name.as_str(),
                    v.scope.identity_instantiation(),
                );
                let inv_def = inv.generate_coq_type_def_core(
                    &base_type,
                    v.variant_def.plain_rt_def_name.as_str(),
                    &rt_param_uses,
                    &v.scope,
                    &[],
                );
                write!(out, "{}\n", inv_def).unwrap();
            }
        }

        // write the Coq inductive, if applicable
        if let Some(ind) = &self.optional_inductive_def {
            let name = ind.get_name();

            let mut document = coq::Document::default();

            let mut out = IndentWriter::new(BASE_INDENT, &mut out);
            writeln!(out).unwrap();

            let comment = format!("Auto-generated representation of {}", name);
            document.push(coq::Sentence::Comment(comment));
            document.push(coq::command::Command::Inductive(ind.clone()));

            document.push(
                coq::command::CommandAttrs::new(coq::command::Instance(
                    coq::term::Type::Literal(format!("Inhabited {}", name)),
                    coq::proof::Proof::new(coq::proof::Terminator::Qed, |proof| {
                        proof.push(model::LTac::SolveInhabited);
                    }),
                ))
                .attributes("global"),
            );

            writeln!(out, "{}", document).unwrap();
        }

        // build the els term applied to generics
        // generate terms to apply the sls app to
        let mut els_app = Vec::new();
        for names in &all_ty_params.params {
            let term = format!("(ty_syn_type {})", names.type_term);
            els_app.push(term);
        }
        let els_app_term = coq::term::App::new(&self.els_def_name, els_app);

        // main def
        #[allow(deprecated)]
        write!(
            out,
            "{indent}Program Definition {} : {} (enum ({})) := {} mk_enum\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}_\n\
               {indent}{indent}({els_app_term})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}({})\n\
               {indent}{indent}_ _ _.\n",
            self.enum_def_name,
            self.scope.get_all_type_term(),
            self.spec.rfn_type,
            self.scope,
            self.spec.xt_type,
            self.spec.xt_injection,
            self.generate_enum_tag(),
            self.generate_enum_rt(),
            self.generate_enum_ty(),
            self.generate_enum_rfn(),
            self.generate_enum_match(),
            self.generate_lfts(),
            self.generate_wf_elctx(),
        )
        .unwrap();
        write!(out, "{indent}Next Obligation. solve_mk_enum_ty_lfts_incl. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. solve_mk_enum_ty_wf_E. Qed.\n").unwrap();
        write!(out, "{indent}Next Obligation. solve_mk_enum_tag_consistent. Defined.\n\n").unwrap();

        // define the actual type
        #[allow(deprecated)]
        write!(
            out,
            "{indent}Definition {} : {} (type _) := {} enum_t ({} {}).\n",
            self.plain_ty_name,
            self.scope.get_all_type_term(),
            self.scope,
            self.enum_def_name,
            self.scope.identity_instantiation(),
        )
        .unwrap();

        // generate the refinement type definition
        write!(out, "{indent}Definition {} : Type.\n", self.plain_rt_name).unwrap();
        write!(
            out,
            "{indent}Proof using {rt_param_uses}. let __a := normalized_rt_of_spec_ty {} in exact __a. Defined.\n",
            self.plain_ty_name
        )
        .unwrap();

        // make it Typeclasses Transparent
        write!(out, "{indent}Global Typeclasses Transparent {}.\n", self.plain_ty_name).unwrap();
        write!(out, "{indent}Global Typeclasses Transparent {}.\n\n", self.plain_rt_name).unwrap();

        write!(out, "{}", self.generate_construct_enum()).unwrap();

        write!(out, "End {}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_rt_name).unwrap();
        write!(out, "Global Arguments {} : clear implicits.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Arguments {} {{_ _}}.\n", self.plain_ty_name).unwrap();
        write!(out, "Global Hint Unfold {} : solve_protected_eq_db.\n", self.plain_ty_name).unwrap();

        out
    }

    /// Make a literal type.
    #[must_use]
    pub fn make_literal_type(&self) -> LiteralType {
        LiteralType {
            rust_name: Some(self.name().to_owned()),
            type_term: self.public_type_name().to_owned(),
            refinement_type: coq::term::Type::Literal(self.public_rt_def_name().to_owned()),
            syn_type: SynType::Literal(self.els_def_name().to_owned()),
        }
    }
}

/// A builder for plain enums without fancy invariants etc.
pub struct EnumBuilder<'def> {
    /// the variants
    variants: Vec<(String, AbstractStructRef<'def>, Int128)>,
    /// the enum's name
    name: String,
    /// names for the type parameters (for the Coq definitions)
    scope: GenericScope<'def>,
    /// type of the integer discriminant
    discriminant_type: IntType,
    /// representation options for the enum
    repr: EnumRepr,
}

impl<'def> EnumBuilder<'def> {
    /// Finish building the enum type and generate an abstract enum definition.
    #[must_use]
    pub fn finish(
        self,
        optional_inductive_def: Option<coq::inductive::Inductive>,
        spec: EnumSpec,
    ) -> AbstractEnum<'def> {
        let els_def_name: String = format!("{}_els", &self.name);
        let st_def_name: String = format!("{}_st", &self.name);
        let plain_ty_name: String = format!("{}_ty", &self.name);
        let plain_rt_name: String = format!("{}_rt", &self.name);
        let enum_def_name: String = format!("{}_enum", &self.name);

        AbstractEnum {
            variants: self.variants,
            name: self.name,
            plain_ty_name,
            plain_rt_name,
            els_def_name,
            st_def_name,
            enum_def_name,
            spec,
            optional_inductive_def,
            scope: self.scope,
            discriminant_type: self.discriminant_type,
            repr: self.repr,
        }
    }

    /// Initialize an enum builder.
    /// `ty_params` are the user-facing type parameter names in the Rust code.
    #[must_use]
    pub fn new(
        name: String,
        scope: GenericScope<'def>,
        discriminant_type: IntType,
        repr: EnumRepr,
    ) -> EnumBuilder<'def> {
        EnumBuilder {
            variants: Vec::new(),
            name,
            scope,
            discriminant_type,
            repr,
        }
    }

    /// Append a variant to the struct def.
    /// `name` is also the Coq constructor of the refinement type we use.
    /// `used_params` is a mask describing which type parameters are used by this variant.
    pub fn add_variant(&mut self, name: &str, variant: AbstractStructRef<'def>, discriminant: Int128) {
        self.variants.push((name.to_owned(), variant, discriminant));
    }
}

/// A usage of an `AbstractEnum` that instantiates its type parameters.
#[derive(Clone, Debug)]
pub struct AbstractEnumUse<'def> {
    /// reference to the enum's definition
    pub(crate) def: AbstractEnumRef<'def>,

    /// Instantiations for type parameters
    pub(crate) scope_inst: GenericScopeInst<'def>,
}

impl<'def> AbstractEnumUse<'def> {
    #[must_use]
    pub const fn new(s: AbstractEnumRef<'def>, scope_inst: GenericScopeInst<'def>) -> Self {
        AbstractEnumUse { def: s, scope_inst }
    }

    /// Get the refinement type of an enum usage.
    /// This requires that all type parameters of the enum have been instantiated.
    #[must_use]
    fn get_rfn_type(&self) -> String {
        let def = self.def.borrow();
        let def = def.as_ref().unwrap();

        let rfn_instantiations: Vec<_> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Type::get_rfn_type).collect();

        let applied = coq::term::App::new(def.plain_rt_name.clone(), rfn_instantiations);
        applied.to_string()
    }

    /// Get the `syn_type` term for this enum use.
    #[must_use]
    fn generate_syn_type_term(&self) -> SynType {
        let param_sts: Vec<SynType> =
            self.scope_inst.get_all_ty_params_with_assocs().iter().map(Into::into).collect();

        let def = self.def.borrow();
        let def = def.as_ref().unwrap();
        // [my_spec] [params]
        let specialized_spec = coq::term::App::new(def.st_def_name.clone(), param_sts);
        SynType::Literal(specialized_spec.to_string())
    }

    /// Generate a string representation of this enum use.
    #[must_use]
    fn generate_type_term(&self) -> String {
        let def = self.def.borrow();
        let def = def.as_ref().unwrap();

        let rt_inst = self
            .scope_inst
            .get_all_ty_params_with_assocs()
            .iter()
            .map(|ty| format!("({})", ty.get_rfn_type()))
            .join(" ");
        format!("({} {} {})", def.plain_ty_name, rt_inst, self.scope_inst.instantiation())
    }
}

/// A representation of Caesium layouts we are interested in.
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub enum Layout {
    // in the case of  32bits
    Ptr,

    // layout specified by the int type
    Int(IntType),

    // size 1, similar to u8/i8
    Bool,

    // size 4, similar to u32
    Char,

    // guaranteed to have size 0 and alignment 1.
    Unit,

    /// used for variable layout terms, e.g. for struct layouts or generics
    Literal(coq::term::App<String, String>),

    /// padding of a given number of bytes
    Pad(u32),
}

impl Display for Layout {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ptr => write!(f, "void*"),
            Self::Int(it) => write!(f, "(it_layout {})", it),
            Self::Bool => write!(f, "bool_layout"),
            Self::Char => write!(f, "char_layout"),
            Self::Unit => write!(f, "(layout_of unit_sl)"),
            Self::Literal(n) => write!(f, "{}", n),
            Self::Pad(s) => write!(f, "(Layout {}%nat 0%nat)", s),
        }
    }
}

// better representation of Iprops?
// - in particular for building the existential abstraction, direct support for existentials would be good.
// - DeBruijn probably not worth it, I don't need subst or anything like that. just try to keep variables
//   apart when generating them.

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum IProp {
    True,
    Atom(String),
    Pure(String),
    // prop, name
    PureWithName(String, String),
    Sep(Vec<IProp>),
    Disj(Vec<IProp>),
    Conj(Vec<IProp>),
    Wand(Box<IProp>, Box<IProp>),
    Exists(Vec<coq::binder::Binder>, Box<IProp>),
    All(Vec<coq::binder::Binder>, Box<IProp>),
}

fn fmt_with_op<T>(v: &[T], op: &str, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error>
where
    T: Display,
{
    if v.is_empty() {
        return write!(f, "True");
    }

    write_list!(f, v, &format!("\n{op} "), "({})")
}

fn fmt_binders(
    binders: &[coq::binder::Binder],
    op: &str,
    f: &mut fmt::Formatter<'_>,
) -> Result<(), fmt::Error> {
    write!(f, "{} ", op)?;
    write_list!(f, binders, " ")
}

impl Display for IProp {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        match self {
            Self::True => write!(f, "True"),
            Self::Atom(a) => write!(f, "{a}"),
            Self::Pure(a) => write!(f, "⌜{a}⌝"),
            Self::PureWithName(p, name) => write!(f, "⌜name_hint \"{name}\" ({p})⌝"),
            Self::Sep(v) => fmt_with_op(v, "∗", f),
            Self::Disj(v) => fmt_with_op(v, "∨", f),
            Self::Conj(v) => fmt_with_op(v, "∧", f),
            Self::Wand(l, r) => write!(f, "({l}) -∗ {r}"),
            Self::Exists(b, p) => {
                if !b.is_empty() {
                    fmt_binders(b, "∃", f)?;
                    write!(f, ", ")?;
                }
                write!(f, "{p}")
            },
            Self::All(b, p) => {
                fmt_binders(b, "∀", f)?;
                write!(f, ", {p}")
            },
        }
    }
}

/// Representation of an Iris predicate
#[derive(Clone, Debug)]
pub struct IPropPredicate {
    binders: Vec<coq::binder::Binder>,
    prop: IProp,
}

impl IPropPredicate {
    #[must_use]
    pub fn new(binders: Vec<coq::binder::Binder>, prop: IProp) -> Self {
        Self { binders, prop }
    }
}

impl Display for IPropPredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt_binders(&self.binders, "λ", f)?;
        write!(f, ", ({})%I : iProp Σ", self.prop)
    }
}

/// Representation of a loop invariant
#[derive(Clone, Constructor, Debug)]
pub struct LoopSpec {
    /// the functional invariant as a predicate on the refinement of local variables.
    func_predicate: IPropPredicate,
    inv_locals: Vec<String>,
    preserved_locals: Vec<String>,
    uninit_locals: Vec<String>,
}
impl Display for LoopSpec {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "([{}], [{}], [{}], wrap_inv ({}), wrap_inv (λ (L : llctx), True%I : iProp Σ))",
            self.inv_locals.join("; "),
            self.preserved_locals.join("; "),
            self.uninit_locals.join("; "),
            self.func_predicate
        )?;

        Ok(())
    }
}

/// A finished inner function specification.
#[derive(Clone, Debug)]
pub enum InnerFunctionSpec<'def> {
    /// A specification declared via attributes
    Lit(LiteralFunctionSpec<'def>),
    /// Use the default specification of a trait
    TraitDefault(InstantiatedTraitFunctionSpec<'def>),
}

impl<'def> InnerFunctionSpec<'def> {
    fn write_spec_term<F>(
        &self,
        f: &mut F,
        scope: &GenericScope<'def, LiteralTraitSpecUseRef<'def>>,
    ) -> fmt::Result
    where
        F: fmt::Write,
    {
        match self {
            Self::Lit(lit) => lit.write_spec_term(f, scope),
            Self::TraitDefault(def) => def.write_spec_term(f, scope),
        }
    }

    #[must_use]
    pub(crate) fn get_params(&self) -> Option<&[coq::binder::Binder]> {
        match self {
            Self::Lit(lit) => Some(&lit.params),
            Self::TraitDefault(_) => None,
        }
    }

    /// Determines whether this spec needs trait requirements quantified.
    #[must_use]
    const fn needs_trait_req_params(&self) -> bool {
        match self {
            Self::Lit(_) => true,
            Self::TraitDefault(_) => false,
        }
    }
}

/// A Radium function specification.
#[derive(Clone, Debug)]
#[allow(clippy::partial_pub_fields)]
pub struct FunctionSpec<'def, T> {
    /// The name of the spec
    pub spec_name: String,
    pub function_name: String,

    /// The name of the trait incl definition
    /// This is `Some` if this is a function spec that is not part of a trait decl.
    pub trait_req_incl_name: Option<String>,

    /// Generics
    pub(crate) generics: GenericScope<'def, LiteralTraitSpecUseRef<'def>>,

    /// Coq-level parameters the typing statement needs
    early_coq_params: coq::binder::BinderList,
    late_coq_params: coq::binder::BinderList,

    pub(crate) spec: T,
}

impl<'def, T> FunctionSpec<'def, T> {
    pub(crate) fn replace_spec<U>(self, new_spec: U) -> FunctionSpec<'def, U> {
        FunctionSpec {
            spec: new_spec,
            trait_req_incl_name: self.trait_req_incl_name,
            spec_name: self.spec_name,
            function_name: self.function_name,
            generics: self.generics,
            early_coq_params: self.early_coq_params,
            late_coq_params: self.late_coq_params,
        }
    }

    #[must_use]
    pub(crate) fn empty(
        spec_name: String,
        trait_req_incl_name: Option<String>,
        function_name: String,
        spec: T,
    ) -> Self {
        Self {
            spec_name,
            trait_req_incl_name,
            function_name,
            generics: GenericScope::empty(),
            early_coq_params: coq::binder::BinderList::empty(),
            late_coq_params: coq::binder::BinderList::empty(),
            spec,
        }
    }

    #[must_use]
    pub(crate) fn get_spec_name(&self) -> &str {
        &self.spec_name
    }

    /// Add a coq parameter that comes before type parameters.
    pub(crate) fn add_early_coq_param(&mut self, param: coq::binder::Binder) {
        self.early_coq_params.0.push(param);
    }

    /// Add a coq parameter that comes after type parameters.
    pub(crate) fn add_late_coq_param(&mut self, param: coq::binder::Binder) {
        self.late_coq_params.0.push(param);
    }
}

impl<'def> FunctionSpec<'def, InnerFunctionSpec<'def>> {
    /// Get all Coq binders for the Coq spec definition.
    #[must_use]
    pub(crate) fn get_all_spec_coq_params(&self) -> coq::binder::BinderList {
        // Important: early parameters should always be first, as they include trait specs.
        // Important: the type parameters should be introduced before late parameters to ensure they are in
        // scope.
        let mut params = self.early_coq_params.clone();

        let typarams = self.generics.get_all_ty_params_with_assocs();
        params.append(typarams.get_coq_ty_params().0);

        params.append(self.late_coq_params.0.clone());

        // finally, the trait spec parameters
        let trait_params = if self.spec.needs_trait_req_params() {
            self.generics.get_all_attr_trait_parameters(true)
        } else {
            self.generics.get_surrounding_attr_trait_parameters(true)
        };

        params.append(trait_params.0);

        params
    }

    /// Get all Coq binders for the Coq trait incl definition.
    #[must_use]
    pub(crate) fn get_all_trait_req_coq_params(&self) -> coq::binder::BinderList {
        let typarams = self.generics.get_all_ty_params_with_assocs();
        let mut params = typarams.get_coq_ty_params();

        // finally, the trait spec parameters
        let trait_params = if self.spec.needs_trait_req_params() {
            self.generics.get_all_trait_parameters(true)
        } else {
            self.generics.get_surrounding_trait_parameters(true)
        };

        params.append(trait_params.0);

        params
    }

    /// Get all Coq binders for the Coq lemma definition.
    #[must_use]
    pub(crate) fn get_all_lemma_coq_params(&self) -> coq::binder::BinderList {
        // Important: early parameters should always be first, as they include trait specs.
        // Important: the type parameters should be introduced before late parameters to ensure they are in
        // scope.
        let mut params = self.early_coq_params.clone();

        let typarams = self.generics.get_all_ty_params_with_assocs();
        params.append(typarams.get_coq_ty_params().0);

        params.append(self.late_coq_params.0.clone());

        // finally, the trait spec parameters
        let trait_params = if self.spec.needs_trait_req_params() {
            self.generics.get_all_trait_parameters(true)
        } else {
            self.generics.get_surrounding_trait_parameters(true)
        };

        params.append(trait_params.0);

        params
    }
}

impl<'def> FunctionSpec<'def, InnerFunctionSpec<'def>> {
    /// Check whether this spec is complete.
    #[must_use]
    pub const fn is_complete(&self) -> bool {
        match &self.spec {
            InnerFunctionSpec::Lit(lit) => lit.has_spec,
            InnerFunctionSpec::TraitDefault(_) => true,
        }
    }

    #[must_use]
    fn generate_trait_req_incl_def(&self) -> coq::command::Definition {
        let params = self.get_all_trait_req_coq_params();

        let mut late_pre = Vec::new();
        for trait_use in self
            .generics
            .get_surrounding_trait_requirements()
            .iter()
            .chain(self.generics.get_direct_trait_requirements().iter())
        {
            let trait_use = trait_use.borrow();
            let trait_use = trait_use.as_ref().unwrap();
            if !trait_use.is_used_in_self_trait {
                let spec_precond = trait_use.make_spec_param_precond();
                late_pre.push(spec_precond);
            }
        }
        let term = coq::term::Term::Infix("∧".to_owned(), late_pre);

        // quantify over the generic scope
        let mut quantified_term = String::new();
        self.generics.format(&mut quantified_term, false, false, &[], &[], &[]).unwrap();
        quantified_term.push_str(&format!(" ({term})"));

        let name = self.trait_req_incl_name.clone().unwrap();
        coq::command::Definition {
            name,
            params,
            ty: Some(coq::term::Type::Literal("spec_with _ _ Prop".to_owned())),
            body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(quantified_term)),
        }
    }
}

// TODO: Deprecated: Generate a coq::Document instead.
impl<'def> Display for FunctionSpec<'def, InnerFunctionSpec<'def>> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut doc = coq::Document::default();
        if self.trait_req_incl_name.is_some() {
            // first generate the trait req incl definition, if this spec needs one.
            doc.push(coq::command::Command::Definition(self.generate_trait_req_incl_def()));
        }

        let params = self.get_all_spec_coq_params();

        let mut term = String::with_capacity(100);
        self.spec.write_spec_term(&mut term, &self.generics)?;

        let coq_def = coq::command::Definition {
            name: self.spec_name.clone(),
            params,
            ty: None,
            body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(term)),
        };
        doc.push(coq::command::Command::Definition(coq_def));

        write!(f, "{doc}")
    }
}

// TODO: separate this into defining and using occurrence.
// extra_link_assum should not be part of a using occurrence.
/// A function specification below generics.
#[derive(Clone, Debug)]
pub struct LiteralFunctionSpec<'def> {
    params: Vec<coq::binder::Binder>,

    /// external lifetime context
    elctx: Vec<ExtLftConstr>,
    /// precondition as a separating conjunction
    pre: IProp,
    /// argument types including refinements
    args: Vec<TypeWithRef<'def>>,
    /// existential quantifiers for the postcondition
    existentials: Vec<coq::binder::Binder>,
    /// return type
    ret: TypeWithRef<'def>,
    /// postcondition as a separating conjunction
    post: IProp,

    // TODO remove
    has_spec: bool,
}

impl<'def> LiteralFunctionSpec<'def> {
    /// Format the external lifetime contexts, consisting of constraints between lifetimes.
    fn format_elctx(&self, scope: &GenericScope<'def, LiteralTraitSpecUseRef<'def>>) -> String {
        let mut out = String::with_capacity(100);

        out.push_str("λ ϝ, [");

        // implied bounds on inputs/outputs
        push_str_list!(out, &self.elctx, "; ", |(lft1, lft2)| format!("({lft1}, {lft2})"));

        // all lifetime parameters outlive this function
        if !self.elctx.is_empty() && !scope.lfts.is_empty() {
            out.push_str("; ");
        }
        push_str_list!(out, &scope.lfts, "; ", |lft| format!("(ϝ, {lft})"));

        out.push(']');

        out
    }

    fn format_args(&self) -> String {
        let mut out = String::with_capacity(100);

        push_str_list!(out, &self.args, ", ");

        out
    }

    fn uncurry_typed_binders<'a, F>(v: F) -> (coq::binder::Pattern, coq::term::Type)
    where
        F: IntoIterator<Item = &'a coq::binder::Binder>,
    {
        let mut v = v.into_iter().peekable();

        if v.peek().is_none() {
            return ("_".to_owned(), coq::term::Type::Literal("unit".to_owned()));
        }

        let mut pattern = String::with_capacity(100);
        let mut types = String::with_capacity(100);

        pattern.push('(');
        types.push('(');

        let mut need_sep = false;
        for binder in v {
            if need_sep {
                pattern.push_str(", ");
                types.push_str(" * ");
            }

            pattern.push_str(&binder.get_name());
            types.push_str(&format!("{}", binder.get_type().unwrap()));

            need_sep = true;
        }

        pattern.push(')');
        types.push(')');

        (pattern, coq::term::Type::Literal(types))
    }

    /// Write the core spec term. Assumes that the coq parameters for the type parameters (as given by
    /// `get_coq_ty_params`) are in scope.
    fn write_spec_term<F>(
        &self,
        f: &mut F,
        scope: &GenericScope<'def, LiteralTraitSpecUseRef<'def>>,
    ) -> Result<(), fmt::Error>
    where
        F: fmt::Write,
    {
        /* fn(∀ [lft_pat] : [lft_count] | | [param_pat] : [param_type]; [elctx]; [args]; [pre]; [trait_reqs])
               → ∃ [exist_pat] : [exist_type], [ret_type]; [post]
        */
        let mut f2 = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);

        // introduce generics
        write!(f2, "fn(∀ ")?;
        scope.format(&mut f2, true, true, &[], &[], &[])?;
        write!(f2, " | \n")?;

        // introduce parameters
        let param = Self::uncurry_typed_binders(self.params.iter());
        write!(f2, "(* params....... *) {} : {},\n", param.0, param.1)?;

        // elctx
        write!(f2, "(* elctx........ *) ({});\n", self.format_elctx(scope).as_str())?;

        // args
        if !self.args.is_empty() {
            write!(f2, "(* args......... *) {};\n", self.format_args().as_str())?;
        }

        // precondition
        let mut f3 = IndentWriter::new_skip_initial(BASE_INDENT, &mut f2);
        write!(f3, "(* precondition. *) (λ π : thread_id, {}) |\n", self.pre)?;

        // late precondition with trait requirements
        let mut late_pre = Vec::new();
        for trait_use in scope
            .get_surrounding_trait_requirements()
            .iter()
            .chain(scope.get_direct_trait_requirements().iter())
        {
            let trait_use = trait_use.borrow();
            let trait_use = trait_use.as_ref().unwrap();
            if !trait_use.is_used_in_self_trait {
                if let Some(spec_precond) = trait_use.make_semantic_spec_term() {
                    //let spec_precond = trait_use.make_spec_param_precond();
                    late_pre.push(IProp::Pure(spec_precond));
                }
            }
        }
        let mut f3 = IndentWriter::new_skip_initial(BASE_INDENT, &mut f2);
        write!(f3, "(* trait reqs... *) (λ π : thread_id, {})) →\n", IProp::Sep(late_pre))?;

        // existential + post
        let existential = Self::uncurry_typed_binders(&self.existentials);
        write!(
            f2,
            "(* existential.. *) ∃ {} : {}, {} @ {};\n",
            existential.0, existential.1, self.ret.1, self.ret.0
        )?;
        write!(f2, "(* postcondition *) (λ π : thread_id, {})", self.post)?;

        Ok(())
    }
}

#[derive(Debug)]
pub struct LiteralFunctionSpecBuilder<'def> {
    params: Vec<coq::binder::Binder>,
    elctx: Vec<ExtLftConstr>,
    pre: IProp,
    args: Vec<TypeWithRef<'def>>,
    existential: Vec<coq::binder::Binder>,
    ret: Option<TypeWithRef<'def>>,
    post: IProp,

    coq_names: HashSet<String>,

    /// true iff there are any annotations
    has_spec: bool,
}

impl<'def> LiteralFunctionSpecBuilder<'def> {
    #[must_use]
    pub fn new() -> Self {
        Self {
            params: Vec::new(),
            elctx: Vec::new(),
            pre: IProp::Sep(Vec::new()),
            args: Vec::new(),
            existential: Vec::new(),
            ret: None,
            post: IProp::Sep(Vec::new()),
            coq_names: HashSet::new(),
            has_spec: false,
        }
    }

    fn push_coq_name(&mut self, name: &Option<String>) {
        if let Some(name) = &name {
            self.coq_names.insert(name.to_owned());
        }
    }

    /// Adds a (universally-quantified) parameter with a given Coq name for the spec.
    pub fn add_param(&mut self, binder: coq::binder::Binder) -> Result<(), String> {
        self.ensure_coq_not_bound(binder.get_name_ref())?;
        self.push_coq_name(binder.get_name_ref());
        self.params.push(binder);
        Ok(())
    }

    /// Add a Coq type annotation for a parameter when no type is currently known.
    /// This can e.g. be used to later on add knowledge about the type of a refinement.
    pub fn add_param_type_annot(&mut self, name: &String, ty: coq::term::Type) -> Result<(), String> {
        for param in &mut self.params {
            let Some(param_name) = param.get_name_ref() else {
                continue;
            };

            if param_name == name {
                let Some(param_ty) = param.get_type() else {
                    unreachable!("Binder is typed");
                };

                if *param_ty == coq::term::Type::Infer {
                    *param = coq::binder::Binder::new(Some(name.clone()), ty);
                }
                return Ok(());
            }
        }
        Err("could not find name".to_owned())
    }

    fn ensure_coq_not_bound(&self, name: &Option<String>) -> Result<(), String> {
        if let Some(name) = &name {
            if self.coq_names.contains(name) {
                return Err(format!("Coq name is already bound: {}", name));
            }
        }

        Ok(())
    }

    /// Add a new universal lifetime constraint.
    pub fn add_lifetime_constraint(&mut self, lft1: UniversalLft, lft2: UniversalLft) {
        self.elctx.push((lft1, lft2));
    }

    /// Add a new function argument.
    pub fn add_arg(&mut self, arg: TypeWithRef<'def>) {
        self.args.push(arg);
    }

    /// Add a new (separating) conjunct to the function's precondition.
    pub fn add_precondition(&mut self, pre: IProp) {
        assert!(matches!(self.pre, IProp::Sep(_)));

        let IProp::Sep(v) = &mut self.pre else {
            unreachable!("An incorrect parameter has been given");
        };

        v.push(pre);
    }

    /// Add a new (separating) conjunct to the function's postcondition.
    pub fn add_postcondition(&mut self, post: IProp) {
        assert!(matches!(self.post, IProp::Sep(_)));

        let IProp::Sep(v) = &mut self.post else {
            unreachable!("An incorrect parameter has been given");
        };

        v.push(post);
    }

    /// Set the return type of the function
    pub fn set_ret_type(&mut self, ret: TypeWithRef<'def>) -> Result<(), String> {
        if self.ret.is_some() {
            return Err("Re-definition of return type".to_owned());
        }
        self.ret = Some(ret);
        Ok(())
    }

    /// Add an existentially-quantified variable to the postcondition.
    pub fn add_existential(&mut self, binder: coq::binder::Binder) -> Result<(), String> {
        self.ensure_coq_not_bound(binder.get_name_ref())?;
        self.existential.push(binder);
        // TODO: if we add some kind of name analysis to postcondition, we need to handle the
        // existential
        Ok(())
    }

    /// Add the information that attributes have been provided for this function.
    pub fn have_spec(&mut self) {
        self.has_spec = true;
    }

    /// Check whether a valid specification has been added.
    #[must_use]
    pub const fn has_spec(&self) -> bool {
        self.has_spec
    }

    /// Generate an actual function spec.
    pub(crate) fn into_function_spec(self) -> LiteralFunctionSpec<'def> {
        LiteralFunctionSpec {
            params: self.params,
            elctx: self.elctx,
            pre: self.pre,
            args: self.args,
            existentials: self.existential,
            ret: self.ret.unwrap_or_else(TypeWithRef::make_unit),
            post: self.post,
            has_spec: self.has_spec,
        }
    }
}

/// A specification for a particular instance of a trait
#[derive(Constructor, Clone, Debug)]
pub struct TraitInstanceSpec<'def> {
    /// a map from the identifiers to the method specs
    pub methods: BTreeMap<String, &'def FunctionSpec<'def, InnerFunctionSpec<'def>>>,
}

/// Specification attribute declaration of a trait
#[derive(Constructor, Clone, Debug)]
pub struct TraitSpecAttrsDecl {
    /// a map of attributes and their types
    attrs: BTreeMap<String, coq::term::Type>,
    semantic_interp: Option<String>,
}

/// Implementation of the attributes of a trait
#[derive(Constructor, Clone, Debug)]
pub struct TraitSpecAttrsInst {
    /// a map of attributes and their implementation
    attrs: BTreeMap<String, coq::term::Term>,
    //pub semantic_interp: Option<String>,
}

/// A using occurrence of a trait spec.
#[derive(Debug, Clone)]
pub struct LiteralTraitSpec {
    /// Name of the trait
    pub name: String,
    /// Associated types
    pub assoc_tys: Vec<String>,

    /// The name of the Coq definition for the spec param information
    pub spec_params_record: String,
    /// The name of the Coq definition for the spec attributes
    pub spec_attrs_record: String,

    /// The optional name of the Coq definition for the traits's semantic interpretation
    pub spec_semantic: Option<String>,

    /// The name of the Coq definition for the spec information
    pub spec_record: String,

    /// The basic specification annotated on the trait definition
    /// (Coq def has self, type parameters, as well as associated types)
    pub base_spec: String,
    pub base_spec_params: String,

    /// The subsumption relation between specs
    /// (Coq def has no parameters)
    pub spec_subsumption: String,

    /// declared attributes of the trait
    pub declared_attrs: HashSet<String>,

    /// maps each trait method to its canonical trait inclusion assumption definition
    pub method_trait_incl_decls: HashMap<String, String>,
}
pub type LiteralTraitSpecRef<'def> = &'def LiteralTraitSpec;

impl LiteralTraitSpec {
    /// Make the name for the method spec field of the spec record.
    #[must_use]
    pub(crate) fn make_spec_method_name(&self, method: &str) -> String {
        format!("{}_{method}_spec", self.name)
    }

    #[must_use]
    fn make_spec_attr_name(&self, attr: &str) -> String {
        format!("{}_{attr}", self.name)
    }

    #[must_use]
    fn spec_record_constructor_name(&self) -> String {
        format!("mk_{}", self.spec_record)
    }

    #[must_use]
    fn spec_record_attrs_constructor_name(&self) -> String {
        format!("mk_{}", self.spec_attrs_record)
    }

    #[must_use]
    fn spec_incl_name(&self) -> String {
        self.spec_subsumption.clone()
    }
}

/// A reference to a trait instantiated with its parameters in the verification of a function.
#[derive(Debug, Constructor, Clone)]
#[allow(clippy::partial_pub_fields)]
pub struct LiteralTraitSpecUse<'def> {
    pub trait_ref: LiteralTraitSpecRef<'def>,

    /// scope to quantify over HRTB requirements
    pub scope: TraitReqScope,

    /// the instantiation of the trait's scope
    pub trait_inst: GenericScopeInst<'def>,

    /// optionally, an override for the trait specification we assume
    overridden_spec_def: Option<String>,

    /// the name including the generic args
    mangled_base: String,

    /// whether this is a usage in the scope of a trait decl of the same trait
    pub is_used_in_self_trait: bool,

    /// optional constraints for each associated type
    assoc_ty_constraints: HashMap<String, Type<'def>>,

    /// origin of this trait assumption
    origin: TyParamOrigin,
}

/// As trait uses may reference other trait uses, we put them below optional `RefCell`s,
/// in order to allow cycles during construction.
pub type LiteralTraitSpecUseCell<'def> = RefCell<Option<LiteralTraitSpecUse<'def>>>;
pub type LiteralTraitSpecUseRef<'def> = &'def LiteralTraitSpecUseCell<'def>;

impl<'def> TraitReqInfo for LiteralTraitSpecUseRef<'def> {
    /// Get the associated types we need to quantify over.
    #[must_use]
    fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam> {
        let mut assoc_tys = Vec::new();
        let b = self.borrow();
        let b = b.as_ref().unwrap();

        for x in &b.trait_ref.assoc_tys {
            if b.assoc_ty_constraints.get(x).is_none() {
                assoc_tys.push(b.make_assoc_type_lit(x));
            }
        }
        assoc_tys
    }

    #[must_use]
    fn get_origin(&self) -> TyParamOrigin {
        let b = self.borrow();
        let b = b.as_ref().unwrap();
        b.origin
    }
}

impl<'def> LiteralTraitSpecUse<'def> {
    /// Get the name for a spec parameter for this trait instance.
    #[must_use]
    fn make_spec_param_name(&self) -> String {
        format!("{}_spec", self.mangled_base)
    }

    /// Get the name for a spec attrs parameter for this trait instance.
    #[must_use]
    fn make_spec_attrs_param_name(&self) -> String {
        format!("{}_spec_attrs", self.mangled_base)
    }

    /// Get the term for accessing a particular attribute in a context where the attribute record
    /// is quantified.
    #[must_use]
    pub fn make_attr_item_term(&self, attr_name: &str) -> coq::term::Term {
        coq::term::Term::RecordProj(
            Box::new(coq::term::Term::Literal(self.make_spec_attrs_param_name())),
            self.trait_ref.make_spec_attr_name(attr_name),
        )
    }

    /// Get the instantiation of associated types.
    #[must_use]
    fn get_assoc_ty_inst(&self) -> Vec<Type<'def>> {
        let mut assoc_tys = Vec::new();
        for x in &self.trait_ref.assoc_tys {
            let ty = self.make_assoc_type_use(x);
            assoc_tys.push(ty.clone());
        }
        assoc_tys
    }

    /// Get the instantiation of the trait spec's parameters, in the same order as
    /// `get_ordered_params`.
    #[must_use]
    fn get_ordered_params_inst(&self) -> Vec<Type<'def>> {
        let mut params = self.trait_inst.get_direct_ty_params().to_vec();
        params.append(&mut self.get_assoc_ty_inst());
        params.append(&mut self.trait_inst.get_direct_assoc_ty_params());

        params
    }

    /// Get the binder for the attribute parameter.
    #[must_use]
    fn get_attr_param(&self) -> coq::binder::Binder {
        let ordered_params = self.get_ordered_params_inst();
        let all_args: Vec<_> = ordered_params.iter().map(Type::get_rfn_type).collect();

        let mut attr_param_ty = format!("{} (RRGS:=RRGS) ", self.trait_ref.spec_attrs_record);
        push_str_list!(attr_param_ty, &all_args, " ");

        // add the attributes
        coq::binder::Binder::new(
            Some(self.make_spec_attrs_param_name()),
            coq::term::Type::Literal(attr_param_ty),
        )
    }

    /// Get the binder for the spec record parameter.
    #[must_use]
    fn get_spec_param(&self) -> coq::binder::Binder {
        let ordered_params = self.get_ordered_params_inst();
        let all_args: Vec<_> = ordered_params.iter().map(Type::get_rfn_type).collect();

        let mut spec_param_ty = format!(
            "spec_with {} [] ({} (RRGS:=RRGS) ",
            self.scope.quantified_lfts.len(),
            self.trait_ref.spec_record
        );
        push_str_list!(spec_param_ty, &all_args, " ");
        spec_param_ty.push(')');

        coq::binder::Binder::new(Some(self.make_spec_param_name()), coq::term::Type::Literal(spec_param_ty))
    }

    /// Get the optional specialized semantic term for this trait assumption.
    #[must_use]
    pub fn make_semantic_spec_term(&self) -> Option<String> {
        if let Some(semantic_def) = &self.trait_ref.spec_semantic {
            let inst = &self.trait_inst;
            let args = inst.get_all_ty_params_with_assocs();

            let mut specialized_semantic = format!("{} ", semantic_def.to_owned());
            push_str_list!(specialized_semantic, &args, " ", |x| { format!("{}", x.get_rfn_type()) });
            specialized_semantic.push(' ');
            push_str_list!(specialized_semantic, &args, " ", |x| { x.to_string() });
            Some(specialized_semantic)
        } else {
            None
        }
    }

    /// Make the precondition on the spec parameter we need to require.
    #[must_use]
    fn make_spec_param_precond(&self) -> coq::term::Term {
        // the spec we have to require for this verification
        let (spec_to_require, need_attrs) = if let Some(override_spec) = &self.overridden_spec_def {
            (override_spec.to_string(), false)
        } else {
            (self.trait_ref.base_spec.clone(), true)
        };

        let all_args = self.get_ordered_params_inst();

        let mut specialized_spec = String::new();
        specialized_spec.push_str(&format!("({} {} ", self.scope, spec_to_require));
        // specialize to rts
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", x.get_rfn_type()) });
        // specialize to sts
        specialized_spec.push(' ');
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", SynType::from(x)) });

        // specialize to further args
        if need_attrs {
            specialized_spec.push_str(&format!(" {}", self.make_spec_attrs_param_name()));
        }
        for req in self.trait_inst.get_direct_trait_requirements() {
            // get attrs + spec term
            specialized_spec.push_str(&format!(" {}", req.get_attr_term()));
            //specialized_spec.push_str(&format!(" {}", req.get_spec_term()));
        }

        // specialize to semtys
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("<TY> {}", x) });
        // specialize to lfts
        push_str_list!(specialized_spec, self.trait_inst.get_lfts(), " ", |x| { format!("<LFT> {}", x) });
        specialized_spec.push_str(" <INST!>)");

        let spec = format!(
            "trait_incl_marker (lift_trait_incl {} {} {specialized_spec})",
            self.trait_ref.spec_subsumption,
            self.make_spec_param_name(),
        );

        coq::term::Term::Literal(spec)
    }

    /// Make the name for the location parameter of a use of a method of this trait parameter.
    #[must_use]
    pub fn make_loc_name(&self, mangled_method_name: &str) -> String {
        format!("{}_{}_loc", self.mangled_base, mangled_method_name)
    }

    /// Make the names for the Coq-level parameters for an associated type of this instance.
    /// Warning: If you are making a using occurrence, use `make_assoc_type_use` instead.
    #[must_use]
    fn make_assoc_type_lit(&self, assoc_type: &str) -> LiteralTyParam {
        let rust_name = if self.is_used_in_self_trait {
            assoc_type.to_owned()
        } else {
            format!("{}_{}", self.mangled_base, assoc_type)
        };
        LiteralTyParam::new_with_origin(&rust_name, &rust_name, self.origin)
    }

    /// Add a constraint on one of the associated types.
    pub fn specialize_assoc_type(&mut self, assoc_type: String, ty: Type<'def>) {
        self.assoc_ty_constraints.insert(assoc_type, ty);
    }

    /// Make a using occurrence of a particular associated type.
    #[must_use]
    pub fn make_assoc_type_use(&self, assoc_type: &str) -> Type<'def> {
        if let Some(cstr) = self.assoc_ty_constraints.get(assoc_type) {
            cstr.to_owned()
        } else {
            Type::LiteralParam(self.make_assoc_type_lit(assoc_type))
        }
    }
}

/// A scope of quantifiers for HRTBs on trait requirements.
#[derive(Debug, Constructor, Clone)]
pub struct TraitReqScope {
    pub quantified_lfts: Vec<Lft>,
}

impl TraitReqScope {
    #[must_use]
    pub fn identity_instantiation(&self) -> TraitReqScopeInst {
        TraitReqScopeInst::new(self.quantified_lfts.clone())
    }
}

impl<'def, T: TraitReqInfo> From<TraitReqScope> for GenericScope<'def, T> {
    fn from(scope: TraitReqScope) -> Self {
        let mut generic_scope: GenericScope<'_, T> = GenericScope::empty();
        for lft in scope.quantified_lfts {
            generic_scope.add_lft_param(lft);
        }
        generic_scope
    }
}
impl Display for TraitReqScope {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // just a special case of `GenericScope`
        let scope: GenericScope<'_, LiteralTraitSpecUseRef<'_>> = self.clone().into();
        write!(f, "{scope}")
    }
}

/// An instantiation for a `TraitReqScope`.
#[derive(Debug, Constructor, Clone)]
pub struct TraitReqScopeInst {
    pub lft_insts: Vec<Lft>,
}

impl Display for TraitReqScopeInst {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write_list!(f, &self.lft_insts, "", |x| format!(" <LFT> {x}"))
    }
}

#[derive(Debug, Constructor, Clone)]
pub struct SpecializedTraitImpl<'def> {
    impl_ref: LiteralTraitImplRef<'def>,
    impl_inst: GenericScopeInst<'def>,
}

impl<'def> SpecializedTraitImpl<'def> {
    #[must_use]
    fn get_spec_term(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{} ", self.impl_ref.spec_record));

        // specialize to rts
        push_str_list!(out, self.impl_inst.get_direct_ty_params(), " ", |x| {
            format!("{}", x.get_rfn_type())
        });
        // specialize to sts
        out.push(' ');
        push_str_list!(out, self.impl_inst.get_direct_ty_params(), " ", |x| {
            format!("{}", SynType::from(x))
        });

        // add trait requirements
        for req in self.impl_inst.get_direct_trait_requirements() {
            // get attrs
            out.push_str(&format!(" {}", req.get_attr_term()));
        }

        // specialize to semtys
        push_str_list!(out, self.impl_inst.get_direct_ty_params(), " ", |x| { format!("<TY> {}", x) });
        // specialize to lfts
        push_str_list!(out, self.impl_inst.get_lfts(), " ", |x| { format!("<LFT> {}", x) });
        out.push_str(" <INST!>");

        out
    }
}

#[derive(Debug, Constructor, Clone)]
pub struct QuantifiedTraitImpl<'def> {
    pub(crate) trait_ref: LiteralTraitSpecUseRef<'def>,

    /// instantiation of the HRTB requirements this trait use is generic over
    scope_inst: TraitReqScopeInst,
}

impl<'def> QuantifiedTraitImpl<'def> {
    #[must_use]
    pub(crate) fn get_spec_term(&self) -> String {
        let mut out = String::new();
        let spec = self.trait_ref.borrow();
        let spec = spec.as_ref().unwrap();
        out.push_str(&spec.make_spec_param_name());
        // instantiate
        out.push_str(&self.scope_inst.to_string());
        out.push_str(" <INST!>");

        out
    }
}

#[derive(Debug, Clone)]
pub enum TraitReqInstSpec<'def> {
    /// A specialized trait impl (i.e., an instantiated declaration)
    Specialized(SpecializedTraitImpl<'def>),
    /// A quantified trait impl (i.e., introduced by a `where` clause)
    Quantified(QuantifiedTraitImpl<'def>),
}

/// Instantiation of a trait requirement.
/// The representation of the associated type instantiation is generic.
#[derive(Debug, Constructor, Clone)]
pub struct TraitReqInst<'def, T> {
    pub spec: TraitReqInstSpec<'def>,
    pub origin: TyParamOrigin,
    pub assoc_ty_inst: Vec<T>,

    pub of_trait: LiteralTraitSpecRef<'def>,

    /// The scope to quantify over for this instantiation.
    /// This is non-empty if the trait requirement we are fulfilling is higher-ranked,
    /// i.e., it quantifies over some lifetimes (`for<'a> ...`), HRTBs.
    pub scope: TraitReqScope,
    // remaining quantified associated types
    //quantified_assoc_tys: Vec<LiteralTyParam>,
}

impl<'def, T> TraitReqInst<'def, T> {
    #[must_use]
    const fn get_origin(&self) -> TyParamOrigin {
        self.origin
    }

    #[must_use]
    fn get_assoc_ty_inst(&self) -> &[T] {
        &self.assoc_ty_inst
    }

    #[must_use]
    pub(crate) fn get_spec_term(&self) -> String {
        let mut out = String::new();
        out.push('(');
        out.push_str(&self.scope.to_string());
        out.push(' ');
        match &self.spec {
            TraitReqInstSpec::Specialized(s) => {
                out.push_str(&s.get_spec_term());
            },
            TraitReqInstSpec::Quantified(s) => {
                out.push_str(&s.get_spec_term());
            },
        }
        out.push(')');
        out
    }

    #[must_use]
    pub(crate) fn get_attr_term(&self) -> String {
        match &self.spec {
            TraitReqInstSpec::Specialized(s) => {
                // instantiate the attrs suitably
                let mut args = Vec::new();
                for ty in s.impl_inst.get_direct_ty_params_with_assocs() {
                    args.push(format!("{}", ty.get_rfn_type()));
                }
                // get the attr terms this depends on
                for req in s.impl_inst.get_direct_trait_requirements() {
                    args.push(req.get_attr_term());
                }

                let attr_term =
                    format!("{}", coq::term::App::new(s.impl_ref.spec_attrs_record.clone(), args));
                attr_term
            },
            TraitReqInstSpec::Quantified(s) => {
                let s = s.trait_ref.borrow();
                let s = s.as_ref().unwrap();
                s.make_spec_attrs_param_name()
            },
        }
    }
}

pub trait TraitReqInfo {
    fn get_assoc_ty_params(&self) -> Vec<LiteralTyParam>;
    fn get_origin(&self) -> TyParamOrigin;
}

#[derive(Clone, Constructor, Debug)]
pub(crate) struct TyParamList {
    pub(crate) params: Vec<LiteralTyParam>,
}

impl TyParamList {
    #[must_use]
    const fn empty() -> Self {
        Self { params: vec![] }
    }

    fn append(&mut self, mut other: Vec<LiteralTyParam>) {
        self.params.append(&mut other);
    }

    fn merge(&mut self, other: Self) {
        self.append(other.params);
    }

    /// Get the Coq parameters that need to be in scope for the type parameters of this function.
    #[must_use]
    pub(crate) fn get_coq_ty_st_params(&self) -> coq::binder::BinderList {
        let mut ty_coq_params = Vec::new();
        for names in &self.params {
            ty_coq_params.push(names.make_syntype_param());
        }
        coq::binder::BinderList::new(ty_coq_params)
    }

    #[must_use]
    fn get_coq_ty_rt_params(&self) -> coq::binder::BinderList {
        let mut ty_coq_params = Vec::new();
        for names in &self.params {
            ty_coq_params.push(names.make_refinement_param());
        }
        coq::binder::BinderList::new(ty_coq_params)
    }

    #[must_use]
    fn get_coq_ty_params(&self) -> coq::binder::BinderList {
        let mut rt_params = self.get_coq_ty_rt_params();
        let st_params = self.get_coq_ty_st_params();
        rt_params.append(st_params.0);
        rt_params
    }

    #[must_use]
    fn get_semantic_ty_params(&self) -> coq::binder::BinderList {
        let mut ty_coq_params = Vec::new();
        for names in &self.params {
            ty_coq_params.push(names.make_semantic_param());
        }
        coq::binder::BinderList::new(ty_coq_params)
    }
}

/// An instantiation of a scope of generics `GenericScope`.
#[derive(Clone, Debug)]
pub struct GenericScopeInst<'def> {
    direct_tys: Vec<Type<'def>>,
    surrounding_tys: Vec<Type<'def>>,

    direct_trait_requirements: Vec<TraitReqInst<'def, Type<'def>>>,
    surrounding_trait_requirements: Vec<TraitReqInst<'def, Type<'def>>>,

    // TODO maybe also separate into direct and surrounding?
    lfts: Vec<Lft>,
}

impl<'def> GenericScopeInst<'def> {
    #[must_use]
    pub fn empty() -> Self {
        Self {
            direct_tys: Vec::new(),
            surrounding_tys: Vec::new(),
            direct_trait_requirements: Vec::new(),
            surrounding_trait_requirements: Vec::new(),
            lfts: Vec::new(),
        }
    }

    pub fn add_direct_ty_param(&mut self, ty: Type<'def>) {
        self.direct_tys.push(ty);
    }

    pub fn add_surrounding_ty_param(&mut self, ty: Type<'def>) {
        self.surrounding_tys.push(ty);
    }

    pub fn add_lft_param(&mut self, lft: Lft) {
        self.lfts.push(lft);
    }

    /// Add a trait requirement.
    pub fn add_trait_requirement(&mut self, req: TraitReqInst<'def, Type<'def>>) {
        if req.get_origin() == TyParamOrigin::Direct {
            self.direct_trait_requirements.push(req);
        } else {
            self.surrounding_trait_requirements.push(req);
        }
    }

    #[must_use]
    fn get_surrounding_ty_params(&self) -> &[Type<'def>] {
        &self.surrounding_tys
    }

    #[must_use]
    pub fn get_direct_ty_params(&self) -> &[Type<'def>] {
        &self.direct_tys
    }

    #[must_use]
    fn get_direct_assoc_ty_params(&self) -> Vec<Type<'def>> {
        let ty_params: Vec<_> =
            self.direct_trait_requirements.iter().map(|x| x.get_assoc_ty_inst().to_vec()).concat();
        ty_params
    }

    #[must_use]
    fn get_surrounding_assoc_ty_params(&self) -> Vec<Type<'def>> {
        let ty_params: Vec<_> = self
            .surrounding_trait_requirements
            .iter()
            .map(|x| x.get_assoc_ty_inst().to_vec())
            .concat();
        ty_params
    }

    #[must_use]
    fn get_direct_ty_params_with_assocs(&self) -> Vec<Type<'def>> {
        let mut direct = self.get_direct_ty_params().to_vec();
        direct.append(&mut self.get_direct_assoc_ty_params());
        direct
    }

    #[must_use]
    fn get_surrounding_ty_params_with_assocs(&self) -> Vec<Type<'def>> {
        let mut surrounding = self.get_surrounding_ty_params().to_vec();
        surrounding.append(&mut self.get_surrounding_assoc_ty_params());
        surrounding
    }

    #[must_use]
    pub fn get_all_ty_params_with_assocs(&self) -> Vec<Type<'def>> {
        let mut params = self.get_surrounding_ty_params_with_assocs();
        let mut direct = self.get_direct_ty_params_with_assocs();
        params.append(&mut direct);
        trace!("all params: {params:?}");
        params
    }

    /// Generate an instantiation of a term with the identity
    #[must_use]
    pub(crate) fn instantiation(&self) -> String {
        let mut out = String::new();

        for ty in self.get_all_ty_params_with_assocs() {
            out.push_str(&format!(" <TY> {}", ty));
        }
        for lft in self.get_lfts() {
            out.push_str(&format!(" <LFT> {}", lft));
        }
        out.push_str(" <INST!>");

        out
    }

    #[must_use]
    fn get_lfts(&self) -> &[Lft] {
        &self.lfts
    }

    #[must_use]
    pub(crate) fn get_direct_trait_requirements(&self) -> &[TraitReqInst<'def, Type<'def>>] {
        &self.direct_trait_requirements
    }

    #[must_use]
    pub(crate) fn get_surrounding_trait_requirements(&self) -> &[TraitReqInst<'def, Type<'def>>] {
        &self.surrounding_trait_requirements
    }
}

/// A scope of generics.
#[derive(Clone, Debug)]
pub struct GenericScope<'def, T = LiteralTraitSpecUseRef<'def>> {
    /// generics quantified on this object.
    direct_tys: TyParamList,
    /// generics quantified by a surrounding scope.
    surrounding_tys: TyParamList,

    /// trait requirements quantified on this object.
    direct_trait_requirements: Vec<T>,
    /// trait requirements quantified by a surrounding scope.
    surrounding_trait_requirements: Vec<T>,

    /// TODO: also separate into direct and surrounding?
    lfts: Vec<Lft>,

    _phantom: PhantomData<&'def ()>,
}

impl<'def, T: TraitReqInfo> GenericScope<'def, T> {
    /// Create an empty scope.
    #[must_use]
    pub fn empty() -> Self {
        Self {
            direct_tys: TyParamList::empty(),
            surrounding_tys: TyParamList::empty(),
            direct_trait_requirements: Vec::new(),
            surrounding_trait_requirements: Vec::new(),
            lfts: Vec::new(),
            _phantom: PhantomData {},
        }
    }

    /// Get the validity term for a generic on a function.
    #[must_use]
    pub(crate) fn generate_validity_term_for_generics(&self) -> IProp {
        let mut props = Vec::new();
        for ty in self.get_all_ty_params_with_assocs().params {
            props.push(Self::generate_validity_term_for_typaram(&ty));
        }
        IProp::Sep(props)
    }

    #[must_use]
    fn generate_validity_term_for_typaram(ty: &LiteralTyParam) -> IProp {
        let prop = format!("typaram_wf {} {} {}", ty.refinement_type, ty.syn_type, ty.type_term);
        IProp::Atom(prop)
    }

    // TODO hack
    pub fn clear_lfts(&mut self) {
        self.lfts = Vec::new();
    }

    /// Get type parameters quantified by a surrounding scope.
    #[must_use]
    const fn get_surrounding_ty_params(&self) -> &TyParamList {
        &self.surrounding_tys
    }

    /// Get type parameters quantified on this object.
    #[must_use]
    const fn get_direct_ty_params(&self) -> &TyParamList {
        &self.direct_tys
    }

    /// Get associated type parameters of trait requirements on this object.
    #[must_use]
    fn get_direct_assoc_ty_params(&self) -> TyParamList {
        let ty_params: Vec<_> =
            self.direct_trait_requirements.iter().map(TraitReqInfo::get_assoc_ty_params).concat();
        TyParamList::new(ty_params)
    }

    /// Get associated type parameters of trait requirements quantified by a surrounding scope.
    #[must_use]
    fn get_surrounding_assoc_ty_params(&self) -> TyParamList {
        let ty_params: Vec<_> =
            self.surrounding_trait_requirements.iter().map(TraitReqInfo::get_assoc_ty_params).concat();
        TyParamList::new(ty_params)
    }

    /// Get direct type parameters and associated type parameters.
    #[must_use]
    fn get_direct_ty_params_with_assocs(&self) -> TyParamList {
        let mut direct = self.get_direct_ty_params().clone();
        direct.merge(self.get_direct_assoc_ty_params());
        direct
    }

    /// Get type parameters and associated type parameters quantified by a surrounding scope.
    #[must_use]
    fn get_surrounding_ty_params_with_assocs(&self) -> TyParamList {
        let mut surrounding = self.get_surrounding_ty_params().clone();
        surrounding.merge(self.get_surrounding_assoc_ty_params());
        surrounding
    }

    /// Get all type parameters and associated type parameters.
    #[must_use]
    pub(crate) fn get_all_ty_params_with_assocs(&self) -> TyParamList {
        let mut params = self.get_surrounding_ty_params_with_assocs();
        let direct = self.get_direct_ty_params_with_assocs();
        params.merge(direct);
        trace!("all params: {params:?}");
        params
    }

    /// Generate an instantiation of a term with the identity
    #[must_use]
    pub(crate) fn identity_instantiation(&self) -> String {
        let mut out = String::new();

        for ty in self.get_all_ty_params_with_assocs().params {
            out.push_str(&format!(" <TY> {}", ty.type_term));
        }
        for lft in self.get_lfts() {
            out.push_str(&format!(" <LFT> {}", lft));
        }
        out.push_str(" <INST!>");

        out
    }

    #[must_use]
    fn get_spec_all_type_term(&self, spec: Box<coq::term::Type>) -> coq::term::Type {
        let params = self.get_all_ty_params_with_assocs();

        coq::term::Type::UserDefined(model::Type::SpecWith(
            self.get_num_lifetimes(),
            // TODO: `LiteralTyParam` should take `Type` instead of `String`
            params
                .params
                .iter()
                .map(|x| coq::term::Type::Literal(x.refinement_type.clone()))
                .collect(),
            spec,
        ))
    }

    #[must_use]
    #[deprecated(note = "Use `get_spec_all_type_term` instead")]
    fn get_all_type_term(&self) -> String {
        let mut out = String::new();

        out.push_str(&format!("spec_with {} [", self.get_num_lifetimes()));
        let tys = self.get_all_ty_params_with_assocs();
        push_str_list!(out, &tys.params, "; ", |x| x.refinement_type.clone());
        out.push(']');

        out
    }

    #[must_use]
    pub(crate) fn get_lfts(&self) -> &[Lft] {
        &self.lfts
    }

    /// Get trait requirements declared on the object.
    #[must_use]
    fn get_direct_trait_requirements(&self) -> &[T] {
        &self.direct_trait_requirements
    }

    /// Get trait requirements surrounding the object.
    #[must_use]
    fn get_surrounding_trait_requirements(&self) -> &[T] {
        &self.surrounding_trait_requirements
    }

    pub fn add_ty_param(&mut self, ty: LiteralTyParam) {
        if ty.origin == TyParamOrigin::Direct {
            self.direct_tys.params.push(ty);
        } else {
            self.surrounding_tys.params.push(ty);
        }
    }

    pub fn add_lft_param(&mut self, lft: Lft) {
        self.lfts.push(lft);
    }

    /// Add a trait requirement.
    pub fn add_trait_requirement(&mut self, req: T) {
        if req.get_origin() == TyParamOrigin::Direct {
            self.direct_trait_requirements.push(req);
        } else {
            self.surrounding_trait_requirements.push(req);
        }
    }

    #[must_use]
    pub(crate) fn get_num_lifetimes(&self) -> usize {
        self.lfts.len()
    }

    /// Format this generic scope.
    pub(crate) fn format<F>(
        &self,
        f: &mut F,
        only_core: bool,
        as_fn: bool,
        surrounding_extra_tys: &[LiteralTyParam],
        direct_extra_tys: &[LiteralTyParam],
        extra_lfts: &[Lft],
    ) -> fmt::Result
    where
        F: fmt::Write,
    {
        let mut lft_pattern = String::with_capacity(100);
        write!(lft_pattern, "( *[")?;
        write_list!(lft_pattern, self.lfts.iter().chain(extra_lfts), "; ", String::to_string)?;
        write!(lft_pattern, "])")?;

        let mut all_params = self.get_surrounding_ty_params().clone();
        all_params.append(surrounding_extra_tys.to_vec());
        all_params.merge(self.get_surrounding_assoc_ty_params());
        all_params.merge(self.get_direct_ty_params().clone());
        all_params.append(direct_extra_tys.to_vec());
        all_params.merge(self.get_direct_assoc_ty_params());

        let mut typarams_pattern = String::with_capacity(100);

        write!(typarams_pattern, "( *[")?;
        write_list!(typarams_pattern, &all_params.params, "; ", |x| x.type_term.clone())?;
        write!(typarams_pattern, "])")?;

        let mut typarams_ty_list = String::with_capacity(100);
        write!(typarams_ty_list, "[")?;
        write_list!(typarams_ty_list, &all_params.params, "; ", |x| {
            if as_fn { format!("({}, {})", x.refinement_type, x.syn_type) } else { x.refinement_type.clone() }
        })?;
        write!(typarams_ty_list, "]")?;

        if only_core {
            write!(
                f,
                "{lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list (Type * syn_type)%type)",
                self.lfts.len() + extra_lfts.len()
            )
        } else if as_fn {
            write!(
                f,
                "fnspec! {lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list Type),",
                self.lfts.len() + extra_lfts.len()
            )
        } else {
            write!(
                f,
                "spec! {lft_pattern} : {} | {typarams_pattern} : ({typarams_ty_list} : list Type),",
                self.lfts.len() + extra_lfts.len()
            )
        }
    }
}

impl<'def, T: TraitReqInfo + Clone> GenericScope<'def, T> {
    pub fn append(&mut self, other: &Self) {
        self.direct_tys.merge(other.direct_tys.clone());
        self.surrounding_tys.merge(other.surrounding_tys.clone());
        for lft in &other.lfts {
            self.lfts.push(lft.to_owned());
        }
        self.direct_trait_requirements.extend(other.direct_trait_requirements.iter().cloned());
        self.surrounding_trait_requirements
            .extend(other.surrounding_trait_requirements.iter().cloned());
    }
}

impl<'def, T: TraitReqInfo> Display for GenericScope<'def, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.format(f, false, false, &[], &[], &[])
    }
}

impl<'def> GenericScope<'def, LiteralTraitSpecUseRef<'def>> {
    #[must_use]
    fn get_direct_attr_trait_parameters(&self, include_self: bool) -> coq::binder::BinderList {
        self.get_trait_req_parameters(false, true, include_self, false)
    }

    #[must_use]
    fn get_surrounding_trait_parameters(&self, include_self: bool) -> coq::binder::BinderList {
        self.get_trait_req_parameters(true, false, include_self, true)
    }

    #[must_use]
    fn get_surrounding_attr_trait_parameters(&self, include_self: bool) -> coq::binder::BinderList {
        self.get_trait_req_parameters(true, false, include_self, false)
    }

    #[must_use]
    fn get_all_trait_parameters(&self, include_self: bool) -> coq::binder::BinderList {
        self.get_trait_req_parameters(true, true, include_self, true)
    }

    #[must_use]
    fn get_all_attr_trait_parameters(&self, include_self: bool) -> coq::binder::BinderList {
        self.get_trait_req_parameters(true, true, include_self, false)
    }

    #[allow(clippy::fn_params_excessive_bools)]
    fn get_trait_req_parameters(
        &self,
        include_surrounding: bool,
        include_direct: bool,
        include_self: bool,
        include_spec: bool,
    ) -> coq::binder::BinderList {
        let mut params = Vec::new();

        // add trait reqs
        let trait_reqs =
            if include_surrounding { self.get_surrounding_trait_requirements().iter() } else { [].iter() };
        let trait_reqs = if include_direct {
            trait_reqs.chain(self.get_direct_trait_requirements().iter())
        } else {
            trait_reqs.chain(&[])
        };
        for trait_use in trait_reqs {
            let trait_use = trait_use.borrow();
            let trait_use = trait_use.as_ref().unwrap();

            if !trait_use.is_used_in_self_trait || include_self {
                params.push(trait_use.get_attr_param());
            }

            // if we're not in the same trait declaration, add the spec
            if include_spec && !trait_use.is_used_in_self_trait {
                params.push(trait_use.get_spec_param());
            }
        }

        coq::binder::BinderList::new(params)
    }
}

/// Generate the record instances for a trait impl.
/// - `scope` quantifies the generics of this instance
/// - `assoc_types` has the associated types of this trait that we quantify over in the spec record decl (for
///   the declaration of the base instance)
/// - `params_inst` is the instantiation of the trait's type parameters, including its associated types and
///   its dependencies
/// - `spec` is the specification of all the functions
/// - `of_trait` gives the trait of which we make an instance
/// - `is_base_spec` should be true if this is the base instance of the trait
/// - `spec_record_name` is the name of the record decl
fn make_trait_instance<'def>(
    scope: &GenericScope<'def, LiteralTraitSpecUseRef<'def>>,
    assoc_types: &[LiteralTyParam],
    param_inst: &[Type<'def>],
    spec: &TraitInstanceSpec<'def>,
    of_trait: LiteralTraitSpecRef<'def>,
    is_base_spec: bool,
    spec_record_name: &str,
) -> Result<coq::Document, fmt::Error> {
    let mut document = coq::Document::default();

    // there should be no surrounding params, as this is the scope of a top-level `impl`
    assert!(scope.surrounding_tys.params.is_empty());
    assert!(scope.surrounding_trait_requirements.is_empty());

    let ty_params = scope.get_direct_ty_params();
    let assoc_params = scope.get_direct_assoc_ty_params();

    // Get all parameters
    // The assoc_types for the Self trait should come before other associated types
    let mut def_params = Vec::new();
    // all rts
    for param in ty_params.params.iter().chain(assoc_types).chain(assoc_params.params.iter()) {
        let rt_param = coq::binder::Binder::new(Some(param.refinement_type.clone()), coq::term::Type::Type);
        def_params.push(rt_param);
    }
    // all sts
    for param in ty_params.params.iter().chain(assoc_types).chain(assoc_params.params.iter()) {
        let rt_param = coq::binder::Binder::new(Some(param.syn_type.clone()), model::Type::SynType);
        def_params.push(rt_param);
    }

    let param_inst_rts: Vec<_> = param_inst.iter().map(Type::get_rfn_type).collect();

    // for the base spec, we quantify over the attrs
    // Otherwise, we do not have to quantify over the attrs, as we fix one particular attrs record
    // for concrete impls.
    // TODO: should this come before the other params maybe?
    if is_base_spec {
        // assemble the type
        // TODO: for trait deps, also instantiate with deps?
        let attrs_type = coq::term::App::new(of_trait.spec_attrs_record.clone(), param_inst_rts.clone());
        let attrs_type = coq::term::Type::Literal(format!("{attrs_type}"));
        def_params.push(coq::binder::Binder::new(Some("_ATTRS".to_owned()), attrs_type));
    }

    // also quantify over all trait deps
    let mut trait_params = scope.get_all_attr_trait_parameters(false);
    def_params.append(&mut trait_params.0);

    let def_params = coq::binder::BinderList::new(def_params);

    // for this, we assume that the semantic type parameters are all in scope
    let body_term = if spec.methods.is_empty() {
        // special-case this, as we cannot use record constructor syntax for empty records
        // implicitly inst rrgs
        let t = coq::term::App::new(
            format!("@{} _ _", of_trait.spec_record_constructor_name()),
            param_inst_rts.clone(),
        );
        coq::term::Term::Literal(t.to_string())
    } else {
        let mut components = Vec::new();

        // order doesn't matter for Coq records
        for (item_name, spec) in &spec.methods {
            let record_item_name = of_trait.make_spec_method_name(item_name);

            // get the param uses for rt + st for all params, including the params of the impl/trait
            let params = spec.generics.get_all_ty_params_with_assocs().get_coq_ty_params();
            let param_uses = params.make_using_terms();

            let mut body = String::with_capacity(100);

            // first instantiate with all rt + st
            write!(body, "{} {param_uses}", spec.spec_name)?;

            // then the attrs, if we have the base spec
            // This comes before other trait requirement's attrs, as the Self requirement is always
            // shuffled first
            if is_base_spec {
                write!(body, " _ATTRS")?;
            }

            // instantiate with all trait specs
            let trait_params = spec.generics.get_all_attr_trait_parameters(false).make_using_terms();
            write!(body, " {trait_params}")?;

            write!(body, "\n")?;

            // instantiate with the scope's types
            for x in &scope.get_direct_ty_params().params {
                write!(body, " <TY> {}", x.type_term)?;
            }
            for x in &scope.lfts {
                write!(body, " <LFT> {x}")?;
            }
            // instantiate with associated types of the trait instance
            // The associated types of this trait alway come first.
            for x in assoc_types {
                write!(body, " <TY> {}", x.type_term)?;
            }
            // instantiate with the scope's associated types
            for x in scope.get_direct_assoc_ty_params().params {
                write!(body, " <TY> {}", x.type_term)?;
            }
            // we leave the direct type parameters and associated types of the function uninstantiated

            // provide type annotation
            let num_lifetimes = spec.generics.get_num_lifetimes() - scope.lfts.len();
            write!(body, " : (spec_with {num_lifetimes} [")?;
            let direct_tys = spec.generics.get_direct_ty_params_with_assocs();
            write_list!(body, &direct_tys.params, "; ", |x| x.refinement_type.clone())?;

            write!(body, "] fn_spec)")?;

            // get the direct parameters (rt + st) of this function.
            // We quantify over these at the record item level.
            let mut direct_params = spec.generics.get_direct_ty_params_with_assocs().get_coq_ty_params();
            // also quantify over direct trait requirements
            let direct_trait_params = spec.generics.get_direct_attr_trait_parameters(false);
            direct_params.append(direct_trait_params.0);

            let item = coq::term::RecordBodyItem {
                name: record_item_name,
                params: direct_params,
                term: coq::term::Term::Literal(body),
            };
            components.push(item);
        }
        let record_body = coq::term::RecordBody { items: components };
        coq::term::Term::RecordBody(record_body)
    };
    // add the surrounding quantifiers over the semantic types
    let mut term_with_specs = String::with_capacity(100);
    scope.format(&mut term_with_specs, false, false, &[], assoc_types, &[])?;
    write!(term_with_specs, " {body_term}")?;

    let mut ty_annot = String::with_capacity(100);
    let spec_record_type = coq::term::App::new(of_trait.spec_record.clone(), param_inst_rts);
    write!(ty_annot, "spec_with _ _ {}", spec_record_type)?;

    document.push(coq::command::Definition {
        name: spec_record_name.to_owned(),
        params: def_params,
        ty: Some(coq::term::Type::Literal(ty_annot)),
        body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(term_with_specs)),
    });

    Ok(document)
}

/// When translating a trait declaration, we should generate this, bundling all the components of
/// the trait together.
#[derive(Constructor, Clone, Debug)]
#[allow(clippy::partial_pub_fields)]
pub struct TraitSpecDecl<'def> {
    /// A reference to all the Coq definition names we should generate.
    pub lit: LiteralTraitSpecRef<'def>,

    /// The generics this trait uses
    generics: GenericScope<'def, LiteralTraitSpecUseRef<'def>>,

    /// associated types
    assoc_types: Vec<LiteralTyParam>,

    /// The default specification from the trait declaration
    default_spec: TraitInstanceSpec<'def>,

    /// the spec attributes
    attrs: TraitSpecAttrsDecl,
}

impl<'def> TraitSpecDecl<'def> {
    // Get the ordered parameters that definitions of the trait are parametric over
    fn get_ordered_params(&self) -> TyParamList {
        let mut params = self.generics.get_direct_ty_params().to_owned();
        params.append(self.assoc_types.clone());
        params.append(self.generics.get_direct_assoc_ty_params().params);
        params
    }

    fn make_attr_record_decl(&self) -> coq::term::Record {
        // write attr record
        let mut record_items = Vec::new();
        for (item_name, item_ty) in &self.attrs.attrs {
            let record_item_name = self.lit.make_spec_attr_name(item_name);

            let item = coq::term::RecordDeclItem {
                name: record_item_name,
                params: coq::binder::BinderList::empty(),
                ty: item_ty.to_owned(),
            };
            record_items.push(item);
        }
        // this is parametric in the params and associated types
        let ordered_params = self.get_ordered_params();
        let mut params = ordered_params.get_coq_ty_rt_params();
        params.make_implicit(coq::binder::Kind::MaxImplicit);
        params.0.insert(0, coq::binder::Binder::new_rrgs());

        coq::term::Record {
            name: self.lit.spec_attrs_record.clone(),
            params,
            ty: coq::term::Type::Type,
            constructor: Some(self.lit.spec_record_attrs_constructor_name()),
            body: record_items,
        }
    }

    /// Make the definition for the semantic declaration.
    fn make_semantic_decl(&self) -> Option<coq::command::Command> {
        if let Some(semantic_interp) = &self.attrs.semantic_interp {
            let def_name = self.lit.spec_semantic.as_ref().unwrap();

            let ordered_params = self.get_ordered_params();
            let mut params = ordered_params.get_coq_ty_rt_params();
            params.0.insert(0, coq::binder::Binder::new_rrgs());
            params.append(ordered_params.get_semantic_ty_params().0);

            let body = semantic_interp.to_owned();

            Some(coq::command::Command::Definition(coq::command::Definition {
                name: def_name.to_owned(),
                params,
                ty: Some(coq::term::Type::Prop),
                body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(body)),
            }))
        } else {
            None
        }
    }

    /// Make the spec record declaration.
    fn make_spec_record_decl(&self) -> coq::term::Record {
        let mut record_items = Vec::new();
        for (item_name, item_spec) in &self.default_spec.methods {
            let record_item_name = self.lit.make_spec_method_name(item_name);

            // get number of lifetime parameters of the function
            let num_lifetimes = item_spec.generics.get_num_lifetimes();

            let rt_param_uses = item_spec
                .generics
                .get_direct_ty_params_with_assocs()
                .get_coq_ty_rt_params()
                .make_using_terms();
            let mut ty_term = String::with_capacity(100);
            ty_term.push_str(&format!("spec_with {num_lifetimes} ["));
            push_str_list!(ty_term, &rt_param_uses.0, "; ");
            ty_term.push_str("] fn_spec");

            // params are the rt and st of the direct type parameters
            let mut params = item_spec.generics.get_direct_ty_params_with_assocs().get_coq_ty_params();
            // also quantify over the trait specs etc.
            let trait_params = item_spec.generics.get_direct_attr_trait_parameters(false);
            params.append(trait_params.0);

            let item = coq::term::RecordDeclItem {
                name: record_item_name,
                params,
                ty: coq::term::Type::Literal(ty_term),
            };
            record_items.push(item);
        }

        // this is parametric in the params and associated types
        let ordered_params = self.get_ordered_params();
        let mut params = ordered_params.get_coq_ty_rt_params();
        params.make_implicit(coq::binder::Kind::MaxImplicit);
        params.0.insert(0, coq::binder::Binder::new_rrgs());

        coq::term::Record {
            name: self.lit.spec_record.clone(),
            params,
            ty: coq::term::Type::Type,
            constructor: Some(self.lit.spec_record_constructor_name()),
            body: record_items,
        }
    }

    fn make_spec_incl_decl(&self) -> coq::command::Definition {
        let spec_incl_name = self.lit.spec_incl_name();
        let spec_param_name1 = "spec1".to_owned();
        let spec_param_name2 = "spec2".to_owned();

        let spec_params = self.get_ordered_params();
        let spec_rt_params = spec_params.get_coq_ty_rt_params();
        let spec_rt_using_terms = spec_rt_params.make_using_terms();

        // the spec incl relation first takes the rt params
        let mut spec_incl_params = spec_rt_params;
        spec_incl_params.make_implicit(coq::binder::Kind::MaxImplicit);

        // compute the type of the two spec params
        let spec_param_type =
            coq::term::App::new(self.lit.spec_record.clone(), spec_rt_using_terms.0).to_string();

        // add the two spec params
        spec_incl_params.0.push(coq::binder::Binder::new(
            Some(spec_param_name1.clone()),
            coq::term::Type::Literal(spec_param_type.clone()),
        ));
        spec_incl_params.0.push(coq::binder::Binder::new(
            Some(spec_param_name2.clone()),
            coq::term::Type::Literal(spec_param_type),
        ));

        let mut incls = Vec::new();
        for (name, decl) in &self.default_spec.methods {
            let mut param_decls = decl.generics.get_direct_ty_params_with_assocs().get_coq_ty_params();
            // also quantify over the trait specs etc.
            let trait_params = decl.generics.get_direct_attr_trait_parameters(false);
            param_decls.append(trait_params.0);

            let param_uses = param_decls.make_using_terms();

            let record_item_name = self.lit.make_spec_method_name(name);
            let incl_term = coq::term::Term::All(
                param_decls,
                Box::new(coq::term::Term::App(Box::new(coq::term::App::new(
                    coq::term::Term::Literal("function_subtype".to_owned()),
                    vec![
                        coq::term::Term::App(Box::new(coq::term::App::new(
                            coq::term::Term::RecordProj(
                                Box::new(coq::term::Term::Literal(spec_param_name1.clone())),
                                record_item_name.clone(),
                            ),
                            param_uses.0.clone(),
                        ))),
                        coq::term::Term::App(Box::new(coq::term::App::new(
                            coq::term::Term::RecordProj(
                                Box::new(coq::term::Term::Literal(spec_param_name2.clone())),
                                record_item_name.clone(),
                            ),
                            param_uses.0.clone(),
                        ))),
                    ],
                )))),
            );
            incls.push(incl_term);
        }
        let body = coq::term::Term::Infix("∧".to_owned(), incls);

        coq::command::Definition {
            name: spec_incl_name,
            params: spec_incl_params,
            ty: Some(coq::term::Type::Prop),
            body: coq::command::DefinitionBody::Term(body),
        }
    }

    fn make_trait_incl_defs(&self) -> coq::Document {
        let mut doc = coq::Document::default();

        // write the trait inclusion decls for each method
        for (fn_name, spec) in &self.default_spec.methods {
            let trait_incl_decl_name = &self.lit.method_trait_incl_decls[fn_name];

            // for the args, consider the functions scope
            let scope = &spec.generics;

            let typarams = scope.get_all_ty_params_with_assocs();
            let mut params = typarams.get_coq_ty_params();
            let trait_params = scope.get_all_trait_parameters(true);
            params.append(trait_params.0);

            let mut late_pre = Vec::new();
            for trait_use in scope
                .get_surrounding_trait_requirements()
                .iter()
                .chain(scope.get_direct_trait_requirements().iter())
            {
                let trait_use = trait_use.borrow();
                let trait_use = trait_use.as_ref().unwrap();
                if !trait_use.is_used_in_self_trait {
                    let spec_precond = trait_use.make_spec_param_precond();
                    late_pre.push(spec_precond);
                }
            }
            let term = coq::term::Term::Infix("∧".to_owned(), late_pre);

            // quantify over the generic scope
            let mut quantified_term = String::new();
            scope.format(&mut quantified_term, false, false, &[], &[], &[]).unwrap();
            quantified_term.push_str(&format!(" ({term})"));

            let def = coq::command::Definition {
                name: trait_incl_decl_name.to_owned(),
                params,
                ty: Some(coq::term::Type::Literal("spec_with _ _ Prop".to_owned())),
                body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(quantified_term)),
            };
            let command = coq::command::Command::from(def);
            doc.push(command);
        }

        doc
    }
}

// TODO: Deprecated: Generate a coq::Document instead.
impl<'def> Display for TraitSpecDecl<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Section {}.\n", self.lit.name)?;

        let spec_attrs_record_constructor = self.lit.spec_record_attrs_constructor_name();

        // write attr record
        let spec_attr_record = self.make_attr_record_decl();
        write!(f, "{spec_attr_record}\n")?;
        write!(f, "Global Arguments {} : clear implicits.\n", self.lit.spec_attrs_record)?;
        write!(f, "Global Arguments {} {{_ _}}.\n", self.lit.spec_attrs_record)?;
        write!(f, "Global Arguments {} ", spec_attrs_record_constructor)?;
        // first two are for refinedrustGS *)
        let attr_param_count = 2 + self.get_ordered_params().params.len();
        for _ in 0..attr_param_count {
            write!(f, " {{_}}")?;
        }
        write!(f, ".\n")?;

        // write spec record
        let spec_record = self.make_spec_record_decl();
        write!(f, "{spec_record}\n")?;

        // clear the implicit argument
        write!(f, "Global Arguments {} : clear implicits.\n", self.lit.spec_record)?;
        // make rrgs implicit again
        write!(f, "Global Arguments {} {{_ _}}.\n", self.lit.spec_record)?;

        if let Some(decl) = self.make_semantic_decl() {
            write!(f, "{decl}.\n")?;
        }

        write!(f, "Context `{{RRGS : !refinedrustGS Σ}}.\n")?;

        // write spec incl relation
        let spec_incl_def = self.make_spec_incl_decl();
        write!(f, "{spec_incl_def}\n")?;

        // write the individual function specs
        for item_spec in self.default_spec.methods.values() {
            write!(f, "{item_spec}\n")?;
        }

        // use the identity instantiation of the trait
        let param_inst = self.get_ordered_params();
        let param_inst: Vec<_> = param_inst.params.into_iter().map(Type::LiteralParam).collect();

        // write the bundled records
        let base_decls = make_trait_instance(
            &self.generics,
            &self.assoc_types,
            &param_inst,
            &self.default_spec,
            self.lit,
            true,
            &self.lit.base_spec,
        )?;
        write!(f, "{base_decls}\n")?;

        write!(f, "{}", self.make_trait_incl_defs())?;

        write!(f, "End {}.\n", self.lit.name)
    }
}

/// Coq Names used for the spec of a trait impl.
#[derive(Constructor, Clone, Debug)]
pub struct LiteralTraitImpl {
    /// The name of the record instance for spec information
    pub spec_record: String,
    pub spec_params_record: String,
    pub spec_attrs_record: String,
    /// the optional definition for the trait's semantic interpretation
    pub spec_semantic: Option<String>,
    /// The name of the proof that the base spec is implied by the more specific spec
    pub spec_subsumption_proof: String,
    /// The name of the definition for the lemma statement
    pub spec_subsumption_statement: String,
}
pub type LiteralTraitImplRef<'def> = &'def LiteralTraitImpl;

/// A full instantiation of a trait spec, e.g. for an impl of a trait,
/// which may itself be generic in a `GenericScope`.
#[derive(Constructor, Clone, Debug)]
#[allow(clippy::partial_pub_fields)]
pub struct TraitRefInst<'def> {
    /// literals of the trait this implements
    pub of_trait: LiteralTraitSpecRef<'def>,
    /// the literals for the impl
    pub impl_ref: LiteralTraitImplRef<'def>,

    /// generic scope for this impl, with trait requirements
    generics: GenericScope<'def, LiteralTraitSpecUseRef<'def>>,

    /// instantiation of the trait's scope
    /// Invariant: no surrounding instantiation
    trait_inst: GenericScopeInst<'def>,

    /// the implementation of the associated types
    /// NOTE: in the same order as in the trait definition
    assoc_types_inst: Vec<Type<'def>>,

    /// the spec attribute instantiation
    attrs: TraitSpecAttrsInst,
}

impl<'def> TraitRefInst<'def> {
    /// Get the instantiation of the trait's parameters in the same order as the trait's declaration
    /// (`get_ordered_params`).
    #[must_use]
    fn get_ordered_params_inst(&self) -> Vec<Type<'def>> {
        let mut params: Vec<_> = self
            .trait_inst
            .get_direct_ty_params()
            .iter()
            .chain(self.assoc_types_inst.iter())
            .cloned()
            .collect();

        params.append(&mut self.trait_inst.get_direct_assoc_ty_params());

        params
    }

    /// Get the term for referring to the attr record of this impl
    /// The parameters are expected to be in scope.
    #[must_use]
    fn get_attr_record_term(&self) -> coq::term::App<coq::term::Term, coq::term::Term> {
        let attr_record = &self.impl_ref.spec_attrs_record;

        // get all type parameters
        let mut binders = self.generics.get_all_ty_params_with_assocs().get_coq_ty_rt_params();
        // add all dependent attrs
        binders.append(self.generics.get_all_attr_trait_parameters(false).0);
        let args = binders.make_using_terms();

        coq::term::App::new(coq::term::Term::Literal(attr_record.to_owned()), args.0)
    }

    /// Get the term for referring to the spec record of this impl
    /// The parameters are expected to be in scope.
    #[must_use]
    fn get_spec_record_term(&self) -> coq::term::Term {
        let spec_record = &self.impl_ref.spec_record;

        // specialize to all type parameters
        let tys = self.generics.get_all_ty_params_with_assocs();
        let mut binders = tys.get_coq_ty_params();
        // specialize to all attribute records
        binders.append(self.generics.get_all_attr_trait_parameters(false).0);
        let args = binders.make_using_terms();

        let mut specialized_spec = coq::term::App::new(spec_record.to_owned(), args.0).to_string();

        // specialize to semtys
        specialized_spec.push_str(&self.generics.identity_instantiation());

        coq::term::Term::Literal(specialized_spec)
        //coq::term::Term::App(Box::new(coq::term::App::new(coq::term::Term::Literal(spec_record.
        // to_owned()), args)))
    }

    #[must_use]
    fn get_base_spec_term(&self) -> coq::term::Term {
        let spec_record = &self.of_trait.base_spec;

        let all_args = self.get_ordered_params_inst();

        let mut specialized_spec = String::new();
        specialized_spec.push_str(&format!("({spec_record} "));
        // specialize to rts
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", x.get_rfn_type()) });
        // specialize to sts
        specialized_spec.push(' ');
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("{}", SynType::from(x)) });

        // specialize to further args: first the attrs of this impl
        specialized_spec.push_str(&format!(" {}", self.get_attr_record_term()));
        // then the dependent attrs
        for req in self.trait_inst.get_direct_trait_requirements() {
            // get attrs
            specialized_spec.push_str(&format!(" {}", req.get_attr_term()));
        }

        // specialize to semtys
        push_str_list!(specialized_spec, &all_args, " ", |x| { format!("<TY> {}", x) });
        // specialize to lfts
        push_str_list!(specialized_spec, self.trait_inst.get_lfts(), " ", |x| { format!("<LFT> {}", x) });
        specialized_spec.push_str(" <INST!>)");

        coq::term::Term::Literal(specialized_spec)
    }

    /// Get the term for referring to an item of the attr record of this impl.
    /// The parameters are expected to be in scope.
    #[must_use]
    pub fn get_attr_record_item_term(&self, attr: &str) -> coq::term::Term {
        let item_name = self.of_trait.make_spec_attr_name(attr);
        coq::term::Term::RecordProj(Box::new(Box::new(self.get_attr_record_term()).into()), item_name)
    }
}

/// When translating an impl block, we should generate this, which bundles all components of the
/// implementation together.
#[derive(Constructor, Clone, Debug)]
pub struct TraitImplSpec<'def> {
    /// the instantiation of the trait
    pub trait_ref: TraitRefInst<'def>,

    /// the name of the Coq def of the method definitions and all type parameters they need
    pub methods: TraitInstanceSpec<'def>,
}

impl<'def> TraitImplSpec<'def> {
    /// Generate the definition of the attribute record of this trait impl.
    #[must_use]
    pub fn generate_attr_decl(&self) -> coq::command::Definition {
        let attrs = &self.trait_ref.attrs;
        let attrs_name = &self.trait_ref.impl_ref.spec_attrs_record;
        let of_trait = &self.trait_ref.of_trait;

        // get all type parameters + assoc types
        let mut def_rts_params =
            self.trait_ref.generics.get_all_ty_params_with_assocs().get_coq_ty_rt_params();
        def_rts_params.0.insert(0, coq::binder::Binder::new_rrgs());

        // add other attrs
        def_rts_params.append(self.trait_ref.generics.get_all_attr_trait_parameters(false).0);

        // instantiate the type of the spec record
        let attrs_type_rts: Vec<coq::term::Type> =
            self.trait_ref.get_ordered_params_inst().iter().map(Type::get_rfn_type).collect();
        let attrs_type = coq::term::App::new(of_trait.spec_attrs_record.clone(), attrs_type_rts);
        let attrs_type = coq::term::Type::Literal(format!("{attrs_type}"));

        // write the attr record decl
        let attr_record_term = if attrs.attrs.is_empty() {
            coq::term::Term::Literal(of_trait.spec_record_attrs_constructor_name())
        } else {
            let mut components = Vec::new();
            for (attr_name, inst) in &attrs.attrs {
                // create an item for every attr
                let record_item_name = of_trait.make_spec_attr_name(attr_name);

                let item = coq::term::RecordBodyItem {
                    name: record_item_name,
                    params: coq::binder::BinderList::empty(),
                    term: inst.to_owned(),
                };
                components.push(item);
            }
            let record_body = coq::term::RecordBody { items: components };
            coq::term::Term::RecordBody(record_body)
        };

        coq::command::Definition {
            name: attrs_name.to_owned(),
            params: def_rts_params,
            ty: Some(attrs_type),
            body: coq::command::DefinitionBody::Term(attr_record_term),
        }
    }

    /// Make the definition for the semantic declaration.
    fn make_semantic_decl(&self) -> Option<coq::Document> {
        if let Some(def_name) = &self.trait_ref.impl_ref.spec_semantic {
            let base_name = self.trait_ref.of_trait.spec_semantic.as_ref().unwrap();

            let generics = &self.trait_ref.generics;

            // build params
            let all_tys = generics.get_all_ty_params_with_assocs();
            let mut params = all_tys.get_coq_ty_rt_params();
            params.append(all_tys.get_semantic_ty_params().0);

            // add semantic assumptions for all trait requirements
            for x in generics
                .get_surrounding_trait_requirements()
                .iter()
                .chain(generics.get_direct_trait_requirements().iter())
            {
                let y = x.borrow();
                let x = y.as_ref().unwrap();
                if let Some(term) = x.make_semantic_spec_term() {
                    params.0.push(coq::binder::Binder::new(None, coq::term::Type::Literal(term)));
                }
            }

            let trait_inst = &self.trait_ref.trait_inst;
            let inst_args = trait_inst.get_all_ty_params_with_assocs();

            // type
            let mut specialized_semantic = format!("{} ", base_name.to_owned());
            push_str_list!(specialized_semantic, &inst_args, " ", |x| { format!("{}", x.get_rfn_type()) });
            specialized_semantic.push(' ');
            push_str_list!(specialized_semantic, &inst_args, " ", |x| { x.to_string() });

            let body = coq::proof::Proof::new(coq::proof::Terminator::Qed, |doc| {
                let vernac: coq::Vernac = coq::ltac::LTac::Literal(format!("unfold {base_name} in *; apply _")).into();
                doc.push(vernac);
                });
            let commands = vec![
                coq::command::Command::Lemma(coq::command::Lemma {
                    name: def_name.to_owned(),
                    params,
                    ty: coq::term::Type::Literal(specialized_semantic),
                    body,
                })
                .into(),
            ];

            Some(coq::Document(commands))
        } else {
            None
        }
    }

    #[must_use]
    fn generate_lemma_statement(&self) -> coq::Document {
        let mut doc = coq::Document::default();

        let spec_name = &self.trait_ref.impl_ref.spec_subsumption_statement;

        // generate the lemma statement
        // get parameters
        // this is parametric in the rts, sts, semtys attrs of all trait deps.
        let ty_params = self.trait_ref.generics.get_all_ty_params_with_assocs();
        let mut params = ty_params.get_coq_ty_params();
        params.append(self.trait_ref.generics.get_all_attr_trait_parameters(false).0);

        // instantiation of the trait
        let incl_name = self.trait_ref.of_trait.spec_incl_name();
        let own_spec = self.trait_ref.get_spec_record_term();
        let base_spec = self.trait_ref.get_base_spec_term();

        let scope = &self.trait_ref.generics;
        let mut ty_term = format!("trait_incl_marker (lift_trait_incl {incl_name} (");
        scope.format(&mut ty_term, false, false, &[], &[], &[]).unwrap();
        ty_term.push_str(&format!(" {own_spec}) ("));
        scope.format(&mut ty_term, false, false, &[], &[], &[]).unwrap();
        ty_term.push_str(&format!(" {base_spec}))"));

        let lem = coq::command::Definition {
            name: spec_name.to_owned(),
            params,
            ty: None,
            body: coq::command::DefinitionBody::Term(coq::term::Term::Literal(ty_term)),
        };
        doc.push(coq::command::Command::Definition(lem));

        doc
    }

    #[must_use]
    pub fn generate_proof(&self) -> coq::Document {
        let mut doc = coq::Document::default();

        let lemma_name = &self.trait_ref.impl_ref.spec_subsumption_proof;

        // generate the lemma statement
        // get parameters
        // this is parametric in the rts, sts, semtys attrs of all trait deps.
        let ty_params = self.trait_ref.generics.get_all_ty_params_with_assocs();
        let mut params = ty_params.get_coq_ty_params();
        params.append(self.trait_ref.generics.get_all_attr_trait_parameters(false).0);

        let ty_term =
            format!("{} {}", self.trait_ref.impl_ref.spec_subsumption_statement, params.make_using_terms());

        doc.push(coq::command::Lemma {
            name: lemma_name.to_owned(),
            params,
            ty: coq::term::Type::Literal(ty_term),
            body: coq::proof::Proof::new(coq::proof::Terminator::Qed, |proof| {
                proof.push(model::LTac::SolveTraitInclPrelude(
                    self.trait_ref.impl_ref.spec_subsumption_statement.clone(),
                ));
                proof.push(model::LTac::RepeatLiRStep.scope(coq::ltac::Scope::All));
                proof.push(model::LTac::PrintRemainingTraitGoal.scope(coq::ltac::Scope::All));
                proof.push(model::LTac::Unshelve);
                proof.push(model::LTac::SidecondSolver.scope(coq::ltac::Scope::All));
                proof.push(model::LTac::Unshelve);
                proof.push(model::LTac::SidecondHammer.scope(coq::ltac::Scope::All));
            }),
        });

        doc
    }
}

impl<'def> Display for TraitImplSpec<'def> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let section = coq::section::Section::new(self.trait_ref.impl_ref.spec_record.clone(), |section| {
            section.push(coq::command::Context::refinedrust());

            // Instantiate with the parameter and associated types
            let params_inst = self.trait_ref.get_ordered_params_inst();

            // This relies on all the impl's functions already having been printed
            let mut instance = make_trait_instance(
                &self.trait_ref.generics,
                &Vec::new(),
                &params_inst,
                &self.methods,
                self.trait_ref.of_trait,
                false,
                &self.trait_ref.impl_ref.spec_record,
            )
            .unwrap();

            section.append(&mut instance.0);

            section.append(&mut self.generate_lemma_statement().0);

            if let Some(mut doc) = self.make_semantic_decl() {
                section.append(&mut doc);
            }
        });

        write!( f, "{section}\n")
    }
}

/// Function specification that arises from the instantiation of the default spec of a trait.
/// The surrounding `GenericScope` should have:
/// - the impl's generics
/// - the function's generics, marked as direct
#[derive(Clone, Constructor, Debug)]
pub struct InstantiatedTraitFunctionSpec<'def> {
    /// the trait we are instantiating
    trait_ref: TraitRefInst<'def>,
    /// name of the trait method we are instantiating
    trait_method_name: String,
}

impl<'def> InstantiatedTraitFunctionSpec<'def> {
    fn write_spec_term<F>(
        &self,
        f: &mut F,
        scope: &GenericScope<'def, LiteralTraitSpecUseRef<'def>>,
    ) -> fmt::Result
    where
        F: fmt::Write,
    {
        // write the scope of the impl
        // (this excludes the function's own direct scope, as that is already quantified in the
        // base spec we are going to instantiate)
        //write!(f, "spec!")?;
        self.trait_ref.generics.format(f, false, false, &[], &[], &[])?;
        //write!(f, ",\n ")?;

        let all_ty_params = self.trait_ref.get_ordered_params_inst();

        // apply the trait's base spec
        let mut params = Vec::new();
        // add rt params
        for ty in &all_ty_params {
            params.push(format!("{}", ty.get_rfn_type()));
        }

        // add syntype params
        for ty in &all_ty_params {
            params.push(format!("{}", SynType::from(ty)));
        }

        // also instantiate with the attrs that are quantified on the outside
        let attr_term = self.trait_ref.get_attr_record_term();
        params.push(attr_term.to_string());

        // instantiate with the attrs of trait requirements
        for trait_req in self.trait_ref.trait_inst.get_direct_trait_requirements() {
            params.push(trait_req.get_attr_term());
            //params.push(trait_req.get_spec_term());
        }

        let mut applied_base_spec = String::with_capacity(100);
        write!(applied_base_spec, "{}\n", coq::term::App::new(&self.trait_ref.of_trait.base_spec, params))?;

        // now add the semantic components
        // instantiate semantic types
        for ty in &all_ty_params {
            write!(applied_base_spec, " <TY> {ty}")?;
        }
        // instantiate lifetimes
        for lft in self.trait_ref.trait_inst.get_lfts() {
            write!(applied_base_spec, " <LFT> {lft}")?;
        }
        write!(applied_base_spec, " <INST!>")?;

        // now we need to project out the concrete function specification
        // we pass as parameters the direct rts and sts of the function
        // for that, look in the generic scope for direct parameters
        let spec_params = scope.get_direct_ty_params_with_assocs().get_coq_ty_params();
        let spec_params = spec_params.make_using_terms();

        // also instantiate the direct trait requirements of the function, which should be
        // quantified in the same way in the surrounding scope
        let trait_params_inst = scope.get_direct_attr_trait_parameters(false).make_using_terms();

        write!(
            f,
            "({applied_base_spec}).({}) {spec_params} {trait_params_inst} <MERGE!>",
            self.trait_ref.of_trait.make_spec_method_name(&self.trait_method_name)
        )?;

        Ok(())
    }
}
