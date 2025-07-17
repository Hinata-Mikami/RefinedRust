use derive_more::Display;

use crate::{coq, fmt_list};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum IntType {
    #[display("I8")]
    I8,

    #[display("I16")]
    I16,

    #[display("I32")]
    I32,

    #[display("I64")]
    I64,

    #[display("I128")]
    I128,

    #[display("U8")]
    U8,

    #[display("U16")]
    U16,

    #[display("U32")]
    U32,

    #[display("U64")]
    U64,

    #[display("U128")]
    U128,

    #[display("ISize")]
    ISize,

    #[display("USize")]
    USize,
}

// NOTE: see ty::layout::layout_of_uncached for the rustc description of this.
pub(crate) static BOOL_REPR: IntType = IntType::U8;

/// A syntactic `RefinedRust` type.
///
/// Every semantic `RefinedRust` type has a corresponding syntactic type that determines its
/// representation in memory.
///
/// A syntactic type does not necessarily specify a concrete [layout]. A [layout] is only fixed once
/// a specific layout algorithm that resolves the non-deterministic choice of the compiler.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum SynType {
    #[display("BoolSynType")]
    Bool,

    #[display("CharSynType")]
    Char,

    #[display("(IntSynType {})", _0)]
    Int(IntType),

    #[display("PtrSynType")]
    Ptr,

    #[display("FnPtrSynType")]
    FnPtr,

    #[display("(UntypedSynType {})", _0)]
    Untyped(Layout),

    #[display("UnitSynType")]
    Unit,

    #[display("UnitSynType")]
    Never,

    /// A Coq term, in case of generics.
    ///
    /// This Coq term is required to have type `syn_type`.
    #[display("{}", _0)]
    Literal(String),
    // no struct or enums - these are specified through literals.
}

/// Representation of Caesium's optypes.
#[derive(Clone, Eq, PartialEq, Debug, Display)]
pub enum OpType {
    #[display("IntOp {}", _0)]
    Int(IntType),

    #[display("BoolOp")]
    Bool,

    #[display("CharOp")]
    Char,

    #[display("PtrOp")]
    Ptr,

    // a term for the struct_layout, and optypes for the individual fields
    #[display("StructOp {} [{}]", _0, fmt_list!(_1, "; "))]
    Struct(coq::term::App<String, String>, Vec<OpType>),

    #[display("UntypedOp ({})", _0)]
    Untyped(Layout),

    #[display("{}", _0)]
    Literal(coq::term::App<String, String>),
}

/// A representation of Caesium layouts we are interested in.
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum Layout {
    // in the case of 32bits
    #[display("void*")]
    Ptr,

    // layout specified by the int type
    #[display("(it_layout {})", _0)]
    Int(IntType),

    // size 1, similar to u8/i8
    #[display("bool_layout")]
    Bool,

    // size 4, similar to u32
    #[display("char_layout")]
    Char,

    // guaranteed to have size 0 and alignment 1.
    #[display("(layout_of unit_sl)")]
    Unit,

    /// used for variable layout terms, e.g. for struct layouts or generics
    #[display("{}", _0)]
    Literal(coq::term::App<String, String>),

    /// padding of a given number of bytes
    #[display("(Layout {}%nat 0%nat)", _0)]
    Pad(u32),
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
