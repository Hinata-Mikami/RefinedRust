// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [terms] section.
//!
//! [terms]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#term-term

use std::fmt;

use derive_more::{Display, From};
use indent_write::fmt::IndentWriter;

use crate::coq::{Ident, binder};
use crate::{BASE_INDENT, fmt_list, model};

/// A [term], extended with user defined terms.
///
/// [term]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-term
pub type Term = RocqTerm<model::Term, model::Type>;

pub(crate) fn fmt_binders(op: &str, binders: &binder::BinderList) -> String {
    fmt_binders_empty(op, binders, "")
}

pub(crate) fn fmt_binders_empty(op: &str, binders: &binder::BinderList, empty: &str) -> String {
    if binders.0.is_empty() {
        return empty.to_owned();
    }

    format!("{} {}, ", op, binders)
}

/// A Rocq [term], limited to Rocq defined terms.
///
/// [term]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-term
#[derive(Clone, Eq, PartialEq, Hash, Debug, From)]
#[expect(clippy::module_name_repetitions)]
pub enum RocqTerm<T, U> {
    /// A Rocq type
    Type(Box<RocqType<U, T>>),

    /// A literal
    Literal(String),

    /// A hole
    Infer,

    /// A reference to an identifier
    Ident(Ident),

    /// An application
    #[from(forward)]
    App(Box<App<Term, Term>>),

    /// A let declaration
    LetIn(Ident, Box<RocqTerm<T, U>>, Box<RocqTerm<T, U>>),

    /// A record constructor
    RecordBody(RecordBody),

    /// A projection `a.(b)` from a record `a`
    #[from(ignore)]
    RecordProj(Box<Term>, String),

    /// A universal quantifier
    #[from(ignore)]
    All(binder::BinderList, Box<Term>),

    /// An existential quantifier
    #[from(ignore)]
    Exists(binder::BinderList, Box<Term>),

    /// A lambda
    #[from(ignore)]
    Lambda(binder::BinderList, Box<Term>),

    /// An infix operator
    #[from(ignore)]
    Infix(String, Vec<Term>),

    /// A prefix operator
    #[from(ignore)]
    Prefix(String, Box<Term>),

    /// A term with a type annotation.
    #[from(ignore)]
    AsType(Box<RocqTerm<T, U>>, Box<RocqType<U, T>>),

    /// User defined type
    UserDefined(T),
}

impl<T: fmt::Display, U: fmt::Display> fmt::Display for RocqTerm<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write as _;

        match self {
            Self::Type(t) => {
                write!(f, "{t}")
            },
            Self::Literal(lit) => {
                let mut f2 = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
                write!(f2, "{lit}")
            },
            Self::Infer => {
                write!(f, "_")
            },
            Self::Ident(ident) => {
                write!(f, "{ident}")
            },
            Self::RecordBody(b) => {
                write!(f, "{b}")
            },
            Self::RecordProj(rec, component) => {
                write!(f, "{rec}.({component})")
            },
            Self::App(box a) => write!(f, "{a}"),
            Self::LetIn(ident, term, term2) => {
                write!(f, "let {ident} := {term} in {term2}")
            },
            Self::All(binders, box body) => {
                write!(f, "{}{}", fmt_binders("∀", binders), body)
            },
            Self::Exists(binders, box body) => {
                write!(f, "{}{}", fmt_binders("∃", binders), body)
            },
            Self::Lambda(binders, box body) => {
                write!(f, "{}{}", fmt_binders_empty("λ", binders, "λ '(), "), body)
            },
            Self::Infix(op, terms) => {
                if terms.is_empty() {
                    write!(f, "True")
                } else {
                    write!(f, "{}", fmt_list!(terms, &format!(" {op} "), "({})"))
                }
            },
            Self::Prefix(op, term) => {
                write!(f, "{op} ({term})")
            },
            Self::AsType(t, ty) => {
                write!(f, "({t}) : ({ty})")
            },
            Self::UserDefined(user_type) => {
                write!(f, "{}", user_type)
            },
        }
    }
}

/// An [application].
///
/// [application]: https://rocq-prover.org/doc/v8.20/refman/language/core/assumptions.html#function-application
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub struct App<T, U> {
    pub(crate) lhs: T,
    pub(crate) rhs: Vec<U>,
}

impl<T: fmt::Display, U: fmt::Display> fmt::Display for App<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write!(f, "({} {})", self.lhs, fmt_list!(&self.rhs, " ", "({})"))
    }
}

impl<T, U> App<T, U> {
    pub const fn new(lhs: T, rhs: Vec<U>) -> Self {
        Self { lhs, rhs }
    }

    pub const fn new_lhs(lhs: T) -> Self {
        Self {
            lhs,
            rhs: Vec::new(),
        }
    }
}

/// A [record].
///
/// [record]: https://rocq-prover.org/doc/v8.20/refman/language/core/records.html#constructing-records
#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RecordBody {
    pub items: Vec<RecordBodyItem>,
}

impl fmt::Display for RecordBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write as _;

        write!(f, "{{|\n")?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.items {
            write!(f2, "{}\n", it)?;
        }
        write!(f, "|}}\n")
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Hash)]
pub struct RecordBodyItem {
    pub name: String,
    pub params: binder::BinderList,
    pub term: Term,
}

impl fmt::Display for RecordBodyItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write as _;

        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        write!(writer, "{} {} :=\n{};", self.name, self.params, self.term)
    }
}

/// A [type], extended with user defined types.
///
/// [type]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-type
pub type Type = RocqType<model::Type, model::Term>;

pub(crate) fn fmt_list(v: &Vec<Type>) -> String {
    format!("[{}]", fmt_list!(v, "; "))
}

pub(crate) fn fmt_hlist(v: &Vec<Type>) -> String {
    format!("+[{}]", fmt_list!(v, "; "))
}

pub(crate) fn fmt_prod(v: &Vec<Type>) -> String {
    match v.as_slice() {
        [] => "unit".to_owned(),
        [t] => t.to_string(),
        _ => format!("({})%type", fmt_list!(v, " * ")),
    }
}

/// A Rocq [type], limited to Rocq defined types.
///
/// [type]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-type
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum RocqType<T, U> {
    /// An arbitrary term.
    #[display("{}", _0)]
    Term(Box<RocqTerm<U, T>>),

    /// Literals
    #[display("({_0})")]
    Literal(String),

    /// Function type
    ///
    /// The argument vector should be non-empty.
    #[display("{} → {}", fmt_list!(_0, " → ", "({})"), *_1)]
    Function(Vec<Type>, Box<Type>),

    /// Placeholder
    #[display("_")]
    Infer,

    /// `Prop` type
    #[display("Prop")]
    Prop,

    /// `Type` type
    #[display("Type")]
    Type,

    /// The `RT` type
    #[display("RT")]
    RT,

    /// `Unit` type
    #[display("unit")]
    Unit,

    /// Integers type
    #[display("Z")]
    Z,

    /// Booleans type
    #[display("bool")]
    Bool,

    /// Product type
    #[display("{}", fmt_prod(_0))]
    Prod(Vec<Type>),

    /// User defined type
    #[display("{}", _0)]
    UserDefined(T),
}

/* TODO: Definitions and constructors use the same grammar (`term_record`): Merge them. */
#[derive(Clone, Debug, Display, Eq, PartialEq)]
#[display("{} {} : {}", name, params, ty)]
pub struct RecordDeclItem {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: Type,
}

/// A record declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Record {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: Type,
    pub constructor: Option<String>,
    pub body: Vec<RecordDeclItem>,
}

impl fmt::Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write as _;

        let constructor = self.constructor.clone().unwrap_or_default();
        write!(f, "Record {} {} : {} := {constructor} {{\n", self.name, self.params, self.ty)?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.body {
            write!(f2, "{it};\n")?;
        }
        write!(f, "}}.")
    }
}
