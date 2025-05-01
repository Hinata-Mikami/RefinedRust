// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [terms] section.
//!
//! [terms]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#term-term

use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;
use indent_write::fmt::IndentWriter;
use itertools::Itertools;

use crate::coq::binder;
use crate::{display_list, model, BASE_INDENT};

/// A [term].
///
/// [term]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-term
#[derive(Clone, Eq, PartialEq, Hash, Debug, FromVariants)]
pub enum Term {
    /// A literal
    Literal(String),

    /// An application
    #[from_variants(into)]
    App(Box<App<Term, Term>>),

    /// A record constructor
    RecordBody(RecordBody),

    /// A projection `a.(b)` from a record `a`
    #[from_variants(skip)]
    RecordProj(Box<Term>, String),

    /// A universal quantifier
    #[from_variants(skip)]
    All(binder::BinderList, Box<Term>),

    /// An existential quantifier
    #[from_variants(skip)]
    Exists(binder::BinderList, Box<Term>),

    /// An infix operator
    #[from_variants(skip)]
    Infix(String, Vec<Term>),
}

impl Display for Term {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        match self {
            Self::Literal(lit) => {
                let mut f2 = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
                write!(f2, "{lit}")
            },
            Self::RecordBody(b) => {
                write!(f, "{b}")
            },
            Self::RecordProj(rec, component) => {
                write!(f, "{rec}.({component})")
            },
            Self::App(box a) => write!(f, "{a}"),
            Self::All(binders, box body) => {
                if !binders.0.is_empty() {
                    write!(f, "∀ {binders}, ")?;
                }
                write!(f, "{body}")
            },
            Self::Exists(binders, box body) => {
                if !binders.0.is_empty() {
                    write!(f, "∃ {binders}, ")?;
                }
                write!(f, "{body}")
            },
            Self::Infix(op, terms) => {
                if terms.is_empty() {
                    write!(f, "True")
                } else {
                    write!(f, "{}", terms.iter().format(&format!(" {op} ")))
                }
            },
        }
    }
}

#[allow(clippy::module_name_repetitions)]
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("{}", display_list!(_0, " ", "{}"))]
pub struct TermList(pub Vec<Term>);

impl TermList {
    #[must_use]
    pub const fn new(params: Vec<Term>) -> Self {
        Self(params)
    }

    #[must_use]
    pub const fn empty() -> Self {
        Self(vec![])
    }

    pub fn append(&mut self, params: Vec<Term>) {
        self.0.extend(params);
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

impl<T: Display, U: Display> Display for App<T, U> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.rhs.is_empty() {
            return write!(f, "{}", self.lhs);
        }

        write!(f, "({} {})", self.lhs, display_list!(&self.rhs, " ", "({})"))
    }
}

impl<T, U> App<T, U> {
    pub fn new(lhs: T, rhs: Vec<U>) -> Self {
        Self { lhs, rhs }
    }

    pub fn new_lhs(lhs: T) -> Self {
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

impl Display for RecordBody {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

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

impl Display for RecordBodyItem {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        let mut writer = IndentWriter::new_skip_initial(BASE_INDENT, &mut *f);
        write!(writer, "{} {} :=\n{};", self.name, self.params, self.term)
    }
}

/// A [type], extended with user defined types.
///
/// [type]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-type
pub type Type = RocqType<model::Type>;

pub(crate) fn fmt_list<T: fmt::Display>(v: &Vec<RocqType<T>>) -> String {
    format!("[{}]", display_list!(v, "; "))
}

pub(crate) fn fmt_hlist<T: fmt::Display>(v: &Vec<RocqType<T>>) -> String {
    format!("+[{}]", display_list!(v, "; "))
}

pub(crate) fn fmt_prod<T: fmt::Display>(v: &Vec<RocqType<T>>) -> String {
    match v.as_slice() {
        [] => "unit".to_owned(),
        [t] => t.to_string(),
        _ => format!("({})%type", display_list!(v, " * ")),
    }
}

/// A Rocq [type], limited to Rocq defined types.
///
/// [type]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-type
#[derive(Clone, Eq, PartialEq, Hash, Debug, Display)]
pub enum RocqType<T> {
    /// Literals
    Literal(String),

    /// Function type
    ///
    /// The argument vector should be non-empty.
    #[display("{} → {}", display_list!(_0, " → ", "({})"), *_1)]
    Function(Vec<Box<RocqType<T>>>, Box<RocqType<T>>),

    /// Placeholder
    #[display("_")]
    Infer,

    /// `Prop` type
    #[display("Prop")]
    Prop,

    /// `Type` type
    #[display("Type")]
    Type,

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
    Prod(Vec<RocqType<T>>),

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

impl Display for Record {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use fmt::Write;

        let constructor = self.constructor.clone().unwrap_or_default();
        write!(f, "Record {} {} : {} := {constructor} {{\n", self.name, self.params, self.ty)?;
        let mut f2 = IndentWriter::new(BASE_INDENT, &mut *f);
        for it in &self.body {
            write!(f2, "{it};\n")?;
        }
        write!(f, "}}.")
    }
}
