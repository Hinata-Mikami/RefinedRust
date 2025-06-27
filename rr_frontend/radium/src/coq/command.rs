// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [command] section.
//!
//! [command]: https://rocq-prover.org/doc/v8.20/refman/coq-cmdindex.html

use std::fmt;

use derive_more::Display;
use from_variants::FromVariants;
use indent_write::indentable::Indentable as _;

use crate::BASE_INDENT;
use crate::coq::{Attribute, binder, eval, inductive, module, proof, section, syntax, term};

/// A [command], with optional attributes.
///
/// [command]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-command
#[expect(clippy::module_name_repetitions)]
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct CommandAttrs {
    pub command: Command,
    pub attributes: Option<Attribute>,
}

impl fmt::Display for CommandAttrs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(attributes) = &self.attributes {
            write!(f, "{} ", attributes)?;
        }
        write!(f, "{}", self.command)
    }
}

impl CommandAttrs {
    #[must_use]
    pub fn new<I: Into<Command>>(command: I) -> Self {
        Self {
            attributes: None,
            command: command.into(),
        }
    }

    #[must_use]
    pub fn attributes<I: Into<Attribute>>(self, attributes: I) -> Self {
        let attributes = Some(attributes.into());

        Self { attributes, ..self }
    }
}

/// A [query command], with optional attributes.
///
/// [query command]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-query_command
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct QueryCommandAttrs {
    pub command: QueryCommand,
    pub natural: Option<i32>,
    pub attributes: Option<Attribute>,
}

impl fmt::Display for QueryCommandAttrs {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(attributes) = &self.attributes {
            write!(f, "{} ", attributes)?;
        }

        if let Some(natural) = &self.natural {
            write!(f, "{}: ", natural)?;
        }

        write!(f, "{}", self.command)
    }
}

impl QueryCommandAttrs {
    #[must_use]
    pub fn new<I: Into<QueryCommand>>(command: I) -> Self {
        Self {
            attributes: None,
            natural: None,
            command: command.into(),
        }
    }

    #[must_use]
    pub fn attributes<I: Into<Attribute>>(self, attributes: I) -> Self {
        let attributes = Some(attributes.into());

        Self { attributes, ..self }
    }
}

/// A [command].
///
/// [command]: https://rocq-prover.org/doc/v8.20/refman/language/core/basic.html#grammar-token-command
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum Command {
    /// The [`From ... Require`] command.
    ///
    /// [`From ... Require`]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/vernacular-commands.html#coq:cmd.From-%E2%80%A6-Require
    #[display("{}.", _0)]
    FromRequire(module::FromRequire),

    /// The [`Inductive`] command.
    ///
    /// [`Inductive`]: https://rocq-prover.org/doc/v8.20/refman/language/core/inductive.html#inductive-types
    #[display("{}", _0)]
    Inductive(inductive::Inductive),

    /// The [`Instance`] command.
    ///
    /// [`Instance`]: https://rocq-prover.org/doc/v8.20/refman/addendum/type-classes.html#coq:cmd.Instance
    #[display("{}", _0)]
    Instance(Instance),

    /// The [`Open Scope`] command.
    ///
    /// [`Open Scope`]: https://rocq-prover.org/doc/v8.20/refman/user-extensions/syntax-extensions.html#coq:cmd.Open-Scope
    #[display("{}", _0)]
    OpenScope(syntax::OpenScope),

    /// The [`Record`] command.
    ///
    /// [`Record`]: https://rocq-prover.org/doc/v8.20/refman/language/core/records.html#coq:cmd.Record
    #[display("{}", _0)]
    Record(term::Record),

    /// The [`Context`] command.
    ///
    /// [`Command`]: https://rocq-prover.org/doc/v8.20/refman/language/core/sections.html#coq:cmd.Context
    #[display("{}", _0)]
    Context(Context),

    /// The [`Definition`] command.
    ///
    /// [`Definition`]: https://rocq-prover.org/doc/v8.20/refman/language/core/definitions.html#coq:cmd.Definition
    #[display("{}", _0)]
    Definition(Definition),

    /// The [`Lemma`] command.
    ///
    /// [`Lemma`]: https://rocq-prover.org/doc/v8.20/refman/language/core/definitions.html#coq:cmd.Lemma
    #[display("{}", _0)]
    Lemma(Lemma),

    /// The [`Section`] command.
    ///
    /// [`Section`]: https://rocq-prover.org/doc/v8.20/refman/language/core/sections.html#using-sections
    #[display("{}", _0)]
    Section(section::Section),

    /// The [`Typeclasses Transparent`] command.
    ///
    /// [`Typeclasses Transparent`]: https://rocq-prover.org/doc/v8.20/refman/addendum/type-classes.html#coq:cmd.Typeclasses-Transparent
    #[display("Typeclasses Transparent {}.", _0)]
    TypeclassesTransparent(String),
}

impl From<Command> for CommandAttrs {
    fn from(command: Command) -> Self {
        Self::new(command)
    }
}

/// A [query command].
///
/// [query command]: https://rocq-prover.org/doc/v8.20/refman/proof-engine/vernacular-commands.html#grammar-token-query_command
#[expect(clippy::module_name_repetitions)]
#[derive(Clone, Eq, PartialEq, Debug, Display, FromVariants)]
pub enum QueryCommand {
    #[display("{}", _0)]
    Compute(eval::Compute),
}

impl From<QueryCommand> for QueryCommandAttrs {
    fn from(command: QueryCommand) -> Self {
        Self::new(command)
    }
}

/// A context declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Context {
    items: binder::BinderList,
}

impl Context {
    #[must_use]
    pub const fn new(items: binder::BinderList) -> Self {
        Self { items }
    }

    #[must_use]
    pub fn refinedrust() -> Self {
        Self {
            items: binder::BinderList::new(vec![binder::Binder::new_rrgs()]),
        }
    }
}

impl fmt::Display for Context {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.items.0.is_empty() { Ok(()) } else { write!(f, "Context {}.", self.items) }
    }
}

/// A Rocq definition
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Definition {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: Option<term::Type>,
    pub body: DefinitionBody,
}

impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(ty) = &self.ty {
            write!(f, "Definition {} {} : {ty}", self.name, self.params)?;
        } else {
            write!(f, "Definition {} {}", self.name, self.params)?;
        }

        match &self.body {
            DefinitionBody::Term(term) => {
                writeln!(f, " :=")?;
                write!(f, "{}.", term.indented(BASE_INDENT))?;
            },

            DefinitionBody::Proof(proof) => {
                writeln!(f, ".")?;
                write!(f, "{}", proof)?;
            },
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq, Display)]
pub enum DefinitionBody {
    #[display("{}", _0)]
    Term(term::Term),

    #[display("{}", _0)]
    Proof(proof::Proof),
}

/// A Rocq lemma declaration.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Lemma {
    pub name: String,
    pub params: binder::BinderList,
    pub ty: term::Type,
    pub body: proof::Proof,
}

impl fmt::Display for Lemma {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Lemma {} {} : {}.", self.name, self.params, self.ty)?;
        write!(f, "{}", self.body)
    }
}

/// The [`Instance`] command.
///
/// [`Instance`]: https://rocq-prover.org/doc/v8.20/refman/addendum/type-classes.html#coq:cmd.Instance
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Instance: {}.\n{}", _0, _1)]
pub struct Instance(pub term::Type, pub proof::Proof);
