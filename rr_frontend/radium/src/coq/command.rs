// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! The [command] section.
//!
//! [command]: https://rocq-prover.org/doc/v8.20/refman/coq-cmdindex.html

use std::fmt;

use derive_more::{Display, From};
use indent_write::indentable::Indentable as _;

use crate::BASE_INDENT;
use crate::coq::{self, Attribute, Ident, binder, eval, inductive, module, proof, section, syntax, term};

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
#[derive(Clone, Eq, PartialEq, Debug, Display, From)]
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

    /// The first variant of the [`Canonical Structure`] command.
    ///
    /// [`Canonical Structure`]: https://rocq-prover.org/doc/v8.20/refman/language/extensions/canonical.html#declaration-of-canonical-structures
    #[display("{}", _0)]
    CanonicalDecl(CanonicalDecl),

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

    /// The [`Next Obligation`] command.
    ///
    /// [`Next Obligation`]: https://rocq-prover.org/doc/v8.20/refman/addendum/program.html?highlight=next%20obligation#coq:cmd.Next-Obligation
    NextObligation(ObligationProof),

    /// The [`Section`] command.
    ///
    /// [`Section`]: https://rocq-prover.org/doc/v8.20/refman/language/core/sections.html#using-sections
    #[display("{}", _0)]
    Section(section::Section),

    #[display("{}", _0)]
    Arguments(Arguments),

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
#[derive(Clone, Eq, PartialEq, Debug, Display, From)]
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
    pub program_mode: bool,
}

impl fmt::Display for Definition {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let pref = if self.program_mode { "Program " } else { "" };
        if let Some(ty) = &self.ty {
            write!(f, "{pref}Definition {} {} : {ty}", self.name, self.params)?;
        } else {
            write!(f, "{pref}Definition {} {}", self.name, self.params)?;
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

/// An obligation proof.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ObligationProof {
    pub content: coq::ProofDocument,
    pub terminator: proof::Terminator,
}

impl fmt::Display for ObligationProof {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f, "Next Obligation.")?;
        write!(f, "{}", (&self.content).indented(BASE_INDENT))?;
        writeln!(f, "{}.", self.terminator)
    }
}

/// The [`Instance`] command.
///
/// [`Instance`]: https://rocq-prover.org/doc/v8.20/refman/addendum/type-classes.html#coq:cmd.Instance
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct Instance {
    pub name: Option<String>,
    pub params: binder::BinderList,
    pub ty: term::Type,
    pub body: proof::Proof,
}
impl fmt::Display for Instance {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if let Some(name) = &self.name {
            writeln!(f, "Instance {} {} : {}.", name, self.params, self.ty)?;
        } else {
            let ty =
                term::Term::All(self.params.clone(), Box::new(term::Term::Type(Box::new(self.ty.clone()))));
            writeln!(f, "Instance: {ty}.")?;
        }
        write!(f, "{}", self.body)
    }
}

/// The first variant [`Canonical Structure`] command.
///
/// [`Canonical Structure`]: https://rocq-prover.org/doc/v8.20/refman/language/extensions/canonical.html#declaration-of-canonical-structures
#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Canonical Structure {}.\n", _0)]
pub struct CanonicalDecl(pub Ident);

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Arguments {} {}.\n", name, arguments_string)]
pub struct Arguments {
    pub name: String,
    pub arguments_string: String,
}
