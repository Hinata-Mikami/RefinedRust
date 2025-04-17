// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! [Sections].
//!
//! [Sections]: https://coq.inria.fr/doc/v8.20/refman/language/core/sections.html

use derive_more::Display;
use indent_write::fmt::IndentWriter;
use indent_write::indentable::Indentable;

use crate::coq::Document;
use crate::BASE_INDENT;

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Section {}.\n{}End {}.", name, proof.to_string().indented(BASE_INDENT), name)]
pub struct Section {
    name: String,
    proof: Document,
}

impl Section {
    pub fn new<Err>(name: String, callback: impl Fn(&mut Document) -> Result<(), Err>) -> Result<Self, Err> {
        let mut proof = Document::default();

        callback(&mut proof)?;

        Ok(Self { name, proof })
    }
}
