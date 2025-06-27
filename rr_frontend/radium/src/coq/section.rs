// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! [Sections].
//!
//! [Sections]: https://rocq-prover.org/doc/v8.20/refman/language/core/sections.html

use derive_more::Display;
use indent_write::indentable::Indentable as _;

use crate::{BASE_INDENT, coq};

#[derive(Clone, Eq, PartialEq, Debug, Display)]
#[display("Section {}.\n{}End {}.", name, content.to_string().indented(BASE_INDENT), name)]
pub struct Section {
    name: String,
    content: coq::Document,
}

impl Section {
    pub fn new<F: FnOnce(&mut coq::Document)>(name: String, callback: F) -> Self {
        let mut content = coq::Document::default();

        callback(&mut content);

        Self { name, content }
    }
}
