// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::collections::HashSet;

use attribute_parse::parse;
use radium::coq;
use rr_rustc_interface::hir;
use rr_rustc_interface::hir::def_id::LocalDefId;

use crate::spec_parsers::parse_utils::{self, attr_args_tokens, str_err};

/// Parse attributes on a module.
/// Permitted attributes:
/// - `rr::import("A.B.C`", "D"), which will import the Coq path "A.B.C.D"
pub(crate) trait ModuleAttrParser {
    fn parse_module_attrs<'a>(
        &'a mut self,
        did: LocalDefId,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<ModuleAttrs, String>;
}

#[derive(Clone, Debug)]
pub(crate) struct ModuleAttrs {
    pub exports: Vec<coq::module::Export>,
    pub includes: HashSet<String>,
    pub export_includes: HashSet<String>,
}

pub(crate) struct VerboseModuleAttrParser;

impl VerboseModuleAttrParser {
    pub(crate) const fn new() -> Self {
        Self {}
    }
}

impl ModuleAttrParser for VerboseModuleAttrParser {
    fn parse_module_attrs<'a>(
        &'a mut self,
        _did: LocalDefId,
        attrs: &'a [&'a hir::AttrItem],
    ) -> Result<ModuleAttrs, String> {
        let mut exports: Vec<coq::module::Export> = Vec::new();
        let mut includes: HashSet<String> = HashSet::new();
        let mut export_includes: HashSet<String> = HashSet::new();

        for &it in attrs {
            let path_segs = &it.path.segments;
            let args = &it.args;

            let Some(seg) = path_segs.get(1) else {
                continue;
            };

            let buffer = parse::Buffer::new(&attr_args_tokens(&it.args));
            match seg.name.as_str() {
                "import" => {
                    let path: parse_utils::CoqExportModule = buffer.parse(&()).map_err(str_err)?;
                    exports.push(path.into());
                },
                "include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
                    includes.insert(name.value());
                },
                "export_include" => {
                    let name: parse::LitStr = buffer.parse(&()).map_err(str_err)?;
                    export_includes.insert(name.value());
                },
                _ => {
                    return Err(format!("unknown attribute for module specification: {:?}", args));
                },
            }
        }

        Ok(ModuleAttrs {
            exports,
            includes,
            export_includes,
        })
    }
}
