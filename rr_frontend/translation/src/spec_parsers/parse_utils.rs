// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use std::fmt;

/// This provides some general utilities for RefinedRust-specific attribute parsing.
use attribute_parse::{parse, MToken};
use lazy_static::lazy_static;
use log::trace;
use parse::Peek as _;
use radium::{coq, specs};
use regex::{Captures, Regex};

/// Parse either a literal string (a term/pattern) or an identifier, e.g.
/// `x`, `z`, `"w"`, `"(a, b)"`
#[derive(Debug)]
pub enum IdentOrTerm {
    Ident(String),
    Term(String),
}

impl IdentOrTerm {
    fn process<'def, T: ParamLookup<'def>>(self, meta: &T) -> Self {
        match self {
            Self::Ident(id) => Self::Ident(id),
            Self::Term(t) => {
                let (s, _) = meta.process_coq_literal(&t);
                Self::Term(s)
            },
        }
    }
}

impl<U> parse::Parse<U> for IdentOrTerm
where
    U: ?Sized,
{
    fn parse(stream: parse::Stream, meta: &U) -> parse::Result<Self> {
        if let Ok(ident) = parse::Ident::parse(stream, meta) {
            // it's an identifer
            Ok(Self::Ident(ident.value()))
        } else {
            parse::LitStr::parse(stream, meta).map(|s| Self::Term(s.value()))
        }
    }
}

impl fmt::Display for IdentOrTerm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Ident(s) | Self::Term(s) => write!(f, "{s}"),
        }
    }
}

/// Parse a refinement with an optional type annotation, e.g.
/// `x`, `"y"`, `x @ "int i32"`, `"(a, b)" @ "struct_t ...."`.
#[derive(Debug)]
pub struct LiteralTypeWithRef {
    pub rfn: IdentOrTerm,
    pub ty: Option<String>,
    pub raw: specs::TypeIsRaw,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for LiteralTypeWithRef {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        // check if a #raw annotation is present
        let loc = stream.pos();
        let mut raw = specs::TypeIsRaw::No;
        if parse::Pound::peek(stream) {
            stream.parse::<_, MToken![#]>(meta)?;
            let macro_cmd: parse::Ident = stream.parse(meta)?;
            match macro_cmd.value().as_str() {
                "raw" => {
                    raw = specs::TypeIsRaw::Yes;
                },
                _ => return Err(parse::Error::OtherErr(loc.unwrap(), "Unsupported flag".to_owned())),
            }
        }

        // refinement
        let rfn: IdentOrTerm = stream.parse(meta)?;
        let rfn = rfn.process(meta);

        // optionally, parse a type annotation (otherwise, use the translated Rust type)
        if parse::At::peek(stream) {
            stream.parse::<_, MToken![@]>(meta)?;
            let ty: parse::LitStr = stream.parse(meta)?;
            let (ty, _) = meta.process_coq_literal(&ty.value());

            Ok(Self {
                rfn,
                ty: Some(ty),
                raw,
            })
        } else {
            Ok(Self { rfn, ty: None, raw })
        }
    }
}

/// Parse a type annotation.
#[derive(Debug)]
pub struct LiteralType {
    pub ty: String,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for LiteralType {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        let ty: parse::LitStr = stream.parse(meta)?;
        let (ty, _) = meta.process_coq_literal(&ty.value());

        Ok(Self { ty })
    }
}

pub struct IProp(specs::IProp);

impl From<IProp> for specs::IProp {
    fn from(iprop: IProp) -> Self {
        iprop.0
    }
}

/// Parse an iProp string, e.g. `"P ∗ Q ∨ R"`
impl<'def, T: ParamLookup<'def>> parse::Parse<T> for IProp {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        let lit: parse::LitStr = stream.parse(meta)?;
        let (lit, _) = meta.process_coq_literal(&lit.value());

        Ok(Self(specs::IProp::Atom(lit)))
    }
}

/// Parse a Coq type.
pub struct RRCoqType {
    pub ty: coq::term::Type,
}
impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRCoqType {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        let ty: parse::LitStr = stream.parse(meta)?;
        let (ty, _) = meta.process_coq_literal(&ty.value());
        let ty = coq::term::Type::Literal(ty);
        Ok(Self { ty })
    }
}

/// Parse a binder declaration with an optional Coq type annotation, e.g.
/// `x : "Z"`,
/// `"y"`,
/// `z`,
/// `w : "(Z * Z)%type"`
#[derive(Clone, Eq, PartialEq, Debug)]
pub struct RRParam(coq::binder::Binder);

impl From<RRParam> for coq::binder::Binder {
    fn from(param: RRParam) -> Self {
        param.0
    }
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRParam {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        let name: IdentOrTerm = stream.parse(meta)?;
        let name = name.to_string();

        if parse::Colon::peek(stream) {
            stream.parse::<_, MToken![:]>(meta)?;
            let ty: RRCoqType = stream.parse(meta)?;
            Ok(Self(coq::binder::Binder::new(Some(name), ty.ty)))
        } else {
            Ok(Self(coq::binder::Binder::new(Some(name), coq::term::Type::Infer)))
        }
    }
}

/// Parse a list of comma-separated parameter declarations.
#[derive(Debug)]
pub struct RRParams {
    pub(crate) params: Vec<RRParam>,
}

impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRParams {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        let params: parse::Punctuated<RRParam, MToken![,]> =
            parse::Punctuated::<_, _>::parse_terminated(stream, meta)?;
        Ok(Self {
            params: params.into_iter().collect(),
        })
    }
}

pub struct CoqExportModule(coq::module::Export);

impl From<CoqExportModule> for coq::module::Export {
    fn from(path: CoqExportModule) -> Self {
        path.0
    }
}

/// Parse a `CoqModule`.
impl<U> parse::Parse<U> for CoqExportModule {
    fn parse(stream: parse::Stream, meta: &U) -> parse::Result<Self> {
        let path_or_module: parse::LitStr = stream.parse(meta)?;
        let path_or_module = path_or_module.value();

        if parse::Comma::peek(stream) {
            stream.parse::<_, MToken![,]>(meta)?;
            let module: parse::LitStr = stream.parse(meta)?;
            let module = module.value();

            Ok(Self(coq::module::Export::new(vec![module]).from(vec![path_or_module])))
        } else {
            Ok(Self(coq::module::Export::new(vec![path_or_module])))
        }
    }
}

/// Parse an assumed Coq context item, e.g.
/// ``"`{ghost_mapG Σ Z Z}"``.
#[derive(Debug)]
pub struct RRCoqContextItem {
    pub item: String,
    /// true if this should be put at the end of the dependency list, e.g. if it depends on type
    /// parameters
    pub at_end: bool,
}
impl<'def, T: ParamLookup<'def>> parse::Parse<T> for RRCoqContextItem {
    fn parse(stream: parse::Stream, meta: &T) -> parse::Result<Self> {
        let item: parse::LitStr = stream.parse(meta)?;
        let (item_str, annot_meta) = meta.process_coq_literal(&item.value());

        let at_end = !annot_meta.is_empty();

        //annot_meta.
        Ok(Self {
            item: item_str,
            at_end,
        })
    }
}

#[expect(clippy::needless_pass_by_value)]
pub fn str_err(e: parse::Error) -> String {
    format!("{:?}", e)
}

/// Handle escape sequences in the given string.
fn handle_escapes(s: &str) -> String {
    String::from(s).replace("\\\"", "\"")
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum RustPathElem {
    AssocItem(String),
}

pub type RustPath = Vec<RustPathElem>;

/// Lookup of lifetime and type parameters given their Rust source names.
pub trait ParamLookup<'def> {
    fn lookup_ty_param(&self, path: &RustPath) -> Option<specs::Type<'def>>;
    fn lookup_lft(&self, lft: &str) -> Option<&specs::Lft>;
    fn lookup_literal(&self, path: &RustPath) -> Option<&str>;

    /// Processes a literal Coq term annotated via an attribute.
    /// In particular, processes escapes `{...}` and replaces them via their interpretation, see
    /// below for supported escape sequences.
    ///
    /// Supported interpretations:
    /// - `{{...}}` is replaced by `{...}`
    /// - `{ty_of T}` is replaced by the type for the type parameter `T`
    /// - `{rt_of T}` is replaced by the refinement type of the type parameter `T`
    /// - `{xt_of T}` is replaced by the xt type of the type parameter `T`
    /// - `{st_of T}` is replaced by the syntactic type of the type parameter `T`
    /// - `{ly_of T}` is replaced by a term giving the layout of the type parameter `T`'s syntactic type
    /// - `{'a}` is replaced by a term corresponding to the lifetime parameter 'a
    ///
    /// We return the list of escaped types we depend on in order to properly track dependencies on
    /// variables.
    /// (This is needed for computing the lifetime constraints of invariant types)
    fn process_coq_literal(&self, s: &str) -> (String, specs::TypeAnnotMeta) {
        self.process_coq_literal_xt(s, false)
    }

    fn process_coq_literal_xt(&self, s: &str, rt_is_xt: bool) -> (String, specs::TypeAnnotMeta) {
        static IDENTCHARR: &str = "[_[[:alpha:]]]";
        static PREFIXR: &str = "([^{]|^)";

        let mut annot_meta = specs::TypeAnnotMeta::empty();

        let s = handle_escapes(s);

        /* regexes:
         * - '{\s*rt_of\s+([[:alpha:]])\s*}' replace by lookup of the refinement type name
         * - '{\s*st_of\s+([[:alpha:]])\s*}' replace by lookup of the syntype name
         * - '{\s*ly_of\s+([[:alpha:]])\s*}' replace by "use_layout_alg' st"
         * - '{\s*ty_of\s+([[:alpha:]])\s*}' replace by the type name
         * - '{\s*'([[:alpha:]])\s*}' replace by lookup of the lifetime name
         * - '{{(.*)}}' replace by the contents
         *
         * Note: the leading regex ([^{]|^) is supposed to rule out leading {, for the RE_LIT rule.
         */

        // compile these just once, not for every invocation of the method
        lazy_static! {
            //(::[[:alpha:]]*)?
            static ref IDENTR: String = format!(r"{IDENTCHARR}[0-9{IDENTCHARR}]*");
            static ref PATHR: String = format!(r"(({}::)*)({})", *IDENTR, *IDENTR);
            static ref RE_RT_OF: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*rt_of\s+{}\s*\}}", *PATHR)).unwrap();
            static ref RE_ST_OF: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*st_of\s+{}\s*\}}", *PATHR)).unwrap();
            static ref RE_LY_OF: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*ly_of\s+{}\s*\}}", *PATHR)).unwrap();
            static ref RE_TY_OF: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*ty_of\s+{}\s*\}}", *PATHR)).unwrap();
            static ref RE_XT_OF: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*xt_of\s+{}\s*\}}", *PATHR)).unwrap();
            static ref RE_LFT_OF: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*'({})\s*\}}", *IDENTR)).unwrap();

            static ref RE_LIT: Regex = Regex::new(&format!(r"{PREFIXR}\{{\s*{}\s*\}}", *PATHR)).unwrap();
        }

        // Parse a path to an item.
        fn parse_path(prefix: Option<regex::Match<'_>>) -> RustPath {
            let mut path = Vec::new();
            if let Some(prefix) = prefix {
                let prefix = prefix.as_str();
                for seg in prefix.split("::") {
                    if !seg.is_empty() {
                        path.push(RustPathElem::AssocItem(seg.to_owned()));
                    }
                }
            }
            path
        }

        let cs = &s;
        let cs = RE_RT_OF.replace_all(cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));

            path.push(RustPathElem::AssocItem(c[4].to_string()));

            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            if rt_is_xt {
                format!("{}(ty_xt {})", &c[1], param)
            } else {
                format!("{}{}", &c[1], &param.get_rfn_type())
            }
        });

        let cs = RE_XT_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));

            path.push(RustPathElem::AssocItem(c[4].to_string()));

            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}(ty_xt {})", &c[1], param)
        });

        let cs = RE_ST_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));

            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}(ty_syn_type {})", &c[1], param)
        });

        let cs = RE_LY_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));
            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}(use_layout_alg' (ty_syn_type {}))", &c[1], param)
        });

        let cs = RE_TY_OF.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));
            let param = self.lookup_ty_param(&path);

            let Some(param) = param else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&param);
            format!("{}{}", &c[1], param)
        });

        let cs = RE_LFT_OF.replace_all(&cs, |c: &Captures<'_>| {
            let t = &c[2];
            let lft = self.lookup_lft(t);

            let Some(lft) = lft else {
                return "ERR".to_owned();
            };

            annot_meta.add_lft(lft);
            format!("{}{}", &c[1], lft)
        });

        let cs = RE_LIT.replace_all(&cs, |c: &Captures<'_>| {
            let mut path = parse_path(c.get(2));
            path.push(RustPathElem::AssocItem(c[4].to_string()));

            trace!("looking up literal {path:?}");

            // first lookup literals
            let lit = self.lookup_literal(&path);

            if let Some(lit) = lit {
                return format!("{}{}", &c[1], lit);
            }

            // else interpret it as ty_of
            let ty = self.lookup_ty_param(&path);

            let Some(ty) = ty else {
                return "ERR".to_owned();
            };

            annot_meta.add_type(&ty);
            format!("{}{}", &c[1], ty)
        });

        let cs = cs.replace("{{", "{");
        let cs = cs.replace("}}", "}");

        (cs, annot_meta)
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::{ParamLookup, RustPath, RustPathElem};

    #[derive(Default)]
    struct TestScope {
        /// conversely, map the declaration name of a lifetime to an index
        pub lft_names: HashMap<String, radium::Lft>,
        /// map types to their index
        pub ty_names: HashMap<String, radium::LiteralTyParam>,

        pub assoc_names: HashMap<RustPath, radium::LiteralTyParam>,

        pub literals: HashMap<RustPath, String>,
    }

    impl<'def> ParamLookup<'def> for TestScope {
        fn lookup_ty_param(&self, path: &RustPath) -> Option<radium::Type<'def>> {
            if path.len() == 1 {
                let RustPathElem::AssocItem(it) = &path[0];
                if let Some(n) = self.ty_names.get(it) {
                    return Some(radium::Type::LiteralParam(n.to_owned()));
                }
            }

            if let Some(n) = self.assoc_names.get(path) {
                return Some(radium::Type::LiteralParam(n.to_owned()));
            }
            None
        }

        fn lookup_lft(&self, lft: &str) -> Option<&radium::Lft> {
            self.lft_names.get(lft)
        }

        fn lookup_literal(&self, path: &RustPath) -> Option<&str> {
            self.literals.get(path).map(String::as_str)
        }
    }

    #[test]
    fn test_literal1() {
        let lit = "{rt_of T} * {rt_of T}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("T".to_owned(), radium::LiteralTyParam::new("T", "T"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "T_rt * T_rt");
    }

    #[test]
    fn test_literal2() {
        let lit = "{ty_of T} * {ty_of T}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("T".to_owned(), radium::LiteralTyParam::new("T", "T"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "T_ty * T_ty");
    }

    #[test]
    fn test_literal3() {
        let lit = "{rt_of Self} * {rt_of Self}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Self".to_owned(), radium::LiteralTyParam::new("Self", "Self"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "Self_rt * Self_rt");
    }

    #[test]
    fn test_literal4() {
        let lit = "{{rt_of Bla}}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Self".to_owned(), radium::LiteralTyParam::new("Self", "Self"));

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "{rt_of Bla}");
    }

    #[test]
    fn test_assoc_1() {
        let lit = "{rt_of Bla::Blub}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Bla".to_owned(), radium::LiteralTyParam::new("Bla", "Bla"));
        scope.assoc_names.insert(
            vec![RustPathElem::AssocItem("Bla".to_owned()), RustPathElem::AssocItem("Blub".to_owned())],
            radium::LiteralTyParam::new("Bla_Blub", "Bla_Blub"),
        );

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "Bla_Blub_rt");
    }

    #[test]
    fn test_assoc_2() {
        let lit = "{rt_of Bla::Bla::Blub}";
        let mut scope = TestScope::default();
        scope.ty_names.insert("Bla".to_owned(), radium::LiteralTyParam::new("Bla", "Bla"));
        scope.assoc_names.insert(
            vec![
                RustPathElem::AssocItem("Bla".to_owned()),
                RustPathElem::AssocItem("Bla".to_owned()),
                RustPathElem::AssocItem("Blub".to_owned()),
            ],
            radium::LiteralTyParam::new("Bla_Blub", "Bla_Blub"),
        );

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "Bla_Blub_rt");
    }

    #[test]
    fn test_lit_1() {
        let lit = "{Size} 4";
        let mut scope = TestScope::default();
        scope
            .literals
            .insert(vec![RustPathElem::AssocItem("Size".to_owned())], "(trait_attrs).(size)".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(trait_attrs).(size) 4");
    }

    #[test]
    fn test_lit_2() {
        let lit = "{Size_bla} 4";
        let mut scope = TestScope::default();
        scope
            .literals
            .insert(vec![RustPathElem::AssocItem("Size_bla".to_owned())], "(trait_attrs).(size)".to_owned());

        let (res, _) = scope.process_coq_literal(lit);
        assert_eq!(res, "(trait_attrs).(size) 4");
    }
}
