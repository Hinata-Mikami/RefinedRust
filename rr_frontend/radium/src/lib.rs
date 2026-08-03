#![feature(box_patterns)]
#![feature(stmt_expr_attributes)]
#![feature(iterator_try_collect)]

pub mod code;
pub mod coq;
pub mod lang;
pub mod model;
pub mod specs;

pub(crate) const BASE_INDENT: &str = "  ";

fn make_indent(i: usize) -> String {
    " ".repeat(i)
}

/// Extend the `core::fmt::Display` trait to display a collection separated by a separator.
///
/// The macro can take an optional third argument to customise the format string (default: `"{}"`).
/// This third argument can also be a closure that takes an element from the collection and returns the
/// formatted string.
#[macro_export]
macro_rules! fmt_list {
    ($collection:expr, $separator:expr) => {
        $crate::fmt_list!($collection, $separator, "{}")
    };
    ($collection:expr, $separator:expr, $pattern:literal) => {
        $crate::fmt_list!($collection, $separator, |e| format!($pattern, e))
    };
    ($collection:expr, $separator:expr, $fmt:expr) => {
        #[allow(clippy::allow_attributes)]
        $collection.into_iter().map($fmt).collect::<Vec<_>>().join($separator)
    };
}

/// Extend the `String::push_str` method to push a collection separated by a separator.
///
/// The macro can take an optional fourth argument to customise the format string (default: `"{}"`).
/// This fourth argument can also be a closure that takes an element from the collection and returns the
/// formatted string.
#[macro_export]
macro_rules! push_str_list {
    ($s:ident, $collection:expr, $separator:expr) => {
        $crate::push_str_list!($s, $collection, $separator, "{}")
    };
    ($s:ident, $collection:expr, $separator:expr, $pattern:literal) => {
        $crate::push_str_list!($s, $collection, $separator, |e| format!($pattern, e))
    };
    ($s:ident, $collection:expr, $separator:expr, $fmt:expr) => {
        $s.push_str(&$crate::fmt_list!($collection, $separator, $fmt))
    };
}

/// Extend the `write!` macro to write a collection separated by a separator.
///
/// The macro can take an optional fourth argument to customise the format string (default: `"{}"`).
/// This fourth argument can also be a closure that takes an element from the collection and returns the
/// formatted string.
#[macro_export]
macro_rules! write_list {
    ($f:ident, $collection:expr, $separator:expr) => {
        $crate::write_list!($f, $collection, $separator, "{}")
    };
    ($f:ident, $collection:expr, $separator:expr, $pattern:literal) => {
        $crate::write_list!($f, $collection, $separator, |e| format!($pattern, e))
    };
    ($f:ident, $collection:expr, $separator:expr, $fmt:expr) => {
        write!($f, "{}", $crate::fmt_list!($collection, $separator, $fmt))
    };
}

#[cfg(test)]
#[expect(clippy::inline_modules)]
mod tests {
    use std::fmt::Write as _;

    use crate::{code, lang};

    #[test]
    fn fmt_list_default() {
        let out = fmt_list!(vec!["10", "20"], "; ");
        assert_eq!(out, "10; 20");
    }

    #[test]
    fn fmt_list_pattern() {
        let out = fmt_list!(vec!["10", "20"], "; ", "'{}'");
        assert_eq!(out, "'10'; '20'");
    }

    #[test]
    fn fmt_list_format() {
        let out = fmt_list!(vec![("x", "10"), ("y", "20")], "; ", |(l, v)| format!("{l}: {v}"));
        assert_eq!(out, "x: 10; y: 20");
    }

    #[test]
    fn push_str_list_default() {
        let mut out = String::new();
        push_str_list!(out, vec!["10", "20"], "; ");
        assert_eq!(out, "10; 20");
    }

    #[test]
    fn push_str_list_pattern() {
        let mut out = String::new();
        push_str_list!(out, vec!["10", "20"], "; ", "'{}'");
        assert_eq!(out, "'10'; '20'");
    }

    #[test]
    fn push_str_list_format() {
        let mut out = String::new();
        push_str_list!(out, vec![("x", "10"), ("y", "20")], "; ", |(l, v)| format!("{l}: {v}"));
        assert_eq!(out, "x: 10; y: 20");
    }

    #[test]
    fn write_list_default() {
        let mut out = String::new();
        write_list!(out, vec!["10", "20"], "; ").unwrap();
        assert_eq!(out, "10; 20");
    }

    #[test]
    fn write_list_pattern() {
        let mut out = String::new();
        write_list!(out, vec!["10", "20"], "; ", "'{}'").unwrap();
        assert_eq!(out, "'10'; '20'");
    }

    #[test]
    fn write_list_format() {
        let mut out = String::new();
        write_list!(out, vec![("x", "10"), ("y", "20")], "; ", |(l, v)| format!("{l}: {v}")).unwrap();
        assert_eq!(out, "x: 10; y: 20");
    }

    #[test]
    fn call_statement_destinations() {
        let call = |destination| code::Stmt::Call {
            f: code::Expr::Literal(code::Literal::Loc("f".to_owned())),
            lfts: Vec::new(),
            tys: Vec::new(),
            args: Vec::new(),
            destination,
            normal: Box::new(code::Stmt::GotoBlock(1)),
            unwind: Box::new(code::Stmt::Stuck),
        };
        let destination = code::CallDestination {
            order: lang::Order::Na1,
            ot: lang::OpType::Unit,
            destination: code::Expr::Var("ret".to_owned()),
        };

        let with_destination = call(Some(destination)).to_string();
        assert!(
            with_destination.contains("(Some (Na1Ord, StructOp unit_sl [], \"ret\"))"),
            "{with_destination:?}"
        );
        assert!(with_destination.contains("Goto \"_bb1\""));
        assert!(with_destination.ends_with("( StuckS)"));

        let without_destination = call(None).to_string();
        assert!(without_destination.contains("[@{expr} ] None"));
        assert!(without_destination.ends_with("( StuckS)"));
    }
}
