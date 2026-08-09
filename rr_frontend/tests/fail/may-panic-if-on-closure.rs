//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]
#![feature(stmt_expr_attributes)]

fn main() {
    let _f = #[rr::may_panic_if("True", "False")] || {};
}
