#![feature(register_tool)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![register_tool(rr)]
#![rr::package("panic_abort")]
#![rr::include("closures")]

#[rr::may_panic_if("True")]
#[rr::verify]
pub fn checked_div(x: u32, y: u32) -> u32 {
    x / y
}

#[rr::verify]
pub fn call_closure() {
    let closure = #[rr::verify] || {};
    closure();
}
