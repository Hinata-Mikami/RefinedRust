#![feature(register_tool)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![register_tool(rr)]
#![rr::package("panic_abort")]
#![rr::include("closures")]

#[rr::may_panic_if("True")]
#[rr::use_panic_abort]
#[rr::verify]
pub fn checked_div(x: u32, y: u32) -> u32 {
    x / y
}

#[rr::may_panic_if("True")]
#[rr::verify]
pub fn checked_rem(x: u32, y: u32) -> u32 {
    x % y
}

#[rr::may_panic_if("True")]
#[rr::verify]
pub fn direct_panic() {
    panic!()
}

#[rr::verify]
pub fn call_closure() {
    let closure = #[rr::use_panic_abort] #[rr::verify] || {};
    closure();
}

#[rr::verify]
pub fn call_unannotated_closure() {
    let closure = #[rr::verify] || {};
    closure();
}
