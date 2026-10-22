#![feature(register_tool)]
#![feature(custom_inner_attributes)]
#![register_tool(rr)]
#![rr::package("panic_abort")]

#[rr::may_unwind_if("True")]
#[rr::use_panic_abort]
#[rr::verify]
pub fn checked_div(x: u32, y: u32) -> u32 {
    x / y
}

#[rr::may_unwind_if("True")]
#[rr::verify]
pub fn checked_rem(x: u32, y: u32) -> u32 {
    x % y
}

#[rr::may_unwind_if("True")]
#[rr::verify]
pub fn direct_panic() {
    panic!()
}
