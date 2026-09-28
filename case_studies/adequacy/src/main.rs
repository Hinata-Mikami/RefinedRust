#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]



#[rr::verify]
fn main() {
    callee(42);
}

#[rr::verify]
#[rr::may_unwind_if("DropGlue_DropGlueUnwind DropGlue_T_spec_attrs")]
fn callee<T>(x: T) {
    let x = (x, 2);
}
