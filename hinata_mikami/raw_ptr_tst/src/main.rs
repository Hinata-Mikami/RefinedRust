#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::include("stdlib")]

#[rr::exists("x")]
#[rr::returns("x")]
// #[rr::ensures(#type "x" : "[]" @ "list Z")]
fn raw_null() -> *mut i32 {
    std::ptr::null_mut()
}

fn main() {

}
