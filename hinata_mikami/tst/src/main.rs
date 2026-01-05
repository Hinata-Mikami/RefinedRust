#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

// fail
#[rr::returns("()")]
fn main() {
    let mut x = 0;
    let ptr : *mut i32 = &mut x; // これがだめ
}
