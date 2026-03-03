#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::include("stdlib")]
// #![rr::include("vec")]

#[rr::params("v")]
#[rr::args("v")]
#[rr::observe("v.ghost" :  "v.cur ++ [42]")] // 名前一応確認
// precondition で長さに関する条件を要求
fn vec_add_42(v: &mut Vec<i32>) {
    // Rust関数自体をif文でオーバーフローしないように修正
    v.push(42);
}

// 現環境　保存しておく？

#[rr::verify]
fn main() {
    let mut v = Vec::new();
    vec_add_42(&mut v);

    assert!(v[0] == 42);
}
