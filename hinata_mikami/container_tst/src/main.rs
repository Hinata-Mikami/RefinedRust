#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]

use std::ptr;

#[rr::refined_by("(v, n)" : "(Z * loc)")]
struct Node {
    #[rr::field("v")]
    value: i32,

    #[rr::field("n")]
    next: *mut Node,
}


// #[rr::refined_by("h" : "heap_rfn")]
// #[rr::invariant(#iris "
//   ⌜NoDup (heap_locs h)⌝ ∗
//   ⌜∀ p r,
//       heap_nodes h !! p = Some r →
//       node_next r = NULL_loc ∨ node_next r ∈ heap_locs h⌝ ∗
//   ([∗ list] p ∈ heap_locs h,
//     ∃ r,
//       ⌜heap_nodes h !! p = Some r⌝ ∗
//       guarded true
//         (p ◁ₗ[π, Owned]
//           # -[#(node_val r); #(node_next r)]
//           @ (◁ (Node_inv_t <INST!>))))
// ")]
// struct Heap {
//     #[rr::field("<$#> (heap_locs h)")]
//     all_nodes: Vec<*mut Node>,
// }


impl Node {
    fn new(value: i32) -> Self {
    }

    fn alloc(value: i32) -> *mut Node {

    }

    fn set_next(&mut self, node : *mut Node, next: *mut Node) {

    }
}


fn main(){

}