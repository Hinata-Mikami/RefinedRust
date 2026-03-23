#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::include("stdlib")]



use std::ptr;

/* ok */
#[rr::params("p", "v" : "Z")]
#[rr::args("p")]
#[rr::requires(#type "p" : "v" @ "int i32")]
#[rr::returns("p")]
#[rr::ensures(#type "p" : "v" @ "int i32")]
unsafe fn id(p: *mut i32) -> *mut i32 {
    p
}

#[rr::refined_by("v")]
struct Cell {
    #[rr::field("v")]
    value: i32,
}

/* ok, but... */
/* v の型は "(Cell_inv_t <INST!>)" と書きたかったが */
/* spec では "Cell_inv_t" が生成されない */
#[rr::params("p", "v")]
#[rr::args("p")]
#[rr::requires(#type "p" : "v" @ "int i32")]
#[rr::returns("p")]
#[rr::ensures(#type "p" : "v" @ "int i32")]
unsafe fn id_Cell(p: *mut Cell) -> *mut Cell {
    p
}

#[rr::refined_by("(v, l)" : "(Z * loc)")]
struct Node{
    #[rr::field("v")]
    value: i32,
    #[rr::field("l")]
    next: *mut Node,
}

impl Node {
    /* ok */ 
    #[rr::params("p", "v", "l")]
    #[rr::args("p")]
    #[rr::requires(#type "p" : "(v, l)" @ "(Node_inv_t <INST!>)")]
    #[rr::ensures(#type "p" : "(v, l)" @ "(Node_inv_t <INST!>)")]
    #[rr::returns("p")]
    unsafe fn id_Node(p: *mut Node) -> *mut Node {
        p
    }

    /* ok */
    #[rr::params("p", "v", "l", "n")]
    #[rr::args("p", "n")]
    #[rr::requires(#type "p" : "(v, l)" @ "(Node_inv_t <INST!>)")]
    #[rr::ensures(#iris "p ◁ₗ[π, Owned] # -[# v; # n] @ StructLtype +[◁ int i32; ◁ alias_ptr_t] Node_sls")]
    #[rr::returns("()")]
    unsafe fn set_next(node: *mut Node, next: *mut Node) {
            (*node).next = next;
    }
}


fn main() {
}
