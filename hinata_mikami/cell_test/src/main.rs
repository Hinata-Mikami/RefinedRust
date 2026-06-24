#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_camel_case_types)]

#[rr::refined_by("(v, next)" : "(Z * loc)")]
struct Cell {
    #[rr::field("v")]
    value: i32,

    #[rr::field("next")]
    next: *mut Cell,
}


//_ : cell ◁ₗ[ π, Owned] # -[# v; # n] @
// StructLtype +[◁ int i32; ◁ alias_ptr_t] Cell_sls

// #[rr::params("cell" : "loc", "v" : "Z", "n" : "loc")]
// #[rr::args("cell")]
// #[rr::requires(#type "cell" : "(v, n)" @ "(Cell_inv_t <INST!>)")]
// #[rr::ensures(#type "cell" : "(v, n)" @ "(Cell_inv_t <INST!>)")]
// #[rr::returns("v")]
// unsafe fn read_value_1(cell: *mut Cell) -> i32 {
//     unsafe { (*cell).value }
// }

// ok
#[rr::params("cell" : "loc", "v" : "Z", "n" : "loc")]
#[rr::args("cell")]
#[rr::requires(#type "cell" : "-[#v; #n]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "cell" : "-[#v; #n]" @ "(Cell_ty <INST!>)")]
#[rr::returns("v")]
unsafe fn read_value_2(cell: *mut Cell) -> i32 {
    unsafe { (*cell).value }
}

//ok 
#[rr::params("cell" : "loc", "v" : "Z", "n" : "loc")]
#[rr::args("cell")]
#[rr::requires(#type "cell" : "-[#v; #n]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "cell" : "-[#v; #n]" @ "(Cell_ty <INST!>)")]
#[rr::returns("n")]
pub unsafe fn read_next(cell: *mut Cell) -> *mut Cell {
    unsafe { (*cell).next }
}

#[rr::params(
    "cell" : "loc",
    "next" : "loc",
    "v" : "Z",
    "next_v" : "Z",
    "next_next" : "loc"
)]
#[rr::args("cell")]
#[rr::requires("cell ≠ next")]
#[rr::requires("next.(loc_a) ≠ 0")]
#[rr::requires(#type "cell" : "-[#v; #next]" @ "(Cell_ty <INST!>)")]
#[rr::requires(#type "next" : "-[#next_v; #next_next]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "cell" : "-[#v; #next]" @ "(Cell_ty <INST!>)")]
#[rr::ensures(#type "next" : "-[#next_v; #next_next]" @ "(Cell_ty <INST!>)")]
#[rr::returns("next_v")]
pub unsafe fn read_next_value(cell: *mut Cell) -> i32 {
    let next = unsafe { (*cell).next };
    unsafe { (*next).value }
}

fn main() {

}
