#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]


#[rr::params("l": "loc", "v": "Z", "v'": "Z")] // specify Coq-level specification parameters
#[rr::args("l", "v'" @ "int i32")]             // specify argument refinements/types
// Type assignments for locations/places can be specified by the `#type "l" : "r" @ "ty"` template, 
// specifying that `l` is an owned pointer storing a value of type `r @ ty`.
#[rr::requires(#type "l" : "v" @ "int i32")]   // specify a precondition
#[rr::ensures(#type "l" : "v'" @ "int i32")]   // specify a postcondition
unsafe fn write_raw(ptr: *mut i32, val: i32) {
    *ptr = val;
}

#[rr::returns("()")]
fn logic1(){
    let mut x = 0;
    
    let p: *mut i32 = &mut x;
    unsafe { write_raw(p, 1); }

    assert!(x == 1);    
}

#[rr::returns("()")]
fn logic2(){
    let mut x = 0;
    
    let p: *mut i32 = &mut x;
    let p_alias: *mut i32 = p;
    unsafe { write_raw(p_alias, 2); }

    assert!(x == 2);
}

fn main() {

    logic1();
    logic2();
    
}

