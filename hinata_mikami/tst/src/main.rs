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

#[rr::refined_by("value")]
#[rr::invariant("(value = 1) ∨ (value = -1)")]
struct PlusOrMinus {
    #[rr::field("value")]
    value: i32,
}

impl PlusOrMinus {
    #[rr::params("value":"Z")]
    #[rr::args("value")]
    fn new(value: i32) -> Self {
        if value >= 0 {
            Self { value : 1 }
        } else {
            Self { value: -1 }
        }
    }
}

// ok
#[rr::refined_by("p" : "loc")]
#[rr::invariant("p = (Loc ProvNone 0)")]
struct NullPtr{
    #[rr::field("p")]
    ptr : *mut NullPtr,
}

// ok
impl NullPtr {
    #[rr::exists("p")]
    #[rr::returns("p")]
    #[rr::ensures("p = (Loc ProvNone 0)")]
    fn new() -> Self {
        Self { ptr: std::ptr::null_mut() }
    }
}

// ok
// #[rr::refined_by("p" : "loc")]
#[rr::refined_by("(p, v)" : "(loc * Z)")]
#[rr::exists("v")]
#[rr::invariant(#type "p" : "v" @ "int i32")]
struct IntPtr{
    #[rr::field("p")]
    ptr : *mut i32,
}

impl IntPtr {
    // ok
    #[rr::params("value" : "Z")]
    #[rr::args("value")]
    #[rr::exists("p" : "loc")]
    #[rr::returns("(p, value)")]
    // ensuresを削除
    fn new(val: i32) -> Self {
            let boxed = Box::new(val);
            Self {
                ptr: Box::into_raw(boxed),
            }
    }
}


#[rr::refined_by("(p, v)" : "(loc * Z)")]
// #[rr::exists("v")]
#[rr::invariant(#iris "(
    ⌜p = (Loc ProvNone 0)⌝
    ∨
    (p ◁ₗ[π, Owned] #(v) @ (◁ int i32))
  )")]
struct NullOrIntPtr{
    #[rr::field("p")]
    ptr : *mut i32,
}

impl NullOrIntPtr {
    #[rr::returns("((Loc ProvNone 0), Null)")]
    fn new() -> Self {
        Self { ptr: std::ptr::null_mut() }
    }
}

#[rr::returns("()")]
fn main() {
}