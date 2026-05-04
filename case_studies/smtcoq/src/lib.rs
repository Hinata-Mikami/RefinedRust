#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(unused)]

#![rr::package("smtcoq")]
#![rr::include("option")]

#[rr::refined_by("x" : "Z")]
#[rr::invariant("Zeven x")]
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}


impl EvenInt {
    /// Create a new even integer.
    #[rr::requires("Zeven x")]
    #[rr::returns("x")]
    pub unsafe fn new(x: i32) -> Self {
        Self {num: x}
    }

    /// Add another even integer.
    #[rr::requires("(self.cur + other)%Z ∈ i32")]
    #[rr::observe("self.ghost": "self.cur + other")]
    pub fn add_even(&mut self, other: &EvenInt) {
        self.num += other.num;
    }
}
