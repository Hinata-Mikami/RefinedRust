#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(unused)]

#![rr::include("stdlib")]


#[rr::verify]
fn main() {
    callee(42);
}

#[rr::verify]
#[rr::may_unwind_if("DropGlue_DropGlueUnwind DropGlue_T_spec_attrs")]
fn callee<T>(x: T) {
    let x = (x, 2);
}





trait Iter {
    type Item;
    #[rr::verify]
    #[rr::may_unwind_if("True")]
    #[rr::exists("x" : "{xt_of Self}")]
    #[rr::observe("self.ghost": "$# x")]
    #[rr::ensures_on_unwind(#iris "∃ (x : RT_xt Self_rt), Obs self.ghost ($# x)")]
    fn next(&mut self) -> Option<Self::Item>;
}

impl<T> Iter for &T {
    type Item = ();
    #[rr::default_spec]
    fn next(&mut self) -> Option<Self::Item> {
        None
    }
}

#[rr::verify]
#[rr::may_unwind_if("True")]
fn foo<T: Iter>(mut x: T) {
    x.next();
}

#[rr::verify]
#[rr::may_unwind_if("True")]
fn call_foo<W>(x: W, y: W) {
    foo(&x); 
    foo(&y);
}

#[rr::verify]
#[rr::may_unwind_if("True")]
fn main2() {
    call_foo(42, 1337);
}

// A recursive edge must carry an abstract linking condition, just like other calls.
#[rr::verify]
fn recurse() {
    recurse();
}

#[rr::refined_by("pending" : "bool")]
struct One {
    #[rr::field("#pending")]
    pending: bool,
}

#[rr::instantiate("Params" := "unit")]
#[rr::instantiate("Inv" := "λ π _ pending, True%I")]
#[rr::instantiate("Next" := "λ π _ pending result pending', ⌜pending' = false ∧ result = (if pending then Some 42 else None)⌝%I")]
impl std::iter::Iterator for One {
    type Item = i32;

    #[rr::default_spec]
    fn next(&mut self) -> Option<i32> {
        if self.pending {
            self.pending = false;
            Some(42)
        } else {
            None
        }
    }
}

#[rr::verify]
fn main_map() {
    let mut iter = One { pending: true }.map(
        #[rr::returns("x")]
        |x: i32| x,
    );
    let first = iter.next();
    let second = iter.next();
}
