//@rustc-env: RR_NO_ASSUMPTION=true

#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::only_spec]
fn main() {
    //~^ ERROR: [RefinedRust] No assumption is allowed, but this function is annotated with `#[rr::only_spec]`
}
