#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![register_tool(rr)]
#![rr::package("loan_supports")]

struct Guard<'a>(&'a mut u32);

#[rr::verify]
pub fn reborrow_in_loop(value: &mut u32) {
    let guard = Guard(value);
    while *guard.0 > 0 {
        let borrowed = &mut *guard.0;
        *borrowed -= 1;
    }
}
