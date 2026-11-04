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

#[rr::verify]
pub fn nested_shared_reborrow<'a, 'b>(value: &'b &'a u32, _use_b: &'b ()) -> &'a u32 {
    &**value
}

#[rr::verify]
pub fn nested_mut_reborrow<'a, 'b>(value: &'b &'a mut u32, _use_a: &'a ()) -> &'b u32 {
    &**value
}

pub struct RawMut(*mut u32);

impl RawMut {
    #[rr::verify]
    pub unsafe fn choose_mut_lifetime<'a>(&mut self) -> &'a mut u32 {
        unsafe { &mut *self.0 }
    }
}

#[rr::verify]
pub unsafe fn call_choose_mut_lifetime(ptr: &mut RawMut) {
    let value = unsafe { ptr.choose_mut_lifetime() };
    *value = 0;
}
