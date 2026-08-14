#![feature(custom_inner_attributes)]
#![feature(register_tool)]
#![register_tool(rr)]
#![rr::package("projection_deps")]

pub trait Assoc {
    type Output;
}

struct Wrapper<T>(T);

impl<T> Assoc for Wrapper<T> {
    type Output = Option<T>;
}

#[rr::only_spec]
fn consume<T>(_value: T) {}

#[rr::verify]
pub fn call<T>(value: Option<T>) {
    consume::<<Wrapper<T> as Assoc>::Output>(value);
}

#[rr::verify]
pub fn call_symbolic<T: Assoc>(value: T::Output) {
    consume::<T::Output>(value);
}
