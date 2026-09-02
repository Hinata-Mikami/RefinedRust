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

#[rr::exists("Observe" : "{xt_of Self} → bool")]
pub trait ItemSource {
    type Item;

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("{Observe} x")]
    fn observe(self) -> bool;
}

#[rr::exists("Enabled" : "{xt_of Self} → Prop")]
pub trait IntoSource {
    type Item;
    type Source: ItemSource<Item = Self::Item>;
}

#[rr::only_spec]
fn consume_source<T: IntoSource>() {}

#[rr::verify]
pub fn call_with_associated_bound<T: IntoSource>(value: <T::Source as ItemSource>::Item) {
    consume::<T::Item>(value);
}

#[rr::verify]
pub fn call_with_associated_bound_attrs<T: IntoSource>() {
    consume_source::<T>();
}

pub trait NestedSource {
    type Inner: IntoSource;
}

#[rr::verify]
pub fn call_with_nested_associated_bound<T: NestedSource>(
    value: <<T::Inner as IntoSource>::Source as ItemSource>::Item,
) {
    consume::<<T::Inner as IntoSource>::Item>(value);
}
