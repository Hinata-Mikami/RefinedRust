#![allow(dead_code)]

fn make_ptr<T>() -> *mut T {
    std::ptr::null_mut()
}

#[mapper::run]
pub fn mut_to_const_ptr_cast<T>() -> *const T {
    let ptr = make_ptr::<T>();
    ptr as *const T
}
