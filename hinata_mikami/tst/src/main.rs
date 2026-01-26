#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

// all OK

#[rr::params("x")]
#[rr::args("x")]        // x : int I32
#[rr::returns("x")]
fn id_int(x : i32) -> i32{
    x
}

#[rr::params("x")]
#[rr::args("x")]        // x : T_ty
#[rr::returns("x")]
fn id<T>(x : T) -> T{
    x
}

// sub functions
#[rr::only_spec]
#[rr::params("x")]      // x : Int I32
#[rr::args("x" @ "int I32")]
#[rr::returns("x" @ "(box (int I32))")]
fn box_new(t: i32) -> Box<i32> {
    Box::new(t)
}

#[rr::only_spec]
#[rr::params("x")]
#[rr::args("x" @ "(box (int I32))")]    // x : (box (int I32))
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "x" @ "int I32")] 
fn box_into_raw(b: Box<i32>) -> *mut i32 {
    Box::into_raw(b)
}

#[rr::only_spec]
#[rr::params("l", "x")]
#[rr::args("l")]
#[rr::requires(#type "l" : "x" @ "int i32")] 
#[rr::returns("x" @ "(box (int I32))")]
unsafe fn box_from_raw(ptr: *mut i32) -> Box<i32> {
    Box::from_raw(ptr)
}


#[rr::params("x")]
#[rr::args("x" @ "int i32")]
#[rr::exists("l")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "x" @ "int i32")] 
fn new(data: i32) -> *mut i32 {

        let inner = data;
        
        let boxed = box_new(inner);

        let ptr = box_into_raw(boxed);

        return ptr;
    }

#[rr::returns("()")]
fn main(){

    let ptr = new(10);
    unsafe {
        let _ = box_from_raw(ptr);
    }

}
