
#[rr::verify]
fn test1(x: &i32) {

}

#[rr::verify]
fn test2<'a, 'b: 'a>(x: &'a i32, y: &'b i32) {

}

#[rr::verify]
fn test3<'a, 'b: 'a, 'c : 'b>(x: &'a i32, y: &'b i32, z: &'c i32) {

}

#[rr::verify]
fn test4<'a, 'b: 'a, 'c>(x: &'a i32, y: &'b (&'c i32)) {

}

#[rr::verify]
fn test5<'a, T>(x: &'a T) {

}
