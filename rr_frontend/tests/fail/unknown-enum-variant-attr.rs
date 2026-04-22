//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]
#![allow(dead_code)]

enum Flag {
    #[rr::mystery]
    On,
}

#[rr::verify]
fn use_flag(flag: Flag) {
    let _ = flag;
}
