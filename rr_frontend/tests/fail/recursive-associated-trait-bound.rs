//@stderr-only

#![feature(register_tool)]
#![register_tool(rr)]
#![allow(dead_code)]

trait Recursive {
    type Next: Recursive;
}

fn main() {}
