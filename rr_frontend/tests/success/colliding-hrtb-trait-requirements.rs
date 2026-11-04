//@check-pass

#![feature(register_tool)]
#![register_tool(rr)]
#![allow(dead_code)]

trait WithAssoc<'a, 'b> {
    type Assoc;
}

#[rr::verify]
fn use_independent_lifetimes<'x, 'y, T>(
    _left: &'x u8,
    _right: &'y u8,
    _value: <T as WithAssoc<'x, 'y>>::Assoc,
) where
    // Both requirements have the same region-erased lookup key, but only the second permits
    // `x` and `y` to be instantiated with distinct regions.
    for<'a> T: WithAssoc<'a, 'a>,
    for<'a, 'b> T: WithAssoc<'a, 'b>,
{
}
