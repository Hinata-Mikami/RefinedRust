#![allow(dead_code)]

struct Payload {
    value: u32,
}

struct Holder {
    payload: Box<Payload>,
}

#[mapper::run]
fn shared_read(input: &Box<Payload>) -> u32 {
    input.value
}

#[mapper::run]
fn mutable_write(input: &mut Box<Payload>) {
    input.value = 7;
}

#[mapper::run]
fn projected_read(holder: &Holder) -> u32 {
    holder.payload.value
}

fn consume(_: u32) {}

#[mapper::run]
fn terminator_read(input: &Box<u32>) {
    consume(**input);
}

#[mapper::run]
fn nested_read(input: &Box<Box<u32>>) -> u32 {
    ***input
}
