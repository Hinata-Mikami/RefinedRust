#![allow(dead_code)]

fn vec_iter<T>(x: &Vec<T>) -> core::slice::Iter<'_, T> {
    x.iter()
}

fn insert_unique<T: Eq>(vec: &mut Vec<T>, elem: T) {
    for e in vec_iter(vec) {
        if e == &elem {
            return;
        }
    }

    vec.push(elem);
}

#[mapper::run]
#[mapper::points]
pub fn inserted_return_after_folded_statement<T: Eq + Copy>(input: &Vec<T>) -> Vec<T> {
    let mut unique = Vec::new();

    for elem in vec_iter(input) {
        insert_unique(&mut unique, *elem);
    }

    unique
}
