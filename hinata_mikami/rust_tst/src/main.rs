#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_camel_case_types)]
#![allow(unsafe_op_in_unsafe_fn)]

#![feature(stmt_expr_attributes)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]

#![rr::import("hinata_mikami.extra_proofs.gc", "heap_lemmas")]
#![rr::import("hinata_mikami.extra_proofs.gc", "gc_defs")]
#![rr::import("hinata_mikami.extra_proofs.gc", "sweep_contract")]


use std::ptr;


use wrappers::*;

mod wrappers {
    #[rr::only_spec]
    #[rr::requires("index < length x")]
    #[rr::returns("x !!! Z.to_nat index")]
    pub fn vec_index<T>(x: &Vec<T>, index: usize) -> &T {
        &x[index]
    }

}

struct Node {
    value: i32,
    next: *mut Node,
    marked: bool,
}


impl Node{
    #[rr::params("node" : "loc", "next" : "loc", "v" : "Z", "old_next" : "loc", "m" : "bool")]
    #[rr::args("node", "next")]
    #[rr::requires(#type "node" : "-[#v; #old_next; #m]" @ "(Node_ty <INST!>)")]
    #[rr::ensures(#type "node" : "-[#v; #next; #m]" @ "(Node_ty <INST!>)")]
    #[rr::returns("()")]
    unsafe fn set_next(node: *mut Node, next: *mut Node) {
            (*node).next = next;
    }


    unsafe fn set_marked(node: *mut Node, new_m: bool) {
        (*node).marked = new_m;
    }

}

struct Heap {
    all_nodes: Vec<*mut Node>,
}


fn make_node(v: i32) -> *mut Node {
    let node = Box::new(Node {
        value: v,
        next: ptr::null_mut(),
        marked: false,
    });
    Box::into_raw(node)
}

unsafe fn read_next_value(node: *mut Node) -> i32 {
    let next = unsafe { (*node).next };
    unsafe { (*next).value }
}



impl Heap {
    fn new() -> Self {
        Heap {
            all_nodes: Vec::new(),
        }
    }


    fn alloc(&mut self, value: i32) -> *mut Node {
        let ptr = make_node(value);
        self.all_nodes.push(ptr);
        ptr
    }


    unsafe fn mark_one(&mut self) {
        let node = *vec_index(&self.all_nodes, 0);
        Node::set_marked(node, true);
    }


    unsafe fn mark_from(&mut self, start_node: *mut Node) {

        // 一時的な proof-debug 用
        let _dummy = *vec_index(&self.all_nodes, 0);

        if (*start_node).marked {
            return;
        }

        let next = (*start_node).next;

        Node::set_marked(start_node, true);

        if !next.is_null() {
            self.mark_from(next);
        }

    }


    unsafe fn mark(&mut self) {
        let root = *vec_index(&self.all_nodes, 0);
        self.mark_from(root);
    }


    unsafe fn sweep(&mut self) {
        let nodes = &mut self.all_nodes;
        let mut i = nodes.len();

        while i > 0 {

            i -= 1;

            let node_ptr = *vec_index(nodes, i);

            if (*node_ptr).marked {

                Node::set_marked(node_ptr, false);
            
            } else {

                let _ = nodes.remove(i);
                let _ = Box::from_raw(node_ptr);
            }
        }
    }


    /* マークアンドスイープGC */
    unsafe fn collect(&mut self) {
        println!("------------------------\nGC msg : Collection started.");

        self.mark();

        self.sweep();

        println!(
            "GC msg : Collection finished (alive: {}).\n------------------------",
            self.all_nodes.len()
        );
    }


    unsafe fn print_heap(&self) {
        for &ptr in &self.all_nodes {
            print!("[{}] ", (*ptr).value);
        }
        println!();
    }
}

fn main() {
}
