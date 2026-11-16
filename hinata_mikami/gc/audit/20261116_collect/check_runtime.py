"""Run the current GC source with a System allocator observer.

Only the empty main is replaced in a temporary copy. This is evidence for one
concrete execution, not a proof of deallocation for every possible execution.
Run after sourcing ../../activate.sh from this directory, or activate.sh from
the crate root. No generated Rocq files are changed.
"""

import hashlib
import pathlib
import subprocess
import tempfile


HARNESS = r'''
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering::Relaxed};

struct AllocatorEvent {
    kind: AtomicUsize,
    address: AtomicUsize,
    size: AtomicUsize,
    align: AtomicUsize,
}

const EVENT_CAPACITY: usize = 128;
static RECORDING: AtomicBool = AtomicBool::new(false);
static EVENT_COUNT: AtomicUsize = AtomicUsize::new(0);
static EVENTS: [AllocatorEvent; EVENT_CAPACITY] = [const { AllocatorEvent {
    kind: AtomicUsize::new(0),
    address: AtomicUsize::new(0),
    size: AtomicUsize::new(0),
    align: AtomicUsize::new(0),
} }; EVENT_CAPACITY];

fn record_allocator_event(kind: usize, address: *mut u8, layout: Layout) {
    if RECORDING.load(Relaxed) {
        let index = EVENT_COUNT.fetch_add(1, Relaxed);
        if index < EVENT_CAPACITY {
            let event = &EVENTS[index];
            event.address.store(address as usize, Relaxed);
            event.size.store(layout.size(), Relaxed);
            event.align.store(layout.align(), Relaxed);
            event.kind.store(kind, Relaxed);
        }
    }
}

struct ObservedSystem;

unsafe impl GlobalAlloc for ObservedSystem {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let address = unsafe { System.alloc(layout) };
        record_allocator_event(1, address, layout);
        address
    }

    unsafe fn dealloc(&self, address: *mut u8, layout: Layout) {
        record_allocator_event(2, address, layout);
        unsafe { System.dealloc(address, layout) };
    }
}

#[global_allocator]
static ALLOCATOR: ObservedSystem = ObservedSystem;

fn node_event_count(kind: usize, node: *mut Node, end: usize) -> usize {
    assert!(end <= EVENT_CAPACITY);
    let layout = Layout::new::<Node>();
    EVENTS[..end].iter().filter(|event| {
        event.kind.load(Relaxed) == kind
            && event.address.load(Relaxed) == node as usize
            && event.size.load(Relaxed) == layout.size()
            && event.align.load(Relaxed) == layout.align()
    }).count()
}

fn main() {
    RECORDING.store(true, Relaxed);
    let mut heap = Heap::new();
    let nodes = [heap.alloc(10), heap.alloc(20), heap.alloc(30),
                 heap.alloc(40), heap.alloc(50)];
    let [a, b, c, d, e] = nodes;
    unsafe {
        // Reachable cycle: a -> b -> c -> b. Unreachable cycle: d <-> e.
        Node::set_next(a, b);
        Node::set_next(b, c);
        Node::set_next(c, b);
        Node::set_next(d, e);
        Node::set_next(e, d);
        assert!(nodes.iter().all(|node| !(**node).marked));
        heap.collect();
    }
    let first_end = EVENT_COUNT.load(Relaxed);
    assert_eq!(heap.all_nodes.as_slice(), &[a, b, c]);
    for (index, node) in heap.all_nodes.iter().enumerate() {
        unsafe {
            assert!(!(**node).marked);
            assert_eq!((**node).value, [10, 20, 30][index]);
            assert_eq!((**node).next, [b, c, b][index]);
        }
    }
    // A second collection exercises the reset-mark postcondition.
    unsafe { heap.collect() };
    let second_end = EVENT_COUNT.load(Relaxed);
    RECORDING.store(false, Relaxed);
    assert_eq!(heap.all_nodes.as_slice(), &[a, b, c]);
    for (index, node) in nodes.iter().enumerate() {
        let expected_frees = usize::from(index >= 3);
        assert_eq!(node_event_count(1, *node, first_end), 1);
        assert_eq!(node_event_count(2, *node, first_end), expected_frees);
        assert_eq!(node_event_count(2, *node, second_end), expected_frees);
        println!("Node {}: System.alloc=1, System.dealloc={}, alive={}",
                 index, expected_frees, index < 3);
    }
    println!("PASS: reachable cycle retained; unreachable cycle deallocated once per node");
    println!("PASS: values/next preserved; marks reset; second collect retains the same nodes");
    // Release the survivors after observing collect; freed nodes are never dereferenced.
    for node in heap.all_nodes.drain(..) {
        unsafe { drop(Box::from_raw(node)) };
    }
}
'''


def main():
    crate = pathlib.Path(__file__).resolve().parents[2]
    source = crate / "src/main.rs"
    content = source.read_text()
    empty_main = "fn main() {\n}\n"
    if content.count(empty_main) != 1:
        raise RuntimeError("Expected exactly one empty main; inspect the harness before rerunning")
    print("Production source SHA256:", hashlib.sha256(source.read_bytes()).hexdigest(), flush=True)
    subprocess.run(["rustc", "--version"], check=True)
    with tempfile.TemporaryDirectory(prefix="gc-20261116-runtime-") as directory:
        test_source = pathlib.Path(directory) / "main.rs"
        executable = pathlib.Path(directory) / "gc-runtime"
        test_source.write_text(content.replace(empty_main, HARNESS))
        subprocess.run(["rustc", "--edition=2024", "-C", "opt-level=0",
                        str(test_source), "-o", str(executable)], check=True)
        subprocess.run([str(executable)], check=True)


if __name__ == "__main__":
    main()
