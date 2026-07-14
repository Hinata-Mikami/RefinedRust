#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]
#![allow(unused)]
#![allow(non_camel_case_types)]
#![allow(unsafe_op_in_unsafe_fn)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]

use std::ptr;

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
}


#[rr::refined_by("(vals, locs, nexts, marks)" :
                 "(list Z * list loc * list loc * list bool)")]
#[rr::depends_on(Node)]
#[rr::inv("Hlen_locs" : "length locs = length vals")]
#[rr::inv("Hlen_nexts" : "length nexts = length vals")]
#[rr::inv("Hlen_marks" : "length marks = length vals")]
#[rr::inv("Hnext_valid" : "Forall (λ n, n = NULL_loc ∨ n ∈ locs) nexts")]
#[rr::inv(#iris "
  ([∗ list] i ↦ v ∈ vals,
    ∃ l n : loc, ∃ m : bool,
      ⌜locs !! i = Some l⌝ ∗
      ⌜nexts !! i = Some n⌝ ∗
      ⌜marks !! i = Some m⌝ ∗
      guarded true
        (l ◁ₗ[π, Owned]
          # -[#v; #n; #m]
          @ ◁(Node_ty <INST!>)) ∗
      freeable_nz l
        (ly_size (use_layout_alg' Node_sls))
        1 HeapAlloc)
")]
struct Heap {
    #[rr::field("<#> locs")]
    all_nodes: Vec<*mut Node>,
}



// ヘルパー
#[rr::params("v" : "Z")]
#[rr::args("v")]
#[rr::requires("MinInt i32 ≤ v")]
#[rr::requires("v ≤ MaxInt i32")]
#[rr::exists("l" : "loc")]
#[rr::returns("l")]
#[rr::ensures(#type "l" : "-[#v; #NULL_loc; #false]" @ "(Node_ty <INST!>)")]
#[rr::ensures(#iris "freeable_nz l (ly_size (use_layout_alg' Node_sls)) 1 HeapAlloc")]
#[rr::ensures("l.(loc_a) ≠ 0")]
#[rr::ensures("MinInt usize ≤ l.(loc_a)")]
#[rr::ensures("l.(loc_a) ≤ MaxInt usize")]
fn make_node(v: i32) -> *mut Node {
    let node = Box::new(Node {
        value: v,
        next: ptr::null_mut(),
        marked: false,
    });
    Box::into_raw(node)
}

#[rr::params(
    "node" : "loc",
    "next" : "loc",
    "v" : "Z",
    "m" : "bool",
    "next_v" : "Z",
    "next_next" : "loc",
    "next_m" : "bool"
)]
#[rr::args("node")]
#[rr::requires("next.(loc_a) ≠ 0")]
#[rr::requires(#type "node" : "-[#v; #next; #m]" @ "(Node_ty <INST!>)")]
#[rr::requires(#type "next" : "-[#next_v; #next_next; #next_m]" @ "(Node_ty <INST!>)")]
#[rr::ensures(#type "node" : "-[#v; #next; #m]" @ "(Node_ty <INST!>)")]
#[rr::ensures(#type "next" : "-[#next_v; #next_next; #next_m]" @ "(Node_ty <INST!>)")]
#[rr::returns("next_v")]
unsafe fn read_next_value(node: *mut Node) -> i32 {
    let next = unsafe { (*node).next };
    unsafe { (*next).value }
}



impl Heap {
    #[rr::returns("([], [], [], [])")]
    fn new() -> Self {
        Heap {
            all_nodes: Vec::new(),
        }
    }

    // hは4つ組。((v, l, n, m), v) と書くと5つ組と解釈される？
    #[rr::params("h", "v" : "Z")]
    #[rr::args("h", "v")]
    #[rr::requires("MinInt i32 ≤ v")]
    #[rr::requires("v ≤ MaxInt i32")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        length locs < MaxInt usize
    ")]
    #[rr::requires("
        let '(vals, locs, nexts, marks) := h.cur in
        size_of_array_in_bytes PtrSynType (2 * length locs) ≤ MaxInt isize
    ")]
    #[rr::exists("ptr" : "loc")]
    #[rr::returns("ptr")]
    #[rr::observe("h.ghost" : "
        let '(vals, locs, nexts, marks) := h.cur in
        (vals ++ [v], locs ++ [ptr], nexts ++ [NULL_loc], marks ++ [false])
    ")]
    #[rr::ensures("ptr.(loc_a) ≠ 0")]
    //x' @ StructLtype +[◁ int i32; ◁ alias_ptr_t; ◁ bool_t] Node_sls を 
    //Node_ty に畳めないエラー -> 手動証明？ 
    fn alloc(&mut self, value: i32) -> *mut Node {
        let ptr = make_node(value);
        self.all_nodes.push(ptr);
        ptr
    }

    /* マークフェーズ */
    unsafe fn mark(&self, start_node: *mut Node) {
        // (ノードがnullか)，またはすでにマークされていれば終了
        if start_node.is_null() || (*start_node).marked {
            return;
        }

        (*start_node).marked = true;
        self.mark((*start_node).next);  // 再帰的に次のノードもマーク
    }

    // あるノードから reachable であるという rocq 側の述語 (inductive)
    // marked all_nodes
    // mark の事後条件 : start_node から reachable == all_nodes の中で marked
    // Rocq がどう呼ばれているかを理解しなければいけなくなるだろう

    /* スイープフェーズ */
    unsafe fn sweep(&mut self) {
        // all_nodesを走査
        // Vec::retain(|&p| {b}) : ベクタの各要素pに対し，b==trueのものを取り出す
        self.all_nodes.retain(|&node_ptr| {
            if (*node_ptr).marked {                 // marked==true -> 参照されているノード
                (*node_ptr).marked = false;         // リセット
                true                                // all_nodesに残す
            } else {
                println!("GC msg : Node [{}] collected.", (*node_ptr).value);
                let _ = Box::from_raw(node_ptr);    // Boxに管理させる 所有者がいないため解放される
                false                               // all_nodesにも残らない 
            }
        });
    }

    /* マークアンドスイープGC */
    unsafe fn collect(&mut self, roots: Vec<*mut Node>) {
        println!("------------------------\nGC msg : Collection started.");

        for root in roots {           // 指定されたノードから走査する
            self.mark(root);
        }

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
