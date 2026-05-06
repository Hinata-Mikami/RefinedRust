#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![allow(dead_code)]

#![rr::include("stdlib")]
#![rr::include("vec")]
#![rr::include("option")]
#![rr::include("ptr")]
#![rr::include("mem")]
#![rr::include("rr_internal")]

use std::ptr;

/* 連結リストの各ノード */
// n に関する　invariant (null or next node)   
// rocq 側で n が 正しいノードであることを表す述語を書く(サイクルなら co-inductive)
#[rr::refined_by("(v, n, m)" : "(Z * loc * bool)")]
#[rr::invariant(#iris "
  (
    ⌜n = (Loc ProvNone 0)⌝
    ∨
    ∃ (v' : Z) (n' : loc) (m' : bool),
        n ◁ₗ[ π, Owned] # -[# v'; # n'; # m'] @
        StructLtype +[◁ int i32; ◁ alias_ptr_t; ◁ bool_t] Node_sls
  )
")]
struct Node {
    #[rr::field("v")]
    value: i32,         // 値 (i32に固定)
    #[rr::field("n")]
    next: *mut Node,    // 次のノードへの生ポインタ
    #[rr::field("m")]
    marked: bool,       // GC用フラグ
}

impl Node{
    /* ok */
    /* Nextの設定・書き換え */
    /* raw_pointer を書き換えて raw_pointer を返す */
    #[rr::params("node":"loc", "next":"loc", "v":"Z", "old_next":"loc", "m":"bool")]
    #[rr::args("node", "next")]
    // #[rr::requires(#type "node" : "(v, old_next, m)" @ "(Node_inv_t <INST!>)")]
    // #[rr::ensures(#iris "
    //   node ◁ₗ[π, Owned] # -[# v; # next; # m] @
    //     (◁ struct_t Node_sls +[◁ int i32; alias_ptr_t; ◁ bool_t])
    // ")]
    #[rr::returns("()")]
    unsafe fn set_next(node: *mut Node, next: *mut Node) {
            (*node).next = next;
    }
}

/* 生成したすべてのNodeを管理するリスト */ // heap, memory, valid nodes
// vecの各要素が有効なポインタであることを表す述語
#[rr::refined_by("all_nodes")]
struct Heap {
    #[rr::field("all_nodes")]
    all_nodes: Vec<*mut Node>,
}

impl Heap {
    /* ok */
    /* 空のメモリ領域を生成 */
    #[rr::returns("[]")]
    fn new() -> Self {
        Self { all_nodes: Vec::new() }
    }

    /* ok */
    /* 新たなノードを生成し割り当て */
    #[rr::params("l", "v" : "Z")]
    #[rr::args("l", "v")]
    #[rr::requires("length l.cur < MaxInt usize")] // precondition で長さに関する条件を要求
    #[rr::requires("size_of_array_in_bytes (PtrSynType) (2 * length l.cur) ≤ MaxInt isize")]
    #[rr::exists("ptr" : "loc")]
    #[rr::returns("ptr")]
    #[rr::observe("l.ghost" : "<$#>(l.cur ++ [ptr])")]
    #[rr::ensures(#type "ptr" : "(v, (Loc ProvNone 0), false)" @ "(Node_inv_t <INST!>)")]
    fn alloc(&mut self, value: i32) -> *mut Node {
        let node = Box::new(Node {      // Boxでヒープにメモリを確保
            value,
            next: ptr::null_mut(),
            marked: false,
        });
        let ptr = Box::into_raw(node);  // Boxから生ポインタに変換し所有権を放棄
        self.all_nodes.push(ptr);       // 管理リストに追加
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

// 実行
fn main() {

    let mut heap = Heap::new();     // メモリ領域の初期化

    unsafe {
        let n1 = heap.alloc(10);    // alloc : ノードの生成と割り当て
        let n2 = heap.alloc(20);
        let n3 = heap.alloc(30);
        let n4 = heap.alloc(40);

        Node::set_next(n1, n2);
        Node::set_next(n2, n3);
        Node::set_next(n3, n1);     // サイクルを形成

        heap.collect(vec![n1]);     // GC : n4解放

        Node::set_next(n1, n3);     // n1 -> n3 -> n1 というサイクルを形成
                                    // n2 孤立
        heap.collect(vec![n1]);     // GC : n2解放
    }
}
