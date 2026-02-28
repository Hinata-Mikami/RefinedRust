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
// #![rr::package("minivec")]
// #![rr::import("refinedrust.extra_proofs.minivec", "minivec")]

use std::ptr;

/// TODO ルートセットの検出

/* 連結リストの各ノード */
#[rr::refined_by("(v, n, m)" : "(Z * loc * bool)")]
#[derive(Debug)]        // 構造体の中身の表示用
struct Node {
    #[rr::field("v")]
    value: i32,         // 値 (i32に固定)
    #[rr::field("n")]
    next: *mut Node,    // 次のノードへの生ポインタ
    #[rr::field("m")]
    marked: bool,       // GC用フラグ
}

/* 生成したすべてのNodeを管理するリスト */
#[rr::refined_by("nodes" : "list loc")]
struct LinkedList {
    #[rr::field("nodes")]
    all_nodes: Vec<*mut Node>,
}

impl LinkedList {
    /* 空のメモリ領域を生成 */
    #[rr::exists("all_nodes")]
    #[rr::returns("all_nodes")]
    fn new() -> Self {
        Self { all_nodes: Vec::new() }
    }

    /* 新たなノードを生成し割り当て */
    #[rr::params("l" : "list loc", "v" : "Z")]
    #[rr::args("l", "v")]
    #[rr::exists("ptr" : "loc")]
    #[rr::returns("ptr")]
    // 事後条件1: selfの管理リストの末尾に新しいポインタが追加されている
    #[rr::ensures("self.all_nodes = l ++ [ptr]")]
    // 事後条件2: 返されたポインタptrは、(v, null, false)という値を持つNodeとして有効である
    #[rr::ensures(#type "ptr" : "(v, null, false)" @ "Node")]
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

    /* Nextの設定・書き換え */
    unsafe fn set_next(&self, node: *mut Node, next: *mut Node) {
        if !node.is_null() {            // 生ポインタを扱うためnullチェックを行う
            (*node).next = next;
        }
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

    let mut linkedlist = LinkedList::new(); // メモリ領域の初期化

    unsafe {
        let n1 = linkedlist.alloc(10);
        let n2 = linkedlist.alloc(20);
        let n3 = linkedlist.alloc(30);
        let n4 = linkedlist.alloc(40);

        linkedlist.set_next(n1, n2);        // n1 -> n2
        linkedlist.set_next(n2, n3);        // n2 -> n3
        linkedlist.set_next(n3, n1);        // n3 -> n1

        linkedlist.print_heap();            // デバッグ用

        linkedlist.collect(vec![n1]);       // GC : n4解放

        linkedlist.set_next(n1, n3);        // n1 -> n3 (n2孤立)

        linkedlist.collect(vec![n1]);       // GC : n2解放

        linkedlist.print_heap();            // デバッグ用
    }
}


// #[rr::only_spec]
// #[rr::params("x")]
// #[rr::args("x" @ "(Node_inv_t <INST!>)")] // RRにより自動生成された型
// #[rr::returns("x" @ "(box (Node_inv_t <INST!>))")]
// fn box_new(t: Node) -> Box<Node> {
//     Box::new(t)
// }

// #[rr::only_spec]
// #[rr::params("x")]
// #[rr::args("x" @ "(box (Node_inv_t <INST!>))")]
// #[rr::exists("l")]
// #[rr::returns("l")]
// #[rr::ensures(#type "l" : "x" @ "(Node_inv_t <INST!>)")] 
// fn box_into_raw(b: Box<Node>) -> *mut Node {
//     Box::into_raw(b)
// }

// #[rr::only_spec]
// #[rr::params("l", "x")]
// #[rr::args("l")]
// #[rr::requires(#type "l" : "x" @ "(Node_inv_t <INST!>)")] 
// #[rr::returns("x" @ "(box (Node_inv_t <INST!>))")]
// unsafe fn box_from_raw(ptr: *mut Node) -> Box<Node> {
//     Box::from_raw(ptr)
// }

// #[rr::only_spec]
// #[rr::exists("v")]
// #[rr::returns("v")]
// fn vec_new() -> Vec<*mut Node> {
//     Vec::new()
// }