use std::ptr::NonNull;

// オブジェクトの型（今回は数値か、2つのオブジェクトへの参照を持つペア）
enum ObjectValue {
    Int(i32),
    Pair(Option<NonNull<Object>>, Option<NonNull<Object>>),
}

// オブジェクトの本体（ヘッダ + データ）
struct Object {
    marked: bool,           // マークビット
    next: Option<NonNull<Object>>, // ヒープ内の全オブジェクトを繋ぐリスト
    value: ObjectValue,
}

struct SimpleGC {
    head: Option<NonNull<Object>>, // ヒープに割り当てられた全オブジェクトのリスト
    stack: Vec<NonNull<Object>>,  // ルートセット（スタック）
    num_objects: usize,           // 現在のオブジェクト数
    max_objects: usize,           // GCをトリガーする閾値
}

impl SimpleGC {
    fn new(threshold: usize) -> Self {
        Self {
            head: None,
            stack: Vec::new(),
            num_objects: 0,
            max_objects: threshold,
        }
    }

    fn new_object(&mut self, value: ObjectValue) -> NonNull<Object> {
        if self.num_objects >= self.max_objects {
            self.collect();
        }

        let obj = Box::new(Object {
            marked: false,
            next: self.head,
            value,
        });
        
        let ptr = unsafe { NonNull::new_unchecked(Box::into_raw(obj)) };
        self.head = Some(ptr);
        self.num_objects += 1;
        ptr
    }

    fn push_root(&mut self, ptr: NonNull<Object>) {
        self.stack.push(ptr);
    }

    // --- 修正ポイント：mark_all ---
    fn mark_all(&mut self) {
        // self.stack への不変借用を回避するため、ポインタのコピーを作成
        let roots = self.stack.clone(); 
        for root in roots {
            unsafe { self.mark(root) };
        }
    }

    // --- 修正ポイント：mark ---
    unsafe fn mark(&mut self, mut ptr: NonNull<Object>) {
        // unsafe fn の中でも、具体的な unsafe 操作にはブロックが必要
        let obj = unsafe { ptr.as_mut() };
        if obj.marked { return; }

        obj.marked = true;

        if let ObjectValue::Pair(left, right) = &obj.value {
            // 再帰呼び出しも unsafe ブロックで囲む
            if let Some(l) = left { unsafe { self.mark(*l) }; }
            if let Some(r) = right { unsafe { self.mark(*r) }; }
        }
    }

    fn sweep(&mut self) {
        let mut current = self.head;
        let mut prev: Option<NonNull<Object>> = None;

        while let Some(mut ptr) = current {
            let obj = unsafe { ptr.as_mut() };

            if obj.marked {
                obj.marked = false;
                prev = Some(ptr);
                current = obj.next;
            } else {
                let next = obj.next;
                if let Some(mut p) = prev {
                    unsafe { p.as_mut().next = next; }
                } else {
                    self.head = next;
                }

                unsafe { drop(Box::from_raw(ptr.as_ptr())); }
                self.num_objects -= 1;
                current = next;
            }
        }
    }

    pub fn collect(&mut self) {
        self.mark_all();
        self.sweep();
    }
}


fn main() {
    let mut gc = SimpleGC::new(10);
    
    // テスト：オブジェクトを作ってGCを回してみる
    let obj1 = gc.new_object(ObjectValue::Int(10));
    gc.push_root(obj1);
    
    let obj2 = gc.new_object(ObjectValue::Int(20));
    // obj2はルートに登録しないので、次のcollectで消えるはず
    
    println!("Before GC: {} objects", gc.num_objects);
    gc.collect();
    println!("After GC: {} objects", gc.num_objects);
}