#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]


//　struct Data は v (Z型) でモデル化する 
#[rr::refined_by("v": "Z")]
struct Data{
    #[rr::field("v")] // v は value フィールドに対応
    value: i32,
}


#[rr::params("data" : "Z", "val" : "Z")]  // 使用する変数宣言
#[rr::args("data", "val" @ "int i32")]  // write 関数の引数との対応
#[rr::returns("val")]  // 返り値は Data だがモデル上は val
fn write(mut data: Data, val : i32) -> Data {
    data.value = val;
    data
}


// この辺のノーテーションはチュートリアルを参考にした
#[rr::params(v : "Z", "γ", val : "Z")]
#[rr::args("(#v, γ)", "val" @ "int i32")] 
#[rr::returns("()")]
#[rr::observe("γ": "val")]
fn write_pointer(ptr: &mut Data, val: i32) {
    (*ptr).value = val;
}


#[rr::returns("()")]
fn logic1() {
    let mut d = Data{value : 0};
    d = write(d, 42);
    assert!(d.value == 42);
}


#[rr::returns("()")]
fn logic2() {
    let mut d = Data{value : 0};

    let p = &mut d;
    write_pointer(p, 42);
 
    assert!(d.value == 42);
}


fn main() {
    logic1();
    logic2();
}
