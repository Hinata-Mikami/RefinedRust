#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#[rr::refined_by("x" : "Z")]
struct Data {
    #[rr::field("x")]
    value: i32,
}

#[rr::returns("d")]
fn id_data(d: Data) -> Data {
    d
}

#[rr::returns("()")]
fn main() {
    let d = Data { value: 10 };
    let _ = id_data(d);
}


/* 
Definition type_of_id_data  :=
  fn(∀ ( *[]) : 0 | ( *[]) : ([] : list (RT * syn_type)%type) | 
      (* params....... *) (d) : ((_)),
      (* elctx........ *) (λ ϝ, []);
      (* args......... *) d :@: (Data_inv_t    <INST!>);
      (* precondition. *) (λ π : thread_id, True) |
      (* trait reqs... *) (λ π : thread_id, True)) →
      (* existential.. *) ∃ _ : (unit), d @ (Data_inv_t    <INST!>);
      (* postcondition *) (λ π : thread_id, True).
*/