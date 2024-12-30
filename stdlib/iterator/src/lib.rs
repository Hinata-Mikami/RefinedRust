#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]

#![feature(try_trait_v2)]

#![rr::coq_prefix("stdlib.iterator")]
#![rr::include("closures")]

mod step;
pub mod adapters;
pub mod traits;

