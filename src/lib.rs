//! This crate provides a thread-safe mutable memory location called
//! [`AtomicCell`].
//!
//! This type is equivalent to [`Cell`], except it can also be shared among
//! multiple threads.
//! 
//! # How it Works
//! 
//! When constructing an `AtomicCell`, callers select an [`AtomicStorage`]
//! implementation that will fit the data they wish to store. (e.g. `AtomicU8`
//! can be used to hold a `#[repr(u8)]` enum)
//! 
//! Under the hood, the desired type is transmuted to the corresponding base
//! type of the storage, and atomic operations are executed on the storage.
//! 
//! The result is that the user should be able to seamlessly interact with the
//! `AtomicCell` almost as if it were a native atomic.
//! 
//! Two implementations are defined `generic` and `macros`. The `generic`
//! implementation relies on the `AtomicStorage` trait, whereas the `macros`
//! implementation relies on the bare functions. This enables the `macros`
//! implementation to have slightly more `const` functions in stable rust.
//! 
//! [`Cell`]: core::cell::Cell
//! [`AtomicStorage`]: atomic::AtomicStorage
#![cfg_attr(
    feature = "const",
    feature(
        const_cell_into_inner,
        const_convert,
        const_fn_trait_bound,
        const_mut_refs,
        const_trait_impl,
        const_type_name,
    )
)]
#![no_std]

pub mod atomic;
mod cell;
pub mod compare_update;
mod utils;

pub use cell::{generic, macros};
pub use generic::AtomicCell;
