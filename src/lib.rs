//! A library for working with Ext terms of the Adams
//! spectral sequence, mod 2.

#[macro_use]
extern crate lazy_static;
extern crate linked_hash_set;
extern crate bit_set;

#[macro_use]
mod internal_macros;

#[macro_use]
pub mod macros;

#[macro_use]
mod memoize;

pub mod module;
pub mod steenrod;
//pub mod resolution;