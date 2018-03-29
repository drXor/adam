//! The Steenrod algebra, and related operations.
//!
//! The Steenrod alrebra consists of all cohomology operations
//! `H^*(X; F_2) -> H^*(X; F_2)` for some space `X`, though
//! its structure is independent of this space.

#[macro_use]
pub mod internal_macros;

pub mod cartan;
pub mod milnor;
pub mod square;

pub use self::cartan::Cartan;
pub use self::milnor::Milnor;
pub use self::square::Square;