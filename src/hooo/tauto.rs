//! Tautology extensions.

/// Maps expression to tautology.
#[macro_export]
macro_rules! tauto(($x:expr) => {|_: $crate::True| $x});
