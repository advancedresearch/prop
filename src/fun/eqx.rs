//! Equality helper macro.

/// Helps converting equality.
///
/// - `def <id>`: Produces an equality that maps a struct to its inner definition
/// - `<expr>, <def>, [<branch cmd>], <leaf cmd>`: Applies branch commands and leaf command.
///
/// # Branch commands
///
/// - `cl`: Compose left
/// - `cr`: Compose right
/// - `a`: Application argument
/// - `am`: Application map
///
/// # Leaf commands
///
/// - `eq`: Both sides of equality
/// - `l`: Left side of equality
/// - `r`: Right side of equality
/// - `co`: Is-constant argument
/// - `tyl`: Type left argument
/// - `tyr`: Type right argument
#[macro_export]
macro_rules! eqx(
    (def $x:ident) => {(std::rc::Rc::new(|x| x.0), std::rc::Rc::new(|x| $x(x)))};
    ($x:expr, $def:expr, cl, $($cmd:tt),+) => {
        eqx!($x, || $crate::fun::comp_eq_left($def()), $($cmd),+)
    };
    ($x:expr, $def:expr, cr, $($cmd:tt),+) => {
        eqx!($x, || $crate::fun::comp_eq_right($def()), $($cmd),+)
    };
    ($x:expr, $def:expr, am, $($cmd:tt),+) => {
        eqx!($x, || $crate::fun::app_map_eq($def()), $($cmd),+)
    };
    ($x:expr, $def:expr, a, $($cmd:tt),+) => {
        eqx!($x, || $crate::fun::app_eq($def()), $($cmd),+)
    };
    ($x:expr, $def:expr, $cmd0:tt, $($cmd:tt),+) => {
        eqx!(eqx!($x, $def, $cmd0), $def, $($cmd),+)
    };
    ($x:expr, $def:expr, eq) => {eqx!(eqx!($x, $def, l), $def, r)};
    ($x:expr, $def:expr, l) => {$crate::eq::in_left_arg($x, $crate::eq::symmetry($def()))};
    ($x:expr, $def:expr, r) => {$crate::eq::in_right_arg($x, $crate::eq::symmetry($def()))};
    ($x:expr, $def:expr, co) => {$crate::fun::const_in_arg($x, $crate::eq::symmetry($def()))};
    ($x:expr, $def:expr, tyl) => {
        $crate::path_semantics::ty::in_left_arg($x, $crate::eq::symmetry($def()))
    };
    ($x:expr, $def:expr, tyr) => {
        $crate::path_semantics::ty_in_right_arg($x, $crate::eq::symmetry($def()))
    };
);
