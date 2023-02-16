//! Traits shows what would happen with alternative axioms for functional programming.

use super::*;
use fun::*;
use hooo::Theory;

/// Shows that raw definition of the identity map is absurd.
pub trait RawIdDef {
    /// `id(a) = a`.
    fn raw_id_def<A: Prop>() -> Eq<App<FId, A>, A>;

    /// `theory(a)`.
    fn theory<A: Prop>() -> Theory<A> {
        hooo::theory_in_arg(app_theory(), tauto!(Self::raw_id_def()))
    }

    /// `false`.
    fn absurd() -> False {Self::theory()(Left(hooo::tr()))}
}
