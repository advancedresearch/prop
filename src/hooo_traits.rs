//! Traits showing what would happen with alternative axioms for HOOO Exponential Propositions.

use crate::*;
use crate::hooo::*;

/// Shows that `tauto_hooo_not` axiom would be absurd.
pub trait TautoHoooNot {
    /// `(¬a)^b => (¬(a^b))^true`.
    fn tauto_hooo_not<A: Prop, B: Prop>(&self) -> Tauto<Pow<Not<Pow<A, B>>, Pow<Not<A>, B>>>;

    /// `false`.
    fn absurd(&self) -> False {
        let a: Pow<True, False> = fa();
        let b: Pow<Not<True>, False> = fa();
        self.tauto_hooo_not()(True)(b)(a)
    }
}

/// Shows that a `hooo_not` axiom would be absurd.
pub trait HoooNot {
    /// `(¬a)^b => ¬(a^b)`.
    fn hooo_not<A: Prop, B: Prop>(&self) -> Pow<Not<Pow<A, B>>, Pow<Not<A>, B>>;

    /// `false`.
    fn absurd(&self) -> False {
        let a: Pow<True, False> = fa();
        let b: Pow<Not<True>, False> = fa();
        self.hooo_not()(b)(a)
    }
}

/// Shows that a global `tauto_hooo_rev_imply` axiom would collapse power to implication.
pub trait GlobalTautoHoooRevImply: Sized {
    /// `(a^c => b^c)^true => (a => b)^c`.
    fn tauto_hooo_rev_imply<A: Prop, B: Prop, C: Prop>() ->
        Pow<Pow<Imply<A, B>, C>, Tauto<Imply<Pow<A, C>, Pow<B, C>>>>;

    /// `(a^c => b^c) => (a => b)^c`.
    fn hooo_rev_imply<A: Prop, B: Prop, C: Prop>(
        x: Imply<Pow<A, C>, Pow<B, C>>
    ) -> Pow<Imply<A, B>, C> {
        fn f<T: GlobalTautoHoooRevImply, A: Prop, B: Prop, C: Prop>(_: True) ->
            Imply<Tauto<Imply<Pow<A, C>, Pow<B, C>>>, Tauto<Pow<Imply<A, B>, C>>> {
            Rc::new(move |x| pow_lift(T::tauto_hooo_rev_imply()(x)))
        }
        Self::tauto_hooo_rev_imply()(f::<Self, A, B, C>)(True)(x)
    }

    /// `(a => b)  =>  (b^a)`.
    fn imply_to_pow<A: Prop, B: Prop>(ab: Imply<A, B>) -> Pow<B, A> {
        let x = pow_to_imply(tauto_pow_imply);
        let x = Self::hooo_rev_imply(x);
        x(True)(ab)
    }
}

/// A `tauto_hooo_rev_imply` axiom.
///
/// This is safe because it requires a proof to obtain the axiom,
/// such that `(tauto_hooo_rev_imply => hooo_rev_imply)^true` is not provable.
///
/// The axiom `hooo_rev_imply` is too strong, since it collapses power to implication.
///
/// The theorem `(tauto_hooo_rev_imply => hooo_rev_imply)^true` is provable
/// when `tauto_hooo_rev_imply^true`, which would be a problem,
/// however since this trait uses `&self`, it is safe.
pub trait TautoHoooRevImply {
    /// `(a^c => b^c)^true => (a => b)^c`.
    fn tauto_hooo_rev_imply<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Pow<Imply<A, B>, C>, Tauto<Imply<Pow<A, C>, Pow<B, C>>>>;
}

/// Shows that a `tauto_hooo_rev_imply` axiom would collapse power to implication.
pub trait HoooRevImply {
    /// `(a^c => b^c) => (a => b)^c`.
    fn hooo_rev_imply<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Pow<Imply<A, B>, C>, Imply<Pow<A, C>, Pow<B, C>>>;

    /// `(a => b)  =>  (b^a)`.
    fn imply_to_pow<A: Prop, B: Prop>(&self, ab: Imply<A, B>) -> Pow<B, A> {
        let x = pow_to_imply(tauto_pow_imply);
        let x = self.hooo_rev_imply()(x);
        x(True)(ab)
    }
}

/// Shows that a `tauto_hooo_neq` axiom would be absurd.
pub trait TautoHoooNeq {
    /// `(¬(a == b))^c => (¬(a^c == b^c))^true`.
    fn tauto_hooo_neq<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Tauto<Not<Eq<Pow<A, C>, Pow<B, C>>>>, Pow<Not<Eq<A, B>>, C>>;

    /// `false`.
    fn absurd(&self) -> False {
        self.tauto_hooo_neq()(fa::<Not<Eq<True, True>>>())(True)(eq::refl())
    }
}

/// Shows that a `hooo_neq` axiom would be absurd.
pub trait HoooNeq {
    /// `(¬(a == b))^c => ¬(a^c == b^c)`.
    fn hooo_neq<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Not<Eq<Pow<A, C>, Pow<B, C>>>, Pow<Not<Eq<A, B>>, C>>;

    /// `false`.
    fn absurd(&self) -> False {
        self.hooo_neq()(fa::<Not<Eq<True, True>>>())(eq::refl())
    }
}

/// Shows that a `tauto_hooo_nrimply` axiom would be absurd.
pub trait TautoHoooNRImply {
    /// `(¬(b => a))^c => (¬(b^c => a^c))^true`.
    fn tauto_hooo_nrimply<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Tauto<Not<Imply<Pow<B, C>, Pow<A, C>>>>, Pow<Not<Imply<B, A>>, C>>;

    /// `false`.
    fn absurd(&self) -> False {
        self.tauto_hooo_nrimply()(fa::<Not<Imply<True, True>>>())(True)(imply::id())
    }
}

/// Shows that a `hooo_nrimply` axiom would be absurd.
pub trait HoooNRImply {
    /// `(¬(b => a))^c => ¬(b^c => a^c)`.
    fn hooo_nrimply<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Not<Imply<Pow<B, C>, Pow<A, C>>>, Pow<Not<Imply<B, A>>, C>>;

    /// `false`.
    fn absurd(&self) -> False {
        self.hooo_nrimply()(fa::<Not<Imply<True, True>>>())(imply::id())
    }
}

/// Shows that a `hooo_dual_imply` axiom would be absurd.
pub trait TautoHoooDualImply {
    /// `c^(a => b) => (¬(c^b => c^a))^true`.
    fn tauto_hooo_dual_imply<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Tauto<Not<Imply<Pow<C, B>, Pow<C, A>>>>, Pow<C, Imply<A, B>>>;

    /// `false`.
    fn absurd(&self) -> False {
        fn f(_: Or<True, Not<True>>) -> True {True}
        let (a, b) = hooo_dual_or(f);
        let y = self.tauto_hooo_dual_imply()(b)(True);
        Rc::new(move |pow_a_b: Pow<_, _>| y(pow_a_b.map_any()))(a)
    }
}

/// Shows that a `hooo_dual_imply` axiom would be absurd.
pub trait HoooDualImply {
    /// `c^(a => b) => ¬(c^b => c^a)`.
    fn hooo_dual_imply<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Not<Imply<Pow<C, B>, Pow<C, A>>>, Pow<C, Imply<A, B>>>;

    /// `false`.
    fn absurd(&self) -> False {
        fn f(_: Or<True, Not<True>>) -> True {True}
        let (a, b) = hooo_dual_or(f);
        let y = self.hooo_dual_imply()(b);
        Rc::new(move |pow_a_b: Pow<_, _>| y(pow_a_b.map_any()))(a)
    }
}

/// Shows that a `hooo_dual_eq` axiom would be absurd.
pub trait HoooDualEq {
    /// `c^(a == b) => ¬(c^a == c^b)`.
    fn hooo_dual_eq<A: Prop, B: Prop, C: Prop>(&self) ->
        Pow<Not<Eq<Pow<C, A>, Pow<C, B>>>, Pow<C, Eq<A, B>>>;

    /// `false`.
    fn absurd(&self) -> False {
        self.hooo_dual_eq::<True, True, True>()(tr())(eq::refl())
    }
}