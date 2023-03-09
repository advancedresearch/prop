//! Traits showing what would happen with alternative axioms for Path Semantical Quality.

use crate::*;
use crate::quality::*;
use path_semantics::{ty, Ty};
use crate::nat::Z;
use crate::hooo::Pow;
use crate::fun::{App, Tup, Type, FEq};
use crate::fun::bool_alg::{Bool, Fa};

/// Prevents other qualities of `A` from excluding `B`.
pub trait NoOtherQ<A, B>: 'static + Clone {
    /// `(a ~~ c) => ¬¬(b ~~ c)`.
    fn no_other_q<C: Prop>(&self, q: Q<A, C>) -> Not<Not<Q<B, C>>>;
}

/// If something is qual to `A`, then `A` is qual to `B`.
pub trait UniqQ<A, B>: NoOtherQ<A, B> {
    /// `(a ~~ a) => (a ~~ b)`.
    fn uniq_q(&self, q_aa: Q<A, A>) -> Q<A, B>;
}

/// Maps every true proposition `a` into self-quality `a ~~ a`.
pub trait IdQ: 'static + Clone {
    /// `a => (a ~~ a)`.
    fn idq<A: Prop>(&self, a: A) -> Q<A, A>;
    /// `¬(a ~~ a) => ¬a`
    fn sesh_to_not<A: Prop>(&self, sesh_a: Not<Q<A, A>>) -> Not<A> {
        let copy = self.clone();
        imply::modus_tollens(Rc::new(move |a| copy.idq(a)))(sesh_a)
    }
}

/// Maps every self-quality `a ~~ a` into true proposition `a`.
pub trait QId: 'static + Clone {
    /// `(a ~~ a) => a`.
    fn qid<A: Prop>(&self, q_aa: Q<A, A>) -> A;
    /// `¬a => ¬(a ~~ a)`.
    fn not_to_sesh<A: Prop>(&self, na: Not<A>) -> Not<Q<A, A>> {
        let copy = self.clone();
        imply::modus_tollens(Rc::new(move |q_aa| copy.qid(q_aa)))(na)
    }
}

/// Pure Platonism assumption.
pub trait PurePlatonism {
    /// `(a == b) => ¬¬(a ~~ b)`.
    fn pure_platonism<A: Prop, B: Prop>(&self) -> Imply<Eq<A, B>, Not<Not<Q<A, B>>>>;

    /// `((a == a) => ¬¬(a ~~ a)) => ¬¬(a ~~ a)`.
    ///
    /// Mirror with pure Platonism
    fn mirror<A: Prop>(&self) -> Not<Not<Q<A, A>>> {self.pure_platonism()(eq::refl())}

    /// `((a == b) => ¬¬(a ~~ b)) ⋀ ¬(a ~~ b) ⋀ (a == b)  =>  false`.
    fn absurd<A: Prop, B: Prop>(&self, n_q: Not<Q<A, B>>, eq: Eq<A, B>) -> False {
        self.pure_platonism()(eq)(n_q)
    }

    /// Excluded middle with pure Platonism implies reflexivity.
    fn excm_refl<A: Prop>(&self, exc: ExcM<Q<A, A>>) -> Q<A, A> {
        match exc {
            Left(q) => q,
            Right(n_q) => not::absurd(self.mirror(), n_q),
        }
    }

    /// `((a == a) => ¬¬(a ~~ a)) ⋀ ¬(a ~~ a)  =>  false`.
    fn sesh_absurd<A: Prop>(&self, f: Not<Q<A, A>>) -> False {self.mirror()(f)}
}

/// Seshatic Inequality Overloading.
///
/// For more information, see [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/seshatic-inequality-overloading.pdf).
pub trait SeshNeq {
    /// `¬(a ~~ b)  =>  eq((a, b)) = false`.
    fn sesh_neq<A: Prop, B: Prop>(&self) ->
        Pow<Eq<App<FEq, Tup<A, B>>, Fa>, Not<Q<A, B>>>;
    /// `¬(t == u)  =>  eq{t : type(0), u : type(0)} : t x u -> bool`.
    ///
    /// This extends the type of the equality operator to allow different types as input.
    fn eq_ext_ty<T: Prop, U: Prop>(&self, _: Not<Eq<T, U>>) ->
        Pow<Ty<FEq, Pow<Bool, Tup<T, U>>>, And<Ty<T, Type<Z>>, Ty<U, Type<Z>>>>;

    /// `(a : x) ⋀ (b : y) ⋀ ¬(x == y)  =>  eq((a, b)) = false`.
    fn neq_ty_to_eq_fa<A: Prop, B: Prop, X: Prop, Y: Prop>(
        &self,
        ty_a: Ty<A, X>,
        ty_b: Ty<B, Y>,
        x: Not<Eq<X, Y>>
    ) -> Eq<App<FEq, Tup<A, B>>, Fa> {
        self.sesh_neq()(ty::neq_to_sesh(ty_a, ty_b, x))
    }
}
