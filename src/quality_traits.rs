//! Traits showing what would happen with alternative axioms for Path Semantical Quality.

use crate::*;
use crate::quality::*;

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
    /// `(a == b) => ((a ~~ b) | ¬¬(a ~~ b))`.
    fn pure_platonism<A: Prop, B: Prop>(&self) -> Imply<Eq<A, B>, Or<Q<A, B>, Not<Not<Q<A, B>>>>>;

    /// Mirror with pure Platonism
    /// `((a == a) => ( (a ~~ a) ⋁ ¬¬(a ~~ a) )) => ¬¬(a ~~ a)`.
    fn mirror<A: Prop>(&self) -> Not<Not<Q<A, A>>> {
        match self.pure_platonism()(eq::refl()) {
            Left(q_aa) => not::double(q_aa),
            Right(nn_q_aa) => nn_q_aa,
        }
    }

    /// `¬(a ~~ b) ⋀ (a == b) ⋀ ((a == b) => ( (a ~~ b) ⋁ ¬¬(a ~~ b) ))  =>  false`.
    fn absurd<A: Prop, B: Prop>(
        &self,
        n_q: Not<Q<A, B>>,
        eq: Eq<A, B>,
    ) -> False {
        match self.pure_platonism()(eq) {
            Left(q) => n_q(q),
            Right(nn_q) => nn_q(n_q),
        }
    }

    /// Excluded middle with pure Platonism implies reflexivity.
    fn excm_refl<A: Prop>(&self, exc: ExcM<Q<A, A>>) -> Q<A, A> {
        match exc {
            Left(q) => q,
            Right(n_q) => not::absurd(self.mirror(), n_q),
        }
    }

    /// `¬(a ~~ a) ⋀ ((a == a) => ( (a ~~ a) ⋁ ¬¬(a ~~ a) ))  =>  false`.
    fn sesh_absurd<A: Prop>(
        &self,
        f: Not<Q<A, A>>,
    ) -> False {
        self.mirror()(f)
    }
}
