//! # Path Semantical Con-Qubit
//!
//! Operator symbol: `.~`
//!
//! The idea behind the con-qubit is to show that
//! an alternative qubit operator can be constructed
//! by removing the `¬.~x == .~¬x` axiom
//! and replace it with three axioms:
//!
//! - `x => .~x`
//! - `¬x => ¬¬.~x`
//! - `¬¬.~x => (x ⋁ ¬x)`
//!
//! This can be thought of as a contractible qubit operator.

use crate::*;

pub use cq_commute as cq_symmetry;

/// Path semantical con-quality `a .~~ b`.
pub type Cq<A, B> = And<Eq<A, B>, And<ConQubit<A>, ConQubit<B>>>;

/// Represents a con-qubit proposition.
#[derive(Clone)]
pub struct ConQubit<A>(A);

impl<A: Prop> ConQubit<A> {
    /// `x => .~x`.
    pub fn from_pos(x : A) -> ConQubit<A> {
        ConQubit(x)
    }

    /// `¬x => ¬¬.~x`.
    pub fn from_neg(_nx: Not<A>) -> Not<Not<Self>> {
        unimplemented!()
    }

    /// `¬¬.~x => (x ⋁ ¬x)`.
    pub fn to_excm(_nnx: Not<Not<Self>>) -> ExcM<A> {
        unimplemented!()
    }
}

/// Paradox for con-qubit by assuming `¬.~x == .~¬x`.
pub trait ConQubitParadox: Sized {
    /// `¬.~x == .~¬x`.
    fn cq_eq<A: Prop>() -> Eq<Not<ConQubit<A>>, ConQubit<Not<A>>>;

    /// `false` as consequence of the paradox.
    fn absurd() -> False {
        nn_cnn_to_ncn_absurd(not::double(()), Self::cq_eq().1)
    }
}

/// `(x ⋁ ¬x) => ¬¬.~x`.
///
/// Convert excluded middle to double-negated con-qubit.
pub fn excm_to_nncq<A: Prop>(excm_a: ExcM<A>) -> Not<Not<ConQubit<A>>> {
    match excm_a {
        Left(x) => not::double(ConQubit::from_pos(x)),
        Right(nx) => ConQubit::from_neg(nx),
    }
}

/// `¬¬x ⋀ (.~¬¬x => ¬.~¬x) => false`.
pub fn nn_cnn_to_ncn_absurd<A: Prop>(
    nnx: Not<Not<A>>,
    f: Imply<ConQubit<Not<Not<A>>>, Not<ConQubit<Not<A>>>>,
) -> False {
    let cnnx = ConQubit::from_pos(nnx.clone());
    let ncnx: Not<ConQubit<Not<A>>> = f(cnnx);
    let nncnx = ConQubit::from_neg(nnx);
    not::absurd(nncnx, ncnx)
}

/// `¬.~x ⋀ (x ⋁ ¬x) => false`.
pub fn nc_excm_absurd<A: Prop>(nx: Not<ConQubit<A>>, excm: ExcM<A>) -> False {
    excm_to_nncq(excm)(nx)
}

/// `¬.~x => x` when `x` is decidable.
pub fn nc_absurd<A: DProp>(nx: Not<ConQubit<A>>) -> False {
    nc_excm_absurd(nx, A::decide())
}

/// `(.~x ⋁ ¬.~x) ⋀ (x ⋁ ¬x) => .~x`.
pub fn excmc_excm_to_cq<A: Prop>(excm: ExcM<ConQubit<A>>, excm_a: ExcM<A>) -> ConQubit<A> {
    let f = Rc::new(move |nx| nc_excm_absurd(nx, excm_a.clone()));
    match excm {
        Left(x) => x,
        Right(nx) => not::absurd(f, nx),
    }
}

/// `(.~x ⋁ ¬.~x) => .~x` when `x` is decidable.
pub fn excmc_to_cq<A: DProp>(excm: ExcM<ConQubit<A>>) -> ConQubit<A> {
    excmc_excm_to_cq(excm, A::decide())
}

/// `(¬¬.~.~x) ⋀ (x ⋁ ¬x) => .~x`.
pub fn nnccq_excm_to_cq<A: Prop>(x: Not<Not<ConQubit<ConQubit<A>>>>, excm: ExcM<A>) -> ConQubit<A> {
    excmc_excm_to_cq(ConQubit::to_excm(x), excm)
}

/// `¬¬.~.~x => .~x` when `x` is decidable.
pub fn nnccq_to_cq<A: DProp>(x: Not<Not<ConQubit<ConQubit<A>>>>) -> ConQubit<A> {
    excmc_to_cq(ConQubit::to_excm(x))
}

/// `(.~x => x) => ¬¬x`.
pub fn cq_unwrap_to_nn<A: Prop>(f: Imply<ConQubit<A>, A>) -> Not<Not<A>> {
    Rc::new(move |nx| {
        let ncx: Not<ConQubit<A>> = imply::modus_tollens(f.clone())(nx.clone());
        excm_to_nncq(Right(nx))(ncx)
    })
}

/// Symmetry `(a .~~ b) => (b .~~ a)`.
pub fn cq_commute<A: Prop, B: Prop>(f: Cq<A, B>) -> Cq<B, A> {
    (eq::symmetry(f.0), (f.1.1, f.1.0))
}

/// Transitivity `(a .~~ b) ⋀ (b .~~ c) => (a .~~ c)`.
pub fn cq_transitivity<A: Prop, B: Prop, C: Prop>(
    f: Cq<A, B>,
    g: Cq<B, C>
) -> Cq<A, C> {
    (eq::transitivity(f.0, g.0), (f.1.0, g.1.1))
}
