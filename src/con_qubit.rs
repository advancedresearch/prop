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
//!
//! ### Naming conventions
//!
//! - `cqu`: con-qubit
//! - `cq`: con-quality
//! - `caq`: con-aquality

use crate::*;
use psq::*;

pub use cq_commute as cq_symmetry;
pub use caq_commute as caq_symmetry;
pub use ncq_commute as ncq_symmetry;
pub use ncaq_commute as ncaq_symmetry;

/// Con-PSQ logic.
pub struct ConPSQ;

impl PSQ for ConPSQ {
    type Qubit<A> = ConQubit<A>;
}

/// Path semantical con-quality `a .~~ b`.
pub type Cq<A, B> = And<Eq<A, B>, And<ConQubit<A>, ConQubit<B>>>;

/// Path semantical con-aquality `a .~¬~ b`.
pub type Caq<A, B> = And<Eq<A, B>, And<ConQubit<Not<A>>, ConQubit<Not<B>>>>;

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
    fn cqu_eq<A: Prop>() -> Eq<Not<ConQubit<A>>, ConQubit<Not<A>>>;

    /// `false` as consequence of the paradox.
    fn absurd() -> False {
        nn_cqunn_to_ncqun_absurd(not::double(()), Self::cqu_eq().1)
    }
}

/// `(x ⋁ ¬x) => ¬¬.~x`.
///
/// Convert excluded middle to double-negated con-qubit.
pub fn excm_to_nncqu<A: Prop>(excm_a: ExcM<A>) -> Not<Not<ConQubit<A>>> {
    match excm_a {
        Left(x) => not::double(ConQubit::from_pos(x)),
        Right(nx) => ConQubit::from_neg(nx),
    }
}

/// `¬¬x ⋀ (.~¬¬x => ¬.~¬x) => false`.
pub fn nn_cqunn_to_ncqun_absurd<A: Prop>(
    nnx: Not<Not<A>>,
    f: Imply<ConQubit<Not<Not<A>>>, Not<ConQubit<Not<A>>>>,
) -> False {
    let cnnx = ConQubit::from_pos(nnx.clone());
    let ncnx: Not<ConQubit<Not<A>>> = f(cnnx);
    let nncnx = ConQubit::from_neg(nnx);
    not::absurd(nncnx, ncnx)
}

/// `¬.~x => false`.
pub fn ncqu_absurd<A: Prop>(nx: Not<ConQubit<A>>) -> False {
    let nnnx = not::double(nx.clone());
    let y: Not<ExcM<A>> = imply::in_left_arg(nnnx, (
        Rc::new(move |nnx| ConQubit::to_excm(nnx)),
        Rc::new(move |excm| excm_to_nncqu(excm))
    ));
    A::nnexcm()(y)
}

/// `(.~x ⋁ ¬.~x) => .~x`.
pub fn excmcqu_to_cqu<A: Prop>(excm: ExcM<ConQubit<A>>) -> ConQubit<A> {
    let f = Rc::new(move |nx| ncqu_absurd(nx));
    match excm {
        Left(x) => x,
        Right(nx) => not::absurd(f, nx),
    }
}

/// `(¬¬.~.~x) => .~x`.
pub fn nnccq_to_cq<A: Prop>(x: Not<Not<ConQubit<ConQubit<A>>>>) -> ConQubit<A> {
    excmcqu_to_cqu(ConQubit::to_excm(x))
}

/// `(.~x => x) => ¬¬x`.
pub fn cqu_unwrap_to_nn<A: Prop>(f: Imply<ConQubit<A>, A>) -> Not<Not<A>> {
    Rc::new(move |nx| {
        let ncx: Not<ConQubit<A>> = imply::modus_tollens(f.clone())(nx.clone());
        excm_to_nncqu(Right(nx))(ncx)
    })
}

/// `(a ⋀ b) => (a .~~ b)`.
pub fn and_pos_to_cq<A: Prop, B: Prop>(and: And<A, B>) -> Cq<A, B> {
    (and::to_eq_pos(and.clone()), (ConQubit::from_pos(and.0), ConQubit::from_pos(and.1)))
}

/// `(¬a ⋀ ¬b) => (a .~¬~ b)`.
pub fn and_neg_to_caq<A: Prop, B: Prop>(and: And<Not<A>, Not<B>>) -> Caq<A, B> {
    (and::to_eq_neg(and.clone()), (ConQubit::from_pos(and.0), ConQubit::from_pos(and.1)))
}

/// Symmetry `(a .~~ b) => (b .~~ a)`.
pub fn cq_commute<A: Prop, B: Prop>(f: Cq<A, B>) -> Cq<B, A> {
    psq::q_commute::<ConPSQ, A, B>(f)
}

/// Symmetry `(a .~¬~ b) => (b .~¬~ a)`.
pub fn caq_commute<A: Prop, B: Prop>(f: Caq<A, B>) -> Caq<B, A> {
    psq::aq_commute::<ConPSQ, A, B>(f)
}

/// Negated symmetry `¬(a .~~ b) => ¬(b .~~ a)`.
pub fn ncq_commute<A: Prop, B: Prop>(nq: Not<Cq<A, B>>) -> Not<Cq<B, A>> {
    psq::nq_commute::<ConPSQ, A, B>(nq)
}

/// Negated symmetry `¬(a .~¬~ b) => ¬(b .~¬~ a)`.
pub fn ncaq_commute<A: Prop, B: Prop>(nq: Not<Caq<A, B>>) -> Not<Caq<B, A>> {
    psq::naq_commute::<ConPSQ, A, B>(nq)
}

/// Transitivity `(a .~~ b) ⋀ (b .~~ c) => (a .~~ c)`.
pub fn cq_transitivity<A: Prop, B: Prop, C: Prop>(
    f: Cq<A, B>,
    g: Cq<B, C>
) -> Cq<A, C> {
    psq::q_transitivity::<ConPSQ, A, B, C>(f, g)
}

/// Transitivity `(a .~¬~ b) ⋀ (b .~¬~ c) => (a .~¬~ c)`.
pub fn caq_transitivity<A: Prop, B: Prop, C: Prop>(
    f: Caq<A, B>,
    g: Caq<B, C>
) -> Caq<A, C> {
    psq::aq_transitivity::<ConPSQ, A, B, C>(f, g)
}

/// `.~a => (a .~~ a)`.
pub fn cqu_to_cq<A: Prop>(x: ConQubit<A>) -> Cq<A, A> {
    psq::qu_to_q::<ConPSQ, A>(x)
}

/// `.~¬a => (a .~¬~ a)`.
pub fn cqun_to_caq<A: Prop>(x: ConQubit<Not<A>>) -> Caq<A, A> {
    psq::qun_to_aq::<ConPSQ, A>(x)
}

/// `(a .~~ a) => .~a`.
pub fn cq_to_cqu<A: Prop>(f: Cq<A, A>) -> ConQubit<A> {
    psq::q_to_qu::<ConPSQ, A>(f)
}

/// `(a .~¬~ a) => .~¬a`.
pub fn caq_to_cqun<A: Prop>(f: Caq<A, A>) -> ConQubit<Not<A>> {
    psq::aq_to_qun::<ConPSQ, A>(f)
}

/// `(a .~~ b) => (a == b)`.
pub fn cq_to_eq<A: Prop, B: Prop>(f: Cq<A, B>) -> Eq<A, B> {
    psq::q_to_eq::<ConPSQ, A, B>(f)
}

/// `(a .~¬~ b) => (a == b)`.
pub fn caq_to_eq<A: Prop, B: Prop>(f: Caq<A, B>) -> Eq<A, B> {
    psq::aq_to_eq::<ConPSQ, A, B>(f)
}

/// `(a .~~ b) => (a .~~ a)`.
pub fn cq_left<A: Prop, B: Prop>(f: Cq<A, B>) -> Cq<A, A> {
    psq::q_left::<ConPSQ, A, B>(f)
}

/// `(a .~¬~ b) => (a .~¬~ a)`.
pub fn caq_left<A: Prop, B: Prop>(f: Caq<A, B>) -> Caq<A, A> {
    psq::aq_left::<ConPSQ, A, B>(f)
}

/// `(a .~~ b) => (b .~~ b)`.
pub fn cq_right<A: Prop, B: Prop>(f: Cq<A, B>) -> Cq<B, B> {
    psq::q_right::<ConPSQ, A, B>(f)
}

/// `(a .~¬~ b) => (b .~¬~ b)`.
pub fn caq_right<A: Prop, B: Prop>(f: Caq<A, B>) -> Caq<B, B> {
    psq::aq_right::<ConPSQ, A, B>(f)
}
