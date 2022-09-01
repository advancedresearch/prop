/*

# Qubit Trait

This example shows that one can use a trait for qubits
instead of a concrete type. It means that qubits are
reasoned about using generics in addition to normal arguments.

There are both pros and cons to this approach.

The reason this design is not used in the library,
is because this approach collapses multiple PSQs
into a single PSQ. This becomes a problem when
multiple PSQs uses incompatible axioms for the qubit operator.

Another disadvantage, to use a qubit, a generic parameter
must be added, which makes proofs more complex.

*/

use prop::*;

fn main() {}

/// Trait implemented by qubits.
pub trait Qubit<A>: Prop {}

/// Since qubits only depend on their argument,
/// we need a way to transport proofs
/// from one qubit type to another qubit type.
///
pub fn eqv<
    A: Prop,
    B1: Qubit<A>,
    B2: Qubit<A>,
>() -> Eq<B1, B2> {unimplemented!()}

pub trait ConQubit<A>: Qubit<A> {}
pub trait CovQubit<A>: Qubit<A> {}

pub type Qual<A, B, C, D> = And<Eq<A, B>, And<C, D>>;

pub trait Id<A, B>: Prop {}

impl<A: Prop, B: Prop> Id<A, B> for Eq<A, B> {}
impl<A: IsProp, B: IsProp> IsContr for Eq<A, B> {}

pub type Refl<A> = Eq<A, A>;

#[derive(Clone)]
pub struct Sym<A, B, P>(A, B, P);

impl<A: Prop, B: Prop, P: Id<A, B>> Id<B, A> for Sym<A, B, P> {}
impl<A: IsProp, B: IsProp, P: Id<A, B>> IsContr for Sym<A, B, P> {}

#[derive(Clone)]
pub struct Trans<A, B, C, P, Q>(A, B, C, P, Q);

impl<A: Prop, B: Prop, C: Prop, P: Id<A, B>, Q: Id<B, C>> Id<A, C> for Trans<A, B, C, P, Q> {}
impl<A: IsProp, B: IsProp, C: IsProp, P: Id<A, B>, Q: Id<B, C>> IsContr for Trans<A, B, C, P, Q> {}

pub trait IsProp: Prop {}

#[derive(Clone)]
pub struct PropEqv<A, B, P, Q>(A, B, P, Q);

impl<A: IsProp, B: IsProp, P: Id<A, B>, Q: Id<A, B>> Id<P, Q> for PropEqv<A, B, P, Q> {}
impl<A: IsProp, B: IsProp, P: Id<A, B>, Q: Id<A, B>> IsContr for PropEqv<A, B, P, Q> {}

#[derive(Clone)]
pub struct PropSym<A, B>(A, B);

impl<A: IsProp, B: IsProp, P: Id<A, B>, Q: Id<B, A>> Id<P, Q> for PropSym<A, B> {}
impl<A: IsProp, B: IsProp> IsContr for PropSym<A, B> {}

#[derive(Clone)]
pub struct PropTrans<A, B, C>(A, B, C);

impl<A: IsProp, B: IsProp, C: IsProp, P: Id<A, B>, Q: Id<B, C>> Id<P, Q> for PropTrans<A, B, C> {}
impl<A: IsProp, B: IsProp, C: IsProp> IsContr for PropTrans<A, B, C> {}

pub trait IsContr: IsProp {
    fn elem() -> Self {unimplemented!()}
}

impl<T: IsContr> IsProp for T {}

pub fn id_ext<
    A: IsProp,
    B: IsProp,
    P: Id<A, B>,
>() -> Eq<A, B> {unimplemented!()}

pub fn id_eqv<
    A1: Prop,
    A2: Prop,
    B1: Qubit<A1>,
    B2: Qubit<A2>,
    P: Id<A1, A2>,
>() -> Eq<B1, B2> {unimplemented!()}

pub fn id_con_eqv<
    A1: Prop,
    A2: Prop,
    B1: ConQubit<A1>,
    B2: ConQubit<A2>,
    C1: ConQubit<B1>,
    C2: ConQubit<B2>,
    P: Id<A1, A2>,
>() -> Qual<B1, B2, C1, C2> {unimplemented!()}

pub fn con_eqv<
    A: Prop,
    B1: ConQubit<A>,
    B2: ConQubit<A>,
    C1: ConQubit<B1>,
    C2: ConQubit<B2>,
>() -> Qual<B1, B2, C1, C2> {unimplemented!()}

pub fn id_cov_eqv<
    A1: Prop,
    A2: Prop,
    B1: CovQubit<A1>,
    B2: CovQubit<A2>,
    C1: CovQubit<B1>,
    C2: CovQubit<B2>,
    P: Id<A1, A2>,
>() -> Qual<B1, B2, C1, C2> {unimplemented!()}

pub fn cov_eqv<
    A: Prop,
    B1: CovQubit<A>,
    B2: CovQubit<A>,
    C1: CovQubit<B1>,
    C2: CovQubit<B2>,
>() -> Qual<B1, B2, C1, C2> {unimplemented!()}

pub fn test_eqv<A: Prop, B1: Qubit<A>, B2: Qubit<A>>() -> impl Prop {
    eqv::<A, B1, B2>()
}

pub fn test2_eqv<A: Prop, B: Qubit<A>>() -> impl Prop {
    eqv::<A, B, B>()
}

pub fn test3_eqv<A1: Prop, A2: Prop, B1: Qubit<A1>, B2: Qubit<A2>>(
    q_a1_a2: Qual<A1, A2, B1, B2>
) -> Eq<B1, B2> {
    and::to_eq_pos(q_a1_a2.1)
}

pub fn test4_eqv<
    A: Prop,
    B1: ConQubit<A>,
    B2: ConQubit<A>,
    C1: ConQubit<B1>,
    C2: ConQubit<B2>,
>() -> Eq<B1, B2> {
    con_eqv::<A, B1, B2, C1, C2>().0
}

pub fn test5_eqv<
    A: Prop,
    B: ConQubit<A>,
    C1: ConQubit<B>,
    C2: ConQubit<B>,
    D1: ConQubit<C1>,
    D2: ConQubit<C2>,
>() -> Qual<C1, C2, D1, D2> {
    con_eqv::<B, C1, C2, D1, D2>()
}

pub fn test6_eqv<
    A: Prop,
    B1: Qubit<A>,
    B2: Qubit<A>,
>() -> Eq<B1, B2> {
    id_eqv::<A, A, B1, B2, Refl<A>>()
}

pub fn test7_eqv<
    A: Prop,
    B: ConQubit<A>,
    C1: ConQubit<B>,
    C2: ConQubit<B>,
    D1: ConQubit<C1>,
    D2: ConQubit<C2>,
>() -> Qual<C1, C2, D1, D2> {
    id_con_eqv::<B, B, C1, C2, D1, D2, Refl<B>>()
}

pub fn test8_eqv<
    A: Prop,
    B: Prop,
    P: Id<A, B>,
    C: Qubit<A>,
>() -> Eq<C, C> {
    id_eqv::<A, A, C, C, Trans<A, B, A, P, Sym<A, B, P>>>()
}

pub fn test9_eqv<
    A: IsProp,
    B: IsProp,
    P: Id<A, B> + IsProp,
    Q: Id<A, B> + IsProp,
>() -> Eq<P, Q> {
    id_ext::<P, Q, PropEqv<A, B, P, Q>>()
}

pub fn test10_eqv<
    A: IsProp,
    B: IsProp,
    P: Id<A, B> + IsProp,
    Q: Id<B, A>,
>() -> Eq<P, Sym<B, A, Q>> {
    id_ext::<P, Sym<B, A, Q>, PropEqv<A, B, P, Sym<B, A, Q>>>()
}

pub fn test11_eqv<
    A: IsProp,
    B: IsProp,
    P: Id<A, B> + IsProp,
    Q: Id<B, A> + IsProp,
>() -> Eq<P, Q> {
    id_ext::<P, Q, PropSym<A, B>>()
}

pub fn test12_eqv<
    A: IsProp,
    B: IsProp,
    C: IsProp,
    P: Id<A, B> + IsProp,
    Q: Id<B, C> + IsProp,
>() -> Eq<P, Q> {
    id_ext::<P, Q, PropTrans<A, B, C>>()
}

pub fn test13_eqv<
    A: IsProp,
>() {
    fn foo<A: Prop, B: Id<A, A>>(_e: B) {}

    let e = id_ext::<A, A, Refl<A>>();
    foo::<A, Eq<A, A>>(e)
}

pub fn test14_eqv<
    A: Prop,
    B: Prop
>(eq_a_b: Eq<A, B>) {
    fn foo<A: Prop, B: Prop, P: Id<A, B>>(_e: P) {}

    foo(eq_a_b)
}

pub fn test15_eqv<
    A: IsContr,
    B: IsContr,
>() {
    fn foo<A: Prop, B: Prop, P: Id<A, B>>() {}

    foo::<A, B, Eq<A, B>>()
}

pub fn test16_eqv<
    A: IsProp,
    B: IsProp,
>() -> Eq<A, B> {
    id_ext::<A, B, Eq<A, B>>()
}

pub fn test17_eqv<
    A: IsProp
>() -> impl IsContr {
    id_ext::<A, A, Eq<A, A>>()
}

pub fn test18_eqv<
    A: IsProp
>() -> impl IsProp {
    id_ext::<A, A, Eq<A, A>>()
}
