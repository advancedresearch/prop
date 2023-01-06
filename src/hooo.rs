//! # Exponential Propositions
//!
//! Paper: [HOOO Exponential Propositions](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/hooo-exponential-propositions.pdf)
//!
//! By using function pointers,
//! one can force construction of propositions
//! without capturing any variables,
//! such that the proposition is tautological true,
//! instead of just assuming it is true.
//!
//! When `a` is tautological provable from `b`,
//! one expresses it as `a^b`.
//!
//! It turns out that this has the same semantics
//! as [Higher Order Operator Overloading](https://github.com/advancedresearch/path_semantics/blob/master/sequences.md#higher-order-operator-overloading) (HOOO).
//!
//! One motivation for developing HOOO for Exponential Propositions
//! is to allow substitution in quality `~~` and qubit `~` operator
//! for Path Semantical Quantum Propositional Logic (PSQ).
//!
//! ### Comment conventions
//!
//! When a function comment says `a => b`, it is actually `(a => b)^true`.
//!
//! The exponent is left out to make the comments more consistent for the whole library.
//! Otherwise, it would be proper to use notation for Exponential Propositions everywhere,
//! but this is unpractical since Exponential Propositions is viewed as an extension of
//! normal Propositional Logic. One would like other modules to not use this notation
//! unless they rely on this extension explicitly.
//!
//! When `a^true` is used explicitly, the function returns a function pointer instead of using a
//! `_: True` argument, since it is natural in programming to not add unused arguments.

use crate::*;
use quality::Q;
use qubit::Qu;
use existence::{E, EProp};

impl<A: DProp, B: DProp> Decidable for Pow<A, B> {
    fn decide() -> ExcM<Self> {decide()}
}

/// `a^b ⋁ ¬(a^b)`.
pub fn decide<A: DProp, B: DProp>() -> ExcM<Pow<A, B>> {
    match tauto_to_or_pow() {
        Left(pow_ab) => Left(pow_ab),
        Right(pow_na_b) => {
            match para_decide::<B>() {
                Left(para_b) => Left(pow_transitivity(para_b, fa())),
                Right(npara_b) => {
                    match para_decide::<A>() {
                        Left(para_a) => {
                            Right(Rc::new(move |pow_ab| {
                                let para_b = pow_transitivity(pow_ab, para_a);
                                let nb: Not<B> = Rc::new(move |b| para_b(b));
                                let para_nb = pow_not(npara_b.clone());
                                para_nb(nb)
                            }))
                        }
                        Right(npara_a) => {
                            let para_na = pow_not(npara_a);
                            let para_b = pow_transitivity(pow_na_b, para_na);
                            let nb: Not<B> = Rc::new(move |b| para_b(b));
                            let para_nb = pow_not(npara_b);
                            imply::absurd()(para_nb(nb))
                        }
                    }

                }
            }
        }
    }
}

/// `a^true ⋁ ¬(a^true)`.
pub fn tauto_decide<A: DProp>() -> ExcM<Tauto<A>> {
    decide()
}

/// `¬¬(false^a) ⋁ ¬(false^a)`.
pub fn para_decide_e<A: EProp>() -> E<Para<A>> {
    fn g<A: EProp>(_: True) -> E<A> {A::e()}
    match hooo_or(pow_refl) {
        Left(pow_nna_ea) =>
            Right(para_rev_not(tauto_not_to_para(pow_transitivity(g, pow_nna_ea)))),
        Right(pow_na_ea) =>
            Left(not::double(tauto_not_to_para(pow_transitivity(g, pow_na_ea)))),
    }
}

/// `false^a ⋁ ¬(false^a)`.
pub fn para_decide<A: DProp>() -> ExcM<Para<A>> {
    match para_and_to_or(and::paradox) {
        Left(para_a) => Left(para_a),
        Right(para_na) => Right(para_rev_not(para_na)),
    }
}

/// `a^b`.
pub type Pow<A, B> = fn(B) -> A;

/// Power equivalence `=^=`.
pub type PowEq<A, B> = And<Pow<B, A>, Pow<A, B>>;

type NEq<A, B> = Not<Eq<A, B>>;

/// `a^b => (a^b)^c`.
pub fn pow_lift<A: Prop, B: Prop, C: Prop>(_: Pow<A, B>) -> Pow<Pow<A, B>, C> {
    unimplemented!()
}

/// `(a^b)^b => a^b`.
pub fn pow_rev_lift_refl<A: Prop, B: Prop>(x: Pow<Pow<A, B>, B>) -> Pow<A, B> {
    fn f<A: Prop, B: Prop>(b: B) -> Imply<Pow<A, B>, A> {
        Rc::new(move |pow_ab| pow_ab(b.clone()))
    }
    hooo_imply(f)(x)
}

/// `(a^b)^c => a^(b ⋀ c)`.
pub fn pow_lower<A: Prop, B: Prop, C: Prop>(x: Pow<Pow<A, B>, C>) -> Pow<A, And<B, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(pow_ab: Pow<A, B>) -> Pow<A, And<B, C>> {
        fn g<A: Prop, B: Prop>((a, _): And<A, B>) -> A {a}
        pow_transitivity(g, pow_ab)
    }
    fn g<A: Prop, B: Prop, C: Prop>(_: C) -> Imply<Pow<A, B>, Pow<A, And<B, C>>> {
        Rc::new(move |pow_ab| f(pow_ab))
    }
    fn h<A: Prop, B: Prop, C: Prop>(x: Pow<Pow<A, And<B, C>>, C>) -> Pow<A, And<B, C>> {
        fn f2<A: Prop, B: Prop, C: Prop>((b, c): And<B, C>) -> Imply<Pow<Pow<A, And<B, C>>, C>, A> {
            Rc::new(move |x| x(c.clone())((b.clone(), c.clone())))
        }
        hooo_imply(f2)(pow_lift(x))
    }
    h(hooo_imply(g)(x))
}

/// `a => a`.
pub fn pow_refl<A: Prop>(x: A) -> A {x}

/// `a^b ⋀ (a == c)^true => c^b`.
pub fn pow_in_left_arg<A: Prop, B: Prop, C: Prop>(
    x: Pow<A, B>,
    tauto_eq_a_c: Tauto<Eq<A, C>>,
) -> Pow<C, B> {
    fn f<A: Prop, C: Prop>((a, x): And<A, Tauto<Eq<A, C>>>) -> C {
        x(True).0(a)
    }
    pow_transitivity(hooo_rev_and((x, pow_lift(tauto_eq_a_c))), f)
}

/// `a^b ⋀ (b == c)^true => a^c`.
pub fn pow_in_right_arg<A: Prop, B: Prop, C: Prop>(
    x: Pow<A, B>,
    tauto_eq_b_c: Tauto<Eq<B, C>>,
) -> Pow<A, C> {
    fn f<B: Prop, C: Prop>(c: C) -> Imply<Tauto<Eq<B, C>>, B> {
        Rc::new(move |x| x(True).1(c.clone()))
    }
    let y: Pow<Tauto<Eq<B, C>>, C> = pow_lift(tauto_eq_b_c);
    let pow_bc: Pow<B, C> = hooo_imply(f)(y);
    pow_transitivity(pow_bc, x)
}

/// `a^(b ⋀ c) => a^(c ⋀ b)`
pub fn pow_right_and_symmetry<A: Prop, B: Prop, C: Prop>(
    x: Pow<A, And<B, C>>
) -> Pow<A, And<C, B>> {
    fn f<A: Prop, B: Prop>((a, b): And<A, B>) -> And<B, A> {(b, a)}
    pow_transitivity(f, x)
}

/// `¬(a^b) => a^(¬b)`.
pub fn pow_not<A: Prop, B: DProp>(x: Not<Pow<A, B>>) -> Pow<A, Not<B>> {
    match para_and_to_or(and::paradox) {
        Left(para_b) => not::absurd(x, pow_transitivity(para_b, fa())),
        Right(para_nb) => pow_transitivity(para_nb, fa()),
    }
}

/// `¬(a^b) => a^(¬b)`.
pub fn pow_not_e<A: Prop, B: EProp>(x: Not<Pow<A, B>>) -> Pow<A, Not<B>> {
    match para_not_and_to_or_e(and::paradox_e::<B>) {
        Left(para_nnb) =>
            not::absurd(x, pow_transitivity(not::double, pow_transitivity(para_nnb, fa()))),
        Right(para_nb) => pow_transitivity(para_nb, fa()),
    }
}

/// `¬(a^b) => a^(¬b)`.
pub fn pow_not_tauto_excm<A: Prop, B: Prop>(
    x: Not<Pow<A, B>>,
    tauto_excm_b: Tauto<ExcM<B>>,
) -> Pow<A, Not<B>> {
    let tauto_excm_nb = tauto_excm_to_tauto_excm_not(tauto_excm_b.clone());
    match para_and_to_or_excm(and::paradox, tauto_excm_b, tauto_excm_nb) {
        Left(para_b) => not::absurd(x, pow_transitivity(para_b, fa())),
        Right(para_nb) => pow_transitivity(para_nb, fa()),
    }
}

/// `a^(¬¬b) => (¬¬a)^b`.
pub fn pow_not_double_down<A: Prop, B: Prop>(x: Pow<A, Not<Not<B>>>) -> Pow<Not<Not<A>>, B> {
    pow_transitivity(not::double, pow_transitivity(x, not::double))
}

/// `b^a ⋀ c^b => c^a`.
pub fn pow_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: Pow<B, A>,
    bc: Pow<C, B>,
) -> Pow<C, A> {
    fn f<A: Prop, B: Prop, C: Prop>(a: A) -> Imply<And<Pow<B, A>, Pow<C, B>>, C> {
        Rc::new(move |(ab, bc)| bc(ab(a.clone())))
    }
    hooo_imply(f)(hooo_rev_and((pow_lift(ab), pow_lift(bc))))
}

/// `x =^= x`.
pub fn pow_eq_refl<A: Prop>() -> PowEq<A, A> {
    fn f<A: Prop>(a: A) -> A {a}
    (f, f)
}
/// `(x =^= y) => (y =^= x)`.
pub fn pow_eq_symmetry<A: Prop, B: Prop>((ab, ba): PowEq<A, B>) -> PowEq<B, A> {(ba, ab)}
/// `(x =^= y) ⋀ (y =^= z) => (x =^= z)`.
pub fn pow_eq_transitivity<A: Prop, B: Prop, C: Prop>(
    (ab, ba): PowEq<A, B>,
    (bc, cb): PowEq<B, C>
) -> PowEq<A, C> {
    let ca: Pow<A, C> = pow_transitivity(cb, ba);
    let ac: Pow<C, A> = pow_transitivity(ab, bc);
    (ac, ca)
}

/// `(x =^= y) => (a == b)^true`.
pub fn pow_eq_to_tauto_eq<A: Prop, B: Prop>((ba, ab): PowEq<A, B>) -> Tauto<Eq<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<Pow<A, B>, Imply<B, A>> {
        Rc::new(move |ba| Rc::new(move |b| ba(b)))
    }
    let f1 = hooo_imply(f);
    let tauto_ba = f1(pow_lift(ab));
    let f2 = hooo_imply(f);
    let tauto_ab = f2(pow_lift(ba));
    hooo_rev_and((tauto_ab, tauto_ba))
}

/// `(a == b)^true => (x =^= y)`.
pub fn tauto_eq_to_pow_eq<A: Prop, B: Prop>(x: Tauto<Eq<A, B>>) -> PowEq<A, B> {
    let pow_ab: Pow<A, B> = pow_in_right_arg(pow_refl, x.clone());
    let pow_ba: Pow<B, A> = pow_in_left_arg(pow_refl, x);
    (pow_ba, pow_ab)
}

/// `a^true => (a ⋁ ¬a)^true`.
pub fn tauto_to_tauto_excm<A: Prop>(x: Tauto<A>) -> Tauto<ExcM<A>> {
    hooo_rev_or(Left(x))
}

/// `false^a => (a ⋁ ¬a)^true`.
pub fn para_to_tauto_excm<A: Prop>(x: Para<A>) -> Tauto<ExcM<A>> {
    hooo_rev_or(Right(para_to_tauto_not(x)))
}

/// `(a ⋁ ¬a)^true => (¬a ⋁ ¬¬a)^true`.
pub fn tauto_excm_to_tauto_excm_not<A: Prop>(x: Tauto<ExcM<A>>) -> Tauto<ExcM<Not<A>>> {
    fn f<A: Prop>(_: True) -> Imply<ExcM<A>, ExcM<Not<A>>> {
        Rc::new(move |x| match x {
            Left(a) => Right(not::double(a)),
            Right(na) => Left(na),
        })
    }
    hooo_imply(f)(x)
}

/// `(¬(a^b))^true => (¬a)^b`.
pub fn tauto_hooo_rev_not<A: DProp, B: Prop>(x: Tauto<Not<Pow<A, B>>>) -> Pow<Not<A>, B> {
    hooo_imply(pow_to_imply_lift(hooo_rev_not))(x)(True)
}

/// `¬(a^b) => (¬a)^b`.
pub fn hooo_rev_not<A: DProp, B: Prop>(x: Not<Pow<A, B>>) -> Pow<Not<A>, B> {
    match tauto_to_or_pow() {
        Left(pow_ab) => not::absurd(x, pow_ab),
        Right(pow_na_b) => pow_na_b,
    }
}

/// `¬(¬¬(a)^b) => (¬a)^b`.
pub fn hooo_e_rev_not<A: EProp, B: Prop>(x: Not<Pow<Not<Not<A>>, B>>) -> Pow<Not<A>, B> {
    fn f<A: EProp, B: Prop>(_: B) -> E<A> {A::e()}
    match hooo_or(f) {
        Left(pow_nna_b) => not::absurd(x, pow_nna_b),
        Right(pow_na_b) => pow_na_b,
    }
}

/// `¬(a^b) ⋀ (a ⋁ ¬a)^true => (¬a)^b`.
pub fn hooo_rev_not_excm<A: Prop, B: Prop>(
    x: Not<Pow<A, B>>,
    y: Tauto<ExcM<A>>,
) -> Pow<Not<A>, B> {
    match tauto_excm_to_or_pow(y) {
        Left(pow_ab) => not::absurd(x, pow_ab),
        Right(pow_na_b) => pow_na_b,
    }
}

/// `(a ⋀ b)^c => (a^c ⋀ b^c)^true`.
pub fn tauto_hooo_and<A: Prop, B: Prop, C: Prop>(
    x: Pow<And<A, B>, C>
) -> Tauto<And<Pow<A, C>, Pow<B, C>>> {
    pow_transitivity(pow_lift(x), hooo_and)
}

/// `(a^c ⋀ b^c)^true => (a ⋀ b)^c`.
pub fn tauto_hooo_rev_and<A: Prop, B: Prop, C: Prop>(
    x: Tauto<And<Pow<A, C>, Pow<B, C>>>
) -> Pow<And<A, B>, C> {
    pow_transitivity(x, hooo_rev_and)(True)
}

/// `(a ⋀ b)^c => (a^c ⋀ b^c)`.
pub fn hooo_and<A: Prop, B: Prop, C: Prop>(x: Pow<And<A, B>, C>) -> And<Pow<A, C>, Pow<B, C>> {
    fn f<A: Prop, B: Prop>((a, _): And<A, B>) -> A {a}
    fn g<A: Prop, B: Prop>((_, b): And<A, B>) -> B {b}
    (pow_transitivity(x.clone(), f), pow_transitivity(x, g))
}

/// `(a^c ⋀ b^c) => (a ⋀ b)^c`.
pub fn hooo_rev_and<A: Prop, B: Prop, C: Prop>(
    x: And<Pow<A, C>, Pow<B, C>>
) -> Pow<And<A, B>, C> {
    let g = pow_to_imply(hooo_imply);
    let f = pow_to_imply_lift(imply::and_map);
    let f = imply::transitivity(hooo_imply(f), g);
    f(x.0)(x.1)
}

/// `c^(a ⋀ b) => (c^a ⋁ c^b)^true`.
///
/// This is only valid for decidable propositions.
pub fn tauto_hooo_dual_and<A: DProp, B: DProp, C: DProp>(
    x: Pow<C, And<A, B>>
) -> Tauto<Or<Pow<C, A>, Pow<C, B>>> {
    match Tauto::<Or<Pow<C, A>, Pow<C, B>>>::decide() {
        Left(y) => y,
        Right(ny) => {
            let y = hooo_rev_not(ny);
            let y = pow_transitivity(y, and::from_de_morgan);
            let (tauto_npow_ca, tauto_npow_cb) = hooo_and(y);
            let pow_nc_a = hooo_rev_not(tauto_npow_ca(True));
            let pow_nc_b = hooo_rev_not(tauto_npow_cb(True));
            let y = hooo_dual_rev_or((pow_nc_a, pow_nc_b));
            let y = pow_transitivity(and::to_or, y);
            let y = hooo_rev_and((x, y));
            let y = pow_transitivity(y, and::paradox);
            match para_and_to_or(y) {
                Left(para_a) => {
                    let pow_ca: Pow<C, A> = pow_transitivity(para_a, fa());
                    pow_transitivity(pow_lift(pow_ca), Left)
                }
                Right(para_b) => {
                    let pow_cb: Pow<C, B> = pow_transitivity(para_b, fa());
                    pow_transitivity(pow_lift(pow_cb), Right)
                }
            }
        }
    }
}

/// `(c^a ⋁ c^b)^true => c^(a ⋀ b)`.
pub fn tauto_hooo_dual_rev_and<A: Prop, B: Prop, C: Prop>(
    x: Tauto<Or<Pow<C, A>, Pow<C, B>>>
) -> Pow<C, And<A, B>> {
    pow_transitivity(x, hooo_dual_rev_and)(True)
}

/// `c^(a ⋀ b) => (c^a ⋁ c^b)`.
///
/// This is only valid for decidable propositions.
pub fn hooo_dual_and<A: DProp, B: DProp, C: DProp>(
    x: Pow<C, And<A, B>>
) -> Or<Pow<C, A>, Pow<C, B>> {
    tauto_hooo_dual_and(x)(True)
}

/// `(c^a ⋁ c^b) => c^(a ⋀ b)`.
pub fn hooo_dual_rev_and<A: Prop, B: Prop, C: Prop>(
    x: Or<Pow<C, A>, Pow<C, B>>
) -> Pow<C, And<A, B>> {
    match x {
        Left(pow_ca) => pow_lower(pow_lift(pow_ca)),
        Right(pow_cb) => pow_transitivity(and::symmetry, pow_lower(pow_lift(pow_cb))),
    }
}

/// `(a ⋁ b)^c => (a^c ⋁ b^c)^true`.
pub fn tauto_hooo_or<A: Prop, B: Prop, C: Prop>(
    _: Pow<Or<A, B>, C>
) -> Tauto<Or<Pow<A, C>, Pow<B, C>>> {
    unimplemented!()
}

/// `(a^c ⋁ b^c)^true => (a ⋁ b)^c`.
pub fn tauto_hooo_rev_or<A: Prop, B: Prop, C: Prop>(
    x: Tauto<Or<Pow<A, C>, Pow<B, C>>>
) -> Pow<Or<A, B>, C> {
    pow_transitivity(x, hooo_rev_or)(True)
}

/// `(a ⋁ b)^c => (a^c ⋁ b^c)`.
pub fn hooo_or<A: Prop, B: Prop, C: Prop>(
    x: Pow<Or<A, B>, C>
) -> Or<Pow<A, C>, Pow<B, C>> {
    tauto_hooo_or(x)(True)
}

/// `(a^c ⋁ b^c) => (a ⋁ b)^c`.
pub fn hooo_rev_or<A: Prop, B: Prop, C: Prop>(
    x: Or<Pow<A, C>, Pow<B, C>>
) -> Pow<Or<A, B>, C> {
    match x {
        Left(ca) => pow_transitivity(ca, Left),
        Right(cb) => pow_transitivity(cb, Right),
    }
}

/// `c^(a ⋁ b) => (c^a ⋀ c^b)^true`.
pub fn tauto_hooo_dual_or<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, Or<A, B>>
) -> Tauto<And<Pow<C, A>, Pow<C, B>>> {
    hooo_imply(pow_to_imply_lift(hooo_dual_or))(pow_lift(x))
}

/// `(c^a ⋀ c^b)^true => c^(a ⋁ b)`.
pub fn tauto_hooo_dual_rev_or<A: Prop, B: Prop, C: Prop>(
    x: Tauto<And<Pow<C, A>, Pow<C, B>>>
) -> Pow<C, Or<A, B>> {
    pow_transitivity(x, hooo_dual_rev_or)(True)
}

/// `c^(a ⋁ b) => (c^a ⋀ c^b)`.
pub fn hooo_dual_or<A: Prop, B: Prop, C: Prop>(
    x: Pow<C, Or<A, B>>
) -> And<Pow<C, A>, Pow<C, B>> {
    (pow_transitivity(Left, x.clone()), pow_transitivity(Right, x))
}

/// `(c^a ⋀ c^b) => c^(a ⋁ b)`.
pub fn hooo_dual_rev_or<A: Prop, B: Prop, C: Prop>(
    x: And<Pow<C, A>, Pow<C, B>>
) -> Pow<C, Or<A, B>> {
    match hooo_or(pow_refl::<Or<A, B>>) {
        Left(y) => pow_transitivity(y, x.0),
        Right(y) => pow_transitivity(y, x.1),
    }
}

/// `(a == b)^c => (a^c == b^c)^true`.
pub fn tauto_hooo_eq<A: Prop, B: Prop, C: Prop>(
    x: Pow<Eq<A, B>, C>
) -> Tauto<Eq<Pow<A, C>, Pow<B, C>>> {
    pow_transitivity(pow_lift(x), hooo_eq)
}

/// `(a^c == b^c)^true => (a == b)^c`.
///
/// This is only valid for decidable propositions.
pub fn tauto_hooo_rev_eq<A: DProp, B: DProp, C: DProp>(
    x: Tauto<Eq<Pow<A, C>, Pow<B, C>>>
) -> Pow<Eq<A, B>, C> {
    hooo_imply(pow_to_imply_lift(hooo_rev_eq))(x)(True)
}

/// `(a == b)^c => (a^c == b^c)`.
pub fn hooo_eq<A: Prop, B: Prop, C: Prop>(x: Pow<Eq<A, B>, C>) -> Eq<Pow<A, C>, Pow<B, C>> {
    fn f<A: Prop, B: Prop>(x: Eq<A, B>) -> Imply<A, B> {x.0}
    fn g<A: Prop, B: Prop>(x: Eq<A, B>) -> Imply<B, A> {x.1}
    let x1 = pow_transitivity(x.clone(), f);
    let x2 = pow_transitivity(x, g);
    (hooo_imply(x1), hooo_imply(x2))
}

/// `(a^c == b^c) => (a == b)^c`.
///
/// This is only valid for decidable propositions.
pub fn hooo_rev_eq<A: DProp, B: DProp, C: DProp>(x: Eq<Pow<A, C>, Pow<B, C>>) -> Pow<Eq<A, B>, C> {
    match Pow::<Eq<A, B>, C>::decide() {
        Left(y) => y,
        Right(ny) => {
            let y = hooo_rev_not(ny);
            let y = pow_transitivity(y, eq::neq_to_eq_not);
            let y = hooo_eq(y);
            let y = eq::transitivity(eq::symmetry(x), y);
            let y = match decide::<B, C>() {
                Left(pow_bc) => {
                    let pow_nb_c = y.0(pow_bc);
                    hooo_rev_and((pow_bc, pow_nb_c))
                }
                Right(npow_bc) => {
                    let pow_nb_c = hooo_rev_not(npow_bc);
                    let pow_bc = y.1(pow_nb_c);
                    hooo_rev_and((pow_bc, pow_nb_c))
                }
            };
            pow_transitivity(pow_transitivity(y, and::paradox), fa())
        }
    }
}

/// `(¬(c^a == c^b))^true => c^(a == b)`.
pub fn tauto_hooo_dual_rev_eq<A: DProp, B: DProp, C: DProp>(
    x: Tauto<Not<Eq<Pow<C, A>, Pow<C, B>>>>
) -> Pow<C, Eq<A, B>> {
    hooo_dual_rev_eq(x(True))
}

/// `¬(c^a == c^b) => c^(a == b)`.
pub fn hooo_dual_rev_eq<A: DProp, B: DProp, C: DProp>(
    x: Not<Eq<Pow<C, A>, Pow<C, B>>>
) -> Pow<C, Eq<A, B>> {
    match Pow::<C, Eq<A, B>>::decide() {
        Left(y) => y,
        Right(ny) => imply::absurd()(imply::in_left(x, |y| hooo_dual_neq(y))(pow_not(ny)))
    }
}

/// `(¬(a^c == b^c))^true => (¬(a == b))^c`.
pub fn tauto_hooo_rev_neq<A: DProp, B: DProp, C: Prop>(
    x: Tauto<NEq<Pow<A, C>, Pow<B, C>>>
) -> Pow<NEq<A, B>, C> {
    hooo_imply(pow_to_imply_lift(hooo_rev_neq))(x)(True)
}

/// `¬(a^c == b^c) => (¬(a == b))^c`.
pub fn hooo_rev_neq<A: DProp, B: DProp, C: Prop>(
    x: NEq<Pow<A, C>, Pow<B, C>>
) -> Pow<NEq<A, B>, C> {
    hooo_rev_not(imply::in_left(x, |y| hooo_eq(y)))
}

/// `c^(¬(a == b)) => (c^a == c^b)^true`.
pub fn tauto_hooo_dual_neq<A: DProp, B: DProp, C: DProp>(
    x: Pow<C, NEq<A, B>>
) -> Tauto<Eq<Pow<C, A>, Pow<C, B>>> {
    fn f<A: Prop, B: Prop, C: Prop>(x: Tauto<Eq<A, B>>) -> Eq<Pow<C, A>, Pow<C, B>> {
        (Rc::new(move |pow_ca| pow_in_right_arg(pow_ca, x)),
         Rc::new(move |pow_cb| pow_in_right_arg(pow_cb, tauto_eq_symmetry(x))))
    }
    fn g<A: Prop, B: Prop, C: Prop>(tauto_c: Tauto<C>) -> Eq<Pow<C, A>, Pow<C, B>> {
        (pow_transitivity(tr(), tauto_c).map_any(), pow_transitivity(tr(), tauto_c).map_any())
    }
    match Tauto::<Eq<Pow<C, A>, Pow<C, B>>>::decide() {
        Left(y) => y,
        Right(ny) => {
            let f: Imply<Tauto<Eq<A, B>>, Tauto<Eq<Pow<C, A>, Pow<C, B>>>> =
                Rc::new(move |x| hooo_imply(pow_to_imply_lift(f))(pow_lift(x)));
            let y: Not<Tauto<Eq<A, B>>> = imply::modus_tollens(f)(ny);
            let y: Tauto<Not<Eq<A, B>>> = hooo_rev_not(y);
            let y: Tauto<C> = pow_transitivity(y, x);
            hooo_imply(pow_to_imply_lift(g))(pow_lift(y))
        }
    }
}

/// `(c^a == c^b)^true => c^(¬(a == b))`.
pub fn tauto_hooo_dual_rev_neq<A: DProp, B: DProp, C: Prop>(
    x: Tauto<Eq<Pow<C, A>, Pow<C, B>>>
) -> Pow<C, NEq<A, B>> {
    fn f<A: Prop, B: Prop>(x: Eq<A, B>) -> Imply<A, B> {x.0}
    fn g<A: Prop, B: Prop>(x: Eq<A, B>) -> Imply<B, A> {x.1}
    let x0 = tauto_hooo_dual_rev_nrimply(pow_transitivity(x, f));
    let x1 = tauto_hooo_dual_rev_nrimply(pow_transitivity(x, g));
    let y = hooo_dual_rev_or((x0, x1));
    pow_transitivity(eq::neq_symmetry, pow_transitivity(or::from_de_morgan, y))
}

/// `c^(¬(a == b)) => (c^a == c^b)`.
pub fn hooo_dual_neq<A: DProp, B: DProp, C: DProp>(
    x: Pow<C, NEq<A, B>>
) -> Eq<Pow<C, A>, Pow<C, B>> {
    tauto_hooo_dual_neq(x)(True)
}

/// `(c^a == c^b) => c^(¬(a == b))`.
pub fn hooo_dual_rev_neq<A: DProp, B: DProp, C: DProp>(
    (x0, x1): Eq<Pow<C, A>, Pow<C, B>>
) -> Pow<C, NEq<A, B>> {
    let y = hooo_dual_rev_or((hooo_dual_rev_nrimply(x0), hooo_dual_rev_nrimply(x1)));
    pow_transitivity(eq::neq_symmetry, pow_transitivity(or::from_de_morgan, y))
}

/// `(a => b)^c => (a^c => b^c)^true`.
pub fn tauto_hooo_imply<A: Prop, B: Prop, C: Prop>(
    _: Pow<Imply<A, B>, C>
) -> Tauto<Imply<Pow<A, C>, Pow<B, C>>> {
    unimplemented!()
}

/// `(a => b)^c => (a^c => b^c)`.
pub fn hooo_imply<A: Prop, B: Prop, C: Prop>(
    x: Pow<Imply<A, B>, C>
) -> Imply<Pow<A, C>, Pow<B, C>> {
    tauto_hooo_imply(x)(True)
}

/// `(¬(c^b => c^a))^true => c^(a => b)`.
pub fn tauto_hooo_dual_rev_imply<A: DProp, B: DProp, C: DProp>(
    x: Tauto<Not<Imply<Pow<C, B>, Pow<C, A>>>>
) -> Pow<C, Imply<A, B>> {
    hooo_imply(pow_to_imply_lift(hooo_dual_rev_imply))(x)(True)
}

/// `¬(c^b => c^a) => c^(a => b)`.
pub fn hooo_dual_rev_imply<A: DProp, B: DProp, C: DProp>(
    x: Not<Imply<Pow<C, B>, Pow<C, A>>>
) -> Pow<C, Imply<A, B>> {
    match Pow::<C, Imply<A, B>>::decide() {
        Left(y) => y,
        Right(ny) => {
            let y: Imply<Pow<C, B>, Pow<C, A>> = hooo_dual_nrimply(pow_not(ny));
            not::absurd(x, y)
        }
    }
}

/// `(¬(b^c => a^c))^true => (¬(b => a))^c`.
pub fn tauto_hooo_rev_nrimply<A: DProp, B: DProp, C: Prop>(
    x: Tauto<Not<Imply<Pow<B, C>, Pow<A, C>>>>
) -> Pow<Not<Imply<B, A>>, C> {
    hooo_imply(pow_to_imply_lift(hooo_rev_nrimply))(x)(True)
}

/// `¬(b^c => a^c) => (¬(b => a))^c`.
pub fn hooo_rev_nrimply<A: DProp, B: DProp, C: Prop>(
    x: Not<Imply<Pow<B, C>, Pow<A, C>>>
) -> Pow<Not<Imply<B, A>>, C> {
    hooo_rev_not(imply::in_left(x, |x| hooo_imply(x)))
}

/// `c^(¬(b => a)) => (c^a => c^b)^true`.
pub fn tauto_hooo_dual_nrimply<A: DProp, B: DProp, C: DProp>(
    x: Pow<C, Not<Imply<B, A>>>
) -> Tauto<Imply<Pow<C, A>, Pow<C, B>>> {
    fn f<A: Prop, B: Prop, C: Prop>(x: Tauto<Imply<B, A>>) -> Imply<Pow<C, A>, Pow<C, B>> {
        Rc::new(move |pow_ca| pow_transitivity(tauto_imply_to_pow(x), pow_ca))
    }
    fn g<A: Prop, B: Prop, C: Prop>(tauto_c: Tauto<C>) -> Imply<Pow<C, A>, Pow<C, B>> {
        pow_transitivity(tr(), tauto_c).map_any()
    }
    match Tauto::<Imply<Pow<C, A>, Pow<C, B>>>::decide() {
        Left(y) => y,
        Right(ny) => {
            let f: Imply<Tauto<Imply<B, A>>, Tauto<Imply<Pow<C, A>, Pow<C, B>>>> =
                Rc::new(move |x| hooo_imply(pow_to_imply_lift(f))(pow_lift(x)));
            let y: Not<Tauto<Imply<B, A>>> = imply::modus_tollens(f)(ny);
            let y: Tauto<Not<Imply<B, A>>> = hooo_rev_not(y);
            let y: Tauto<C> = pow_transitivity(y, x);
            hooo_imply(pow_to_imply_lift(g))(pow_lift(y))
        }
    }
}

/// `(c^a => c^b)^true => c^(¬(b => a))`.
pub fn tauto_hooo_dual_rev_nrimply<A: DProp, B: DProp, C: Prop>(
    x: Tauto<Imply<Pow<C, A>, Pow<C, B>>>
) -> Pow<C, Not<Imply<B, A>>> {
    fn f<A: DProp, B: DProp, C: Prop>(
        nba: Not<Imply<B, A>>
    ) -> Imply<Imply<Pow<C, A>, Pow<C, B>>, C> {
        Rc::new(move |x| {
            let y: Not<Or<Not<B>, A>> = imply::in_left(nba.clone(), |y| imply::from_or(y));
            let (nnb, na): And<Not<Not<B>>, Not<A>> = and::from_de_morgan(y);
            let npara_na: Not<Para<Not<A>>> = not_not_to_not_para(not::double(na));
            let nnpara_a: Not<Not<Para<A>>> = imply::in_left(npara_na, |y| pow_not(y));
            let para_a = not::rev_double(nnpara_a);
            let pow_ca: Pow<C, A> = pow_transitivity(para_a, fa());
            let pow_cb: Pow<C, B> = x(pow_ca);
            let b = not::rev_double(nnb);
            pow_cb(b)
        })
    }
    hooo_imply(f)(pow_to_imply_lift(tauto_imply_to_pow(x)))
}

/// `c^(¬(b => a)) => (c^a => c^b)`.
pub fn hooo_dual_nrimply<A: DProp, B: DProp, C: DProp>(
    x: Pow<C, Not<Imply<B, A>>>
) -> Imply<Pow<C, A>, Pow<C, B>> {
    tauto_hooo_dual_nrimply(x)(True)
}

/// `(c^a => c^b) => c^(¬(b => a))`.
pub fn hooo_dual_rev_nrimply<A: DProp, B: DProp, C: DProp>(
    x: Imply<Pow<C, A>, Pow<C, B>>
) -> Pow<C, Not<Imply<B, A>>> {
    match Tauto::<Imply<Pow<C, A>, Pow<C, B>>>::decide() {
        Left(y) => tauto_hooo_dual_rev_nrimply(y),
        Right(ny) => imply::absurd()(hooo_rev_not(ny)(True)(x)),
    }
}

/// A tautological proposition.
pub type Tauto<A> = fn(True) -> A;

/// A paradoxical proposition.
pub type Para<A> = fn(A) -> False;

/// A uniform proposition.
pub type Uniform<A> = Or<Tauto<A>, Para<A>>;

/// A proposition is a theory when non-uniform.
pub type Theory<A> = Not<Uniform<A>>;

/// Lift equality with tautological distinction into quality.
pub fn lift_q<A: Prop, B: Prop>(
    _: Eq<A, B>,
    _: Theory<Eq<A, B>>
) -> Q<A, B> {unimplemented!()}

/// `~a ∧ (a == b)^true  =>  ~b`.
pub fn qu_in_arg<A: Prop, B: Prop>(x: Qu<A>, y: Tauto<Eq<A, B>>) -> Qu<B> {
    qubit::in_arg(x, y)
}

/// `(a ~~ b) ∧ (a == c)^true  =>  (c ~~ b)`.
pub fn q_in_left_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qu_a, qu_b)): Q<A, B>,
    g: Tauto<Eq<A, C>>
) -> Q<C, B> {
    (eq::in_left_arg(eq_ab, g(True)), (qu_in_arg(qu_a, g), qu_b))
}

/// `(a ~~ b) ∧ (b == c)^true  =>  (a ~~ c)`.
pub fn q_in_right_arg<A: Prop, B: Prop, C: Prop>(
    (eq_ab, (qu_a, qu_b)): Q<A, B>,
    g: Tauto<Eq<B, C>>
) -> Q<A, C> {
    (eq::in_right_arg(eq_ab, g(True)), (qu_a, qu_in_arg(qu_b, g)))
}

/// `true^a`.
pub fn tr<A: Prop>() -> Pow<True, A> {
    fn f<A: Prop>(_: A) -> True {True}
    f::<A>
}

/// `a^false`.
pub fn fa<A: Prop>() -> Pow<A, False> {
    fn f<A: Prop>(x: False) -> A {imply::absurd()(x)}
    f::<A>
}

/// `¬(false^true)`.
///
/// A consistent logic can't prove `false` without further assumptions.
pub fn consistency() -> Not<Tauto<False>> {
    Rc::new(move |f| f(True))
}

/// `a^true ∧ (a == b)^true => b^true`.
pub fn tauto_in_arg<A: Prop, B: Prop>(
    a: Tauto<A>,
    eq: Tauto<Eq<A, B>>
) -> Tauto<B> {
    hooo_eq(eq).0(a)
}

/// `a^true => (a == true)^true`.
pub fn tauto_to_eq_true<A: Prop>(
    x: Tauto<A>
) -> Tauto<Eq<A, True>> {
    fn f<A: Prop>(_: True) -> Imply<A, Eq<A, True>> {
        Rc::new(move |a| (True.map_any(), a.map_any()))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `(a == true)^true => a^true`.
pub fn tauto_from_eq_true<A: Prop>(
    x: Tauto<Eq<A, True>>
) -> Tauto<A> {
    fn f<A: Prop>(_: True) -> Imply<Eq<A, True>, A> {
        Rc::new(move |eq| eq.1(True))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `false^a => (a == false)^true`.
pub fn para_to_eq_false<A: DProp>(
    x: Para<A>
) -> Tauto<Eq<A, False>> {
    let y: Not<Tauto<A>> = Rc::new(move |tauto_a| {
        x(tauto_a(True))
    });
    let eq: Eq<Not<Tauto<False>>, Not<Tauto<A>>> = (
        y.map_any(),
        consistency().map_any(),
    );
    let eq2: Eq<Tauto<A>, Tauto<False>> = eq::rev_modus_tollens_excm(
        eq, tauto_decide(), tauto_decide());
    hooo_rev_eq(eq2)
}

/// `¬(x^true) => (¬x)^true`.
pub fn tauto_not<A: DProp>(x: Not<Tauto<A>>) -> Tauto<Not<A>> {
    hooo_rev_not(x)
}

/// `¬(x^true) ⋀ (a ⋁ ¬a)^true => (¬x)^true`.
pub fn tauto_not_excm<A: Prop>(x: Not<Tauto<A>>, y: Tauto<ExcM<A>>) -> Tauto<Not<A>> {
    hooo_rev_not_excm(x, y)
}

/// `(¬x)^true => ¬(x^true)`.
pub fn tauto_rev_not<A: Prop>(x: Tauto<Not<A>>) -> Not<Tauto<A>> {
    Rc::new(move |tauto_a| x(True)(tauto_a(True)))
}

/// `(¬a)^true => false^a`.
pub fn tauto_not_to_para<A: Prop>(x: Tauto<Not<A>>) -> Para<A> {
    fn f<A: Prop>(a: A) -> Imply<Tauto<Not<A>>, False> {
        Rc::new(move |x| x(True)(a.clone()))
    }
    hooo_imply(f)(pow_lift(x))
}

/// `false^a => (¬a)^true`.
pub fn para_to_tauto_not<A: Prop>(x: Para<A>) -> Tauto<Not<A>> {
    fn f<A: Prop>(_: True) -> Imply<Para<A>, Not<A>> {
        Rc::new(move |x| Rc::new(move |a| x(a)))
    }
    let x: Tauto<Para<A>> = pow_lift(x);
    hooo_imply(f)(x)
}

/// `a^true => false^(¬a)`.
pub fn tauto_to_para_not<A: Prop>(x: Tauto<A>) -> Para<Not<A>> {
    let y: Not<Para<A>> = Rc::new(move |para_a| para_a(x(True)));
    let tauto_excm_a: Tauto<ExcM<A>> = pow_transitivity(x, Left);
    pow_not_tauto_excm(y, tauto_excm_a)
}

/// `false^(¬a) => ¬¬(a^true)`.
pub fn para_not_to_not_not_tauto<A: DProp>(x: Para<Not<A>>) -> Not<Not<Tauto<A>>> {
    Rc::new(move |ntauto_a| x(hooo_rev_not(ntauto_a)(True)))
}

/// `x^true => (¬¬x)^true`.
pub fn tauto_not_double<A: Prop>(x: Tauto<A>) -> Tauto<Not<Not<A>>> {
    fn f<A: Prop>(_: True) -> Imply<A, Not<Not<A>>> {
        Rc::new(move |a| not::double(a))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `false^(¬x) => (¬false^x)^true`.
pub fn tauto_para_rev_not<A: Prop>(para_na: Para<Not<A>>) -> Tauto<Not<Para<A>>> {
    pow_transitivity(pow_lift(para_na), para_rev_not)
}

/// `false^(¬x) => false^(false^x)`.
pub fn para_not_to_para_para<A: Prop>(x: Para<Not<A>>) -> Para<Para<A>> {
    pow_transitivity(para_to_not, x)
}

/// `¬(false^a) => false^(¬a)`.
pub fn para_not<A: EProp>(npara_a: Not<Para<A>>) -> Para<Not<A>> {pow_not_e(npara_a)}

/// `false^(¬x) => ¬false^x`.
pub fn para_rev_not<A: Prop>(para_na: Para<Not<A>>) -> Not<Para<A>> {
    Rc::new(move |para_a| para_na(Rc::new(move |a| para_a(a))))
}

/// `false^a => false^(¬¬a)`.
pub fn para_not_double<A: Prop>(x: Para<A>) -> Para<Not<Not<A>>> {
    let y: Tauto<ExcM<Not<A>>> = tauto_excm_to_tauto_excm_not(para_to_tauto_excm(x.clone()));
    pow_not_tauto_excm(imply::in_left(not::double(x), |x: Para<Not<A>>| para_rev_not(x)), y)
}

/// `false^(¬¬a) => false^a`.
pub fn para_not_rev_double<A: Prop>(x: Para<Not<Not<A>>>) -> Para<A> {
    pow_transitivity(not::double, x)
}

/// `false^(¬x) => false^(¬¬¬x)`.
pub fn para_not_triple<A: Prop>(x: Para<Not<A>>) -> Para<Not<Not<Not<A>>>> {
    pow_transitivity(not::rev_triple, x)
}

/// `false^(¬¬¬x) => false^(¬x)`.
pub fn para_not_rev_triple<A: Prop>(x: Para<Not<Not<Not<A>>>>) -> Para<Not<A>> {
    pow_transitivity(not::double, x)
}

/// `false^x => ¬x`.
pub fn para_to_not<A: Prop>(para_a: Para<A>) -> Not<A> {Rc::new(move |a| para_a(a))}

/// `¬(false^a) => false^(false^a)`.
pub fn not_para_to_para_para<A: DProp>(npara_a: Not<Para<A>>) -> Para<Para<A>> {
    pow_transitivity(para_to_not, pow_not(npara_a))
}

/// `¬(false^a) ⋀ (a ⋁ ¬a)^true  =>  false^(false^a)`.
pub fn not_para_to_para_para_with_tauto_excm<A: Prop>(
    npara_a: Not<Para<A>>,
    tauto_excm: Tauto<ExcM<A>>
) -> Para<Para<A>> {
    pow_transitivity(para_to_not, pow_not_tauto_excm(npara_a, tauto_excm))
}

/// `¬(false^a) => false^(false^a)`.
pub fn not_para_to_para_para_e<A: EProp>(npara_a: Not<Para<A>>) -> Para<Para<A>> {
    pow_transitivity(para_to_not, pow_not_e(npara_a))
}

/// `false^(false^a) => ¬(false^a)`.
pub fn para_para_to_not_para<A: Prop>(para_para_a: Para<Para<A>>) -> Not<Para<A>> {
    Rc::new(move |para_a| para_para_a(para_a))
}

/// `¬¬a => ¬(false^a)`.
pub fn not_not_to_not_para<A: Prop>(nna: Not<Not<A>>) -> Not<Para<A>> {
    imply::in_left(nna, para_to_not)
}

/// `¬(false^a) => ¬¬a`.
pub fn not_para_to_not_not<A: DProp>(npara_a: Not<Para<A>>) -> Not<Not<A>> {
    Rc::new(move |na| pow_not(npara_a.clone())(na))
}

/// `¬(false^a) => ¬¬a`.
pub fn not_para_to_not_not_e<A: EProp>(npara_a: Not<Para<A>>) -> Not<Not<A>> {
    Rc::new(move |na| pow_not_e(npara_a.clone())(na))
}

/// `¬¬a => false^(false^a)`.
pub fn not_not_to_para_para<A: DProp>(nna: Not<Not<A>>) -> Para<Para<A>> {
    not_para_to_para_para(not_not_to_not_para(nna))
}

/// `¬¬a ⋀ (a ⋁ ¬a)^true  =>  false^(false^a)`.
pub fn not_not_to_para_para_with_tauto_excm<A: Prop>(
    nna: Not<Not<A>>,
    tauto_excm: Tauto<ExcM<A>>
) -> Para<Para<A>> {
    not_para_to_para_para_with_tauto_excm(not_not_to_not_para(nna), tauto_excm)
}

/// `¬¬a => false^(false^a)`.
pub fn not_not_to_para_para_e<A: EProp>(nna: Not<Not<A>>) -> Para<Para<A>> {
    not_para_to_para_para_e(not_not_to_not_para(nna))
}

/// `false^(false^a) => ¬¬a`.
pub fn para_para_to_not_not<A: DProp>(para_para_a: Para<Para<A>>) -> Not<Not<A>> {
    Rc::new(move |na| pow_not(para_para_to_not_para(para_para_a))(na))
}

/// `a => false^(false^a)`.
pub fn para_para<A: DProp>(a: A) -> Para<Para<A>> {
    not_not_to_para_para(not::double(a))
}

/// `(¬(false^a) == ¬(false^b)) => (false^a == false^b)`.
pub fn eq_not_para_to_eq_para<A: DProp, B: DProp>(
    eq_npara_a_npara_b: Eq<Not<Para<A>>, Not<Para<B>>>
) -> Eq<Para<A>, Para<B>> {
    fn f<A: DProp>() -> Eq<Not<Not<Para<A>>>, Para<A>> {
        (
            Rc::new(move |nnpara_a| {
                let x: Not<Para<Not<A>>> = imply::in_left(nnpara_a,
                    |x: Para<Not<A>>| para_rev_not(x));
                para_not_rev_double(pow_not(x))
            }),
            Rc::new(move |para_a| not::double(para_a))
        )
    }
    let x = eq::modus_tollens(eq_npara_a_npara_b);
    let x: Eq<Para<B>, Not<Not<Para<A>>>> = eq::in_left_arg(x, f());
    eq::in_left_arg(eq::symmetry(x), f())
}

/// `(x == x)^true`.
pub fn eq_refl<A: Prop>() -> Tauto<Eq<A, A>> {
    fn f<A: Prop>(_: True) -> Eq<A, A> {eq::refl()}
    f::<A>
}

/// `(x == y)^true => (y == x)^true`.
pub fn tauto_eq_symmetry<A: Prop, B: Prop>(x: Tauto<Eq<A, B>>) -> Tauto<Eq<B, A>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<Eq<A, B>, Eq<B, A>> {
        Rc::new(move |ab| eq::symmetry(ab))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `false^(x == y) => false^(y == x)`.
pub fn para_eq_symmetry<A: Prop, B: Prop>(x: Para<Eq<A, B>>) -> Para<Eq<B, A>> {
    pow_transitivity(eq::symmetry, x)
}

/// `(a == b)^true ∧ (b == c)^true => (a == c)^true`.
pub fn tauto_eq_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Eq<A, B>>,
    bc: Tauto<Eq<B, C>>
) -> Tauto<Eq<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True) ->
    Imply<Eq<A, B>, Imply<Eq<B, C>, Eq<A, C>>> {
        Rc::new(move |ab| Rc::new(move |bc| eq::transitivity(ab.clone(), bc)))
    }
    let f = hooo_imply(f);
    let g = hooo_imply(f(ab));
    g(bc)
}

pub use tauto_eq_transitivity as tauto_eq_in_right_arg;

/// `(a == b) ∧ (a == c) => (c == b)`.
pub fn tauto_eq_in_left_arg<A: Prop, B: Prop, C: Prop>(
    f: Tauto<Eq<A, B>>,
    g: Tauto<Eq<A, C>>,
) -> Tauto<Eq<C, B>> {
    tauto_eq_transitivity(tauto_eq_symmetry(g), f)
}

/// `uniform(a) ⋁ false^uniform(a)`.
pub fn program<A: DProp>() -> Or<Uniform<A>, Para<Uniform<A>>> {
    match para_decide::<A>() {
        Left(para_a) => Left(Right(para_a)),
        Right(npara_a) => {
            let nntauto_a = para_not_to_not_not_tauto(pow_not(npara_a));
            match tauto_decide::<A>() {
                Left(tauto_a) => Left(Left(tauto_a)),
                Right(ntauto_a) => not::absurd(nntauto_a, ntauto_a),
            }
        }
    }
}

/// `(a^true => b^true) => (false^b => false^a)`.
pub fn imply_tauto_to_imply_para<A: DProp, B: Prop>(
    x: Imply<Tauto<A>, Tauto<B>>
) -> Imply<Para<B>, Para<A>> {
    Rc::new(move |para_b| {
        let x = imply::modus_tollens(x.clone());
        tauto_not_to_para(tauto_not(x(tauto_rev_not(para_to_tauto_not(para_b)))))
    })
}

/// `(a^true => b^true) => (false^b => false^a)`.
pub fn imply_tauto_to_imply_para_excm<A: Prop, B: Prop>(
    x: Imply<Tauto<A>, Tauto<B>>,
    y: Tauto<ExcM<A>>
) -> Imply<Para<B>, Para<A>> {
    Rc::new(move |para_b| {
        let x = imply::modus_tollens(x.clone());
        tauto_not_to_para(tauto_not_excm(x(tauto_rev_not(para_to_tauto_not(para_b))), y))
    })
}

/// `(a^true == b^true) => (false^a == false^b)`.
pub fn eq_tauto_to_eq_para<A: DProp, B: DProp>(
    x: Eq<Tauto<A>, Tauto<B>>
) -> Eq<Para<A>, Para<B>> {
    let y0 = imply_tauto_to_imply_para(x.0);
    let y1 = imply_tauto_to_imply_para(x.1);
    (y1, y0)
}

/// `(a^true == b^true) => (false^a == false^b)`.
pub fn eq_tauto_to_eq_para_excm<A: Prop, B: Prop>(
    x: Eq<Tauto<A>, Tauto<B>>,
    excm_a: Tauto<ExcM<A>>,
    excm_b: Tauto<ExcM<B>>,
) -> Eq<Para<A>, Para<B>> {
    let y0 = imply_tauto_to_imply_para_excm(x.0, excm_a);
    let y1 = imply_tauto_to_imply_para_excm(x.1, excm_b);
    (y1, y0)
}

/// `(a^true == false^a) => false^uniform(a)`.
pub fn eq_tauto_para_to_para_uniform<A: DProp>(eq: Eq<Tauto<A>, Para<A>>) -> Para<Uniform<A>> {
    not::absurd(Para::<A>::nnexcm(), Rc::new(move |excm| {
        let eq = eq.clone();
        match excm {
            Left(para_a) => para_a(eq.1(para_a)(True)),
            Right(npara_a) => {
                let x = eq::modus_tollens(eq).0(npara_a.clone());
                npara_a(tauto_not_to_para(hooo_rev_not(x)))
            }
        }
    }))
}

/// `false^uniform(a) => (a^true == false^a)`.
pub fn para_uniform_to_eq_tauto_para<A: Prop>(
    para_uni: Para<Uniform<A>>
) -> Eq<Tauto<A>, Para<A>> {
    (
        Rc::new(move |tauto_a| imply::absurd()(para_uni(Left(tauto_a)))),
        Rc::new(move |para_a| imply::absurd()(para_uni(Right(para_a)))),
    )
}

/// `(false^a ∧ (a == b)^true) => false^b`.
pub fn para_in_arg<A: Prop, B: Prop>(
    para_a: Para<A>,
    tauto_eq_a_b: Tauto<Eq<A, B>>
) -> Para<B> {
    let y0 = para_to_tauto_excm(para_a);
    let y1 = para_to_tauto_excm_transitivity(para_a.clone(), tauto_eq_a_b.clone());
    let eq = hooo_eq(tauto_eq_a_b);
    let eq2 = eq_tauto_to_eq_para_excm(eq, y0, y1);
    eq2.0(para_a)
}

/// `false^a ∧ (a == b)^true => (b ⋁ ¬b)^true`.
pub fn para_to_tauto_excm_transitivity<A: Prop, B: Prop>(
    para_a: Para<A>, x: Tauto<Eq<A, B>>
) -> Tauto<ExcM<B>> {
    fn f<A: Prop, B: Prop>(x: Eq<A, B>) -> Imply<Not<A>, Not<B>> {
        Rc::new(move |na| eq::modus_tollens(x.clone()).1(na))
    }
    para_to_tauto_excm(tauto_not_to_para(
        hooo_imply(pow_transitivity(x, f))(para_to_tauto_not(para_a))
    ))
}

/// `(false^(a == b) ∧ (b == c)^true) => false^(a == c)`.
pub fn para_eq_transitivity_left<A: Prop, B: Prop, C: Prop>(
    ab: Para<Eq<A, B>>,
    bc: Tauto<Eq<B, C>>
) -> Para<Eq<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>((neq_ab, eq_bc): And<Not<Eq<A, B>>, Eq<B, C>>) -> Not<Eq<A, C>> {
        Rc::new(move |eq_ac| neq_ab(eq::transitivity(eq_ac, eq::symmetry(eq_bc.clone()))))
    }
    let ab = para_to_tauto_not(ab);
    let x = hooo_rev_and((ab, bc));
    tauto_not_to_para(pow_transitivity(x, f))
}

/// `((a == b)^true ∧ false^(b == c)) => false^(a == c)`.
pub fn para_eq_transitivity_right<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Eq<A, B>>,
    bc: Para<Eq<B, C>>
) -> Para<Eq<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>((neq_bc, eq_ab): And<Not<Eq<B, C>>, Eq<A, B>>) -> Not<Eq<A, C>> {
        Rc::new(move |eq_ac| {
            let eq_bc: Eq<B, C> = eq::transitivity(eq::symmetry(eq_ab.clone()), eq_ac);
            neq_bc(eq_bc)
        })
    }
    let bc = para_to_tauto_not(bc);
    let x = hooo_rev_and((bc, ab));
    tauto_not_to_para(pow_transitivity(x, f))
}

/// `x => x`.
pub fn imply_refl<A: Prop>() -> Imply<A, A> {
    Rc::new(move |x| x)
}

/// `(a => b)^true ∧ (b => c)^true => (a => c)^true`.
pub fn tauto_imply_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Imply<A, B>>,
    bc: Tauto<Imply<B, C>>,
) -> Tauto<Imply<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True) -> Imply<And<Imply<A, B>, Imply<B, C>>, Imply<A, C>> {
        Rc::new(move |(ab, bc)| imply::transitivity(ab, bc))
    }
    let f = hooo_imply(f::<A, B, C>);
    let x = hooo_rev_and((ab, bc));
    f(x)
}

/// `(a^true ∧ b^true) => (a == b)^true`.
pub fn tauto_and_to_eq_pos<A: Prop, B: Prop>(a: Tauto<A>, b: Tauto<B>) -> Tauto<Eq<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<And<A, B>, Eq<A, B>> {
        Rc::new(move |ab| and::to_eq_pos(ab))
    }
    let f = hooo_imply(f::<A, B>);
    let x = hooo_rev_and((a, b));
    f(x)
}

/// `a^true => (a ⋁ b)^true`.
pub fn tauto_or_left<A: Prop, B: Prop>(
    x: Tauto<A>
) -> Tauto<Or<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<A, Or<A, B>> {
        Rc::new(move |a| Left(a))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `b^true => (a ⋁ b)^true`.
pub fn tauto_or_right<A: Prop, B: Prop>(
    x: Tauto<B>
) -> Tauto<Or<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<B, Or<A, B>> {
        Rc::new(move |b| Right(b))
    }
    let f = hooo_imply(f);
    f(x)
}

/// `(a^true ⋁ b^true) => (a ⋁ b)^true`.
pub fn tauto_or<A: Prop, B: Prop>(or_ab: Or<Tauto<A>, Tauto<B>>) -> Tauto<Or<A, B>> {
    match or_ab {
        Left(tauto_a) => tauto_or_left(tauto_a),
        Right(tauto_b) => tauto_or_right(tauto_b),
    }
}

/// `(a ⋁ b)^true => (a^true ⋁ b^true)`.
pub fn tauto_rev_or<A: Prop, B: Prop>(x: Tauto<Or<A, B>>) -> Or<Tauto<A>, Tauto<B>> {
    hooo_or(x)
}

/// `a^true ⋁ (¬a)^true`.
pub fn tauto_to_or<A: DProp>() -> Or<Tauto<A>, Tauto<Not<A>>> {
    fn f<A: DProp>(_: True) -> ExcM<A> {A::decide()}
    tauto_excm_to_or(f)
}

/// `(a ⋁ ¬a)^true => (a^true ⋁ (¬a)^true)`.
pub fn tauto_excm_to_or<A: Prop>(x: Tauto<ExcM<A>>) -> Or<Tauto<A>, Tauto<Not<A>>> {
    hooo_or(x)
}

/// `a^b ⋁ (¬a)^b`.
pub fn tauto_to_or_pow<A: DProp, B: Prop>() -> Or<Pow<A, B>, Pow<Not<A>, B>> {
    match tauto_to_or() {
        Left(tauto_a) => Left(pow_transitivity(tr(), tauto_a)),
        Right(tauto_na) => Right(pow_transitivity(tr(), tauto_na)),
    }
}

/// `(a ⋁ ¬a)^true => (a^b ⋁ (¬a)^b)`.
pub fn tauto_excm_to_or_pow<A: Prop, B: Prop>(x: Tauto<ExcM<A>>) -> Or<Pow<A, B>, Pow<Not<A>, B>> {
    match tauto_excm_to_or(x) {
        Left(tauto_a) => Left(pow_transitivity(tr(), tauto_a)),
        Right(tauto_na) => Right(pow_transitivity(tr(), tauto_na)),
    }
}

/// `(false^a ∧ false^b) => false^(a ⋁ b)`.
pub fn para_to_or<A: Prop, B: Prop>(
    para_a: Para<A>,
    para_b: Para<B>
) -> Para<Or<A, B>> {
    hooo_dual_rev_or((para_a, para_b))
}

/// `false^(a ⋁ b) => false^a ∧ false^b`.
pub fn para_from_or<A: Prop, B: Prop>(
    x: Para<Or<A, B>>,
) -> And<Para<A>, Para<B>> {
    hooo_dual_or(x)
}

/// `false^(a ∧ b) => false^a ⋁ false^b`.
pub fn para_and_to_or<A: DProp, B: DProp>(
    x: Para<And<A, B>>
) -> Or<Para<A>, Para<B>> {
    match (tauto_to_or(), tauto_to_or()) {
        (Left(tauto_a), Left(tauto_b)) => imply::absurd()(x((tauto_a(True), tauto_b(True)))),
        (Right(tauto_na), _) => Left(tauto_not_to_para(tauto_na)),
        (_, Right(tauto_nb)) => Right(tauto_not_to_para(tauto_nb)),
    }
}

/// `false^(¬a ∧ ¬b) => false^(¬a) ⋁ false^(¬b)`.
pub fn para_not_and_to_or_e<A: EProp, B: EProp>(
    x: Para<And<Not<A>, Not<B>>>
) -> Or<Para<Not<A>>, Para<Not<B>>> {
    fn f<A: EProp>(_: True) -> E<A> {A::e()}
    match (hooo_or(f), hooo_or(f)) {
        (Left(tauto_nnna), Left(tauto_nnnb)) =>
            imply::absurd()(x((not::rev_triple(tauto_nnna(True)), not::rev_triple(tauto_nnnb(True))))),
        (Right(tauto_nna), _) => Left(tauto_not_to_para(tauto_nna)),
        (_, Right(tauto_nnb)) => Right(tauto_not_to_para(tauto_nnb)),
    }
}

/// `false^(a ∧ b) => false^a ⋁ false^b`.
pub fn para_and_to_or_excm<A: Prop, B: Prop>(
    x: Para<And<A, B>>,
    excm_a: Tauto<ExcM<A>>,
    excm_b: Tauto<ExcM<B>>,
) -> Or<Para<A>, Para<B>> {
    match (tauto_excm_to_or(excm_a), tauto_excm_to_or(excm_b)) {
        (Left(tauto_a), Left(tauto_b)) => imply::absurd()(x((tauto_a(True), tauto_b(True)))),
        (Right(tauto_na), _) => Left(tauto_not_to_para(tauto_na)),
        (_, Right(tauto_nb)) => Right(tauto_not_to_para(tauto_nb)),
    }
}

/// `a^true ∧ b^true => (a ∧ b)^true`.
pub fn tauto_and<A: Prop, B: Prop>(
    tauto_a: Tauto<A>,
    tauto_b: Tauto<B>,
) -> Tauto<And<A, B>> {
    hooo_rev_and((tauto_a, tauto_b))
}

/// `(a ∧ b)^true => a^true ∧ b^true`.
pub fn tauto_rev_and<A: Prop, B: Prop>(
    tauto_and_a_b: Tauto<And<A, B>>,
) -> And<Tauto<A>, Tauto<B>> {
    hooo_and(tauto_and_a_b)
}

/// `false^a => false^(a ∧ b)`.
pub fn para_left_and<A: Prop, B: Prop>(
    para_a: Para<A>,
) -> Para<And<A, B>> {
    pow_lower(pow_lift(para_a))
}

/// `false^b => false^(a ∧ b)`.
pub fn para_right_and<A: Prop, B: Prop>(
    para_b: Para<B>,
) -> Para<And<A, B>> {
    pow_right_and_symmetry(pow_lower(pow_lift(para_b)))
}

/// `(a => b)^true ∧ (a == c)^true  =>  (c => b)^true`.
pub fn tauto_imply_in_left_arg<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Imply<A, B>>,
    eq_a_c: Tauto<Eq<A, C>>
) -> Tauto<Imply<C, B>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True)
    -> Imply<And<Imply<A, B>, Eq<A, C>>, Imply<C, B>> {
        Rc::new(move |(ab, eq_a_c)| imply::in_left_arg(ab, eq_a_c))
    }
    let f = hooo_imply(f);
    let x = hooo_rev_and((ab, eq_a_c));
    f(x)
}

/// `(a => b)^true ∧ (b == c)^true  =>  (a => c)^true`.
pub fn tauto_imply_in_right_arg<A: Prop, B: Prop, C: Prop>(
    ab: Tauto<Imply<A, B>>,
    eq_b_c: Tauto<Eq<B, C>>
) -> Tauto<Imply<A, C>> {
    fn f<A: Prop, B: Prop, C: Prop>(_: True)
    -> Imply<And<Imply<A, B>, Eq<B, C>>, Imply<A, C>> {
        Rc::new(move |(ab, eq_b_c)| imply::in_right_arg(ab, eq_b_c))
    }
    let f = hooo_imply(f);
    let x = hooo_rev_and((ab, eq_b_c));
    f(x)
}

/// `(a => b)^true ∧ a^true  =>  b^true`.
pub fn tauto_modus_ponens<A: Prop, B: Prop>(
    ab: Tauto<Imply<A, B>>,
    a: Tauto<A>,
) -> Tauto<B> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<And<Imply<A, B>, A>, B> {
        Rc::new(move |(ab, a)| ab(a))
    }
    let f = hooo_imply(f);
    let x = hooo_rev_and((ab, a));
    f(x)
}

/// `uniform(a == a)`.
pub fn uniform_refl<A: Prop>() -> Uniform<Eq<A, A>> {
    Left(eq_refl())
}

/// `uniform(a == b) => uniform(b == a)`.
pub fn uniform_symmetry<A: Prop, B: Prop>(
    f: Uniform<Eq<A, B>>
) -> Uniform<Eq<B, A>> {
    match f {
        Left(t_ab) => Left(tauto_eq_symmetry(t_ab)),
        Right(p_ab) => Right(para_eq_symmetry(p_ab)),
    }
}

/// `uniform(a == b) ∧ uniform(b == c) => uniform(a == c)`.
pub fn uniform_transitivity<A: DProp, B: DProp, C: DProp>(
    f: Uniform<Eq<A, B>>,
    g: Uniform<Eq<B, C>>
) -> Uniform<Eq<A, C>> {
    match (f, g) {
        (Left(t_ab), Left(t_bc)) => Left(tauto_eq_transitivity(t_ab, t_bc)),
        (Left(t_ab), Right(p_bc)) => Right(para_eq_transitivity_right(t_ab, p_bc)),
        (Right(p_ab), Left(t_bc)) => Right(para_eq_transitivity_left(p_ab, t_bc)),
        (Right(p_ab), Right(p_bc)) => Left(tauto_from_para_transitivity(p_ab, p_bc)),
    }
}

/// `(false^(a == b) ∧ false^(b == c)) => (a == c)^true`.
pub fn tauto_from_para_transitivity<A: DProp, B: DProp, C: DProp>(
    para_eq_ab: Para<Eq<A, B>>,
    para_eq_bc: Para<Eq<B, C>>,
) -> Tauto<Eq<A, C>> {
    match (para_decide::<A>(), para_decide::<B>(), para_decide::<C>()) {
        (Left(para_a), Left(para_b), _) => {
            imply::absurd()(para_eq_ab((
                Rc::new(move |a| imply::absurd()(para_a(a))),
                Rc::new(move |b| imply::absurd()(para_b(b)))
            )))
        }
        (_, Left(para_b), Left(para_c)) => {
            imply::absurd()(para_eq_bc((
                Rc::new(move |b| imply::absurd()(para_b(b))),
                Rc::new(move |c| imply::absurd()(para_c(c)))
            )))
        }
        (Left(para_a), _, Left(para_c)) => {
            let z: Eq<Tauto<A>, Tauto<C>> = (
                Rc::new(move |tauto_a| imply::absurd()(para_a(tauto_a(True)))),
                Rc::new(move |tauto_c| imply::absurd()(para_c(tauto_c(True))))
            );
            hooo_rev_eq(z)
        }
        (_, Right(npara_b), Right(npara_c)) => {
            let b: B = not::rev_double(not_para_to_not_not(npara_b));
            let c: C = not::rev_double(not_para_to_not_not(npara_c));
            imply::absurd()(para_eq_bc((c.map_any(), b.map_any())))
        }
        (Right(npara_a), Right(npara_b), _) => {
            let a: A = not::rev_double(not_para_to_not_not(npara_a));
            let b: B = not::rev_double(not_para_to_not_not(npara_b));
            imply::absurd()(para_eq_ab((b.map_any(), a.map_any())))
        }
        (Right(npara_a), _, Right(npara_c)) => {
            let y: Eq<Para<A>, Para<C>> = eq_not_para_to_eq_para((npara_c.map_any(), npara_a.map_any()));
            let y: Para<Not<Eq<A, C>>> = hooo_dual_rev_neq(y);
            match program::<Eq<A, C>>() {
                Left(Left(tauto_eq_ac)) => tauto_eq_ac,
                Left(Right(para_eq_ac)) => imply::absurd()(para_rev_not(y)(para_eq_ac)),
                Right(para_uni_eq_ac) => {
                    let nuni_eq_ac = Rc::new(move |x| para_uni_eq_ac(x));
                    let (x, _): And<Not<Tauto<Eq<A, C>>>, Not<Para<Eq<A, C>>>> = and::from_de_morgan(nuni_eq_ac);
                    let x: Tauto<Not<Eq<A, C>>> = hooo_rev_not(x);
                    imply::absurd()(y(x(True)))
                }
            }
        }
    }
}

/// `uniform(a) ⋀ (a == b)^true => uniform(b)`.
pub fn uniform_in_arg<A: Prop, B: Prop>(
    uni: Uniform<A>,
    eq: Tauto<Eq<A, B>>
) -> Uniform<B> {
    match uni {
        Left(tauto_a) => Left(hooo_eq(eq).0(tauto_a)),
        Right(para_a) => Right(para_in_arg(para_a, eq))
    }
}

/// `uniform(a) ∧ uniform(b) => uniform(a ∧ b)`.
pub fn uniform_and<A: Prop, B: Prop>(
    uni_a: Uniform<A>,
    uni_b: Uniform<B>
) -> Uniform<And<A, B>> {
    match (uni_a, uni_b) {
        (Left(tauto_a), Left(tauto_b)) => Left(hooo_rev_and((tauto_a, tauto_b))),
        (_, Right(para_b)) => Right(hooo_dual_rev_and(Right(para_b))),
        (Right(para_a), _) => Right(hooo_dual_rev_and(Left(para_a))),
    }
}

/// `false^uniform(a ∧ b) => false^(uniform(a) ∧ uniform(b))`.
pub fn para_uniform_and<A: Prop, B: Prop>(
    x: Para<Uniform<And<A, B>>>
) -> Para<And<Uniform<A>, Uniform<B>>> {
    fn f<A: Prop, B: Prop>((a, b): And<Uniform<A>, Uniform<B>>) -> Uniform<And<A, B>> {
        uniform_and(a, b)
    }
    pow_transitivity(f::<A, B>, x)
}

/// `uniform(a ∧ b) => uniform(a) ⋁ uniform(b)`.
pub fn uniform_dual_and<A: DProp, B: DProp>(
    uni_and: Uniform<And<A, B>>,
) -> Or<Uniform<A>, Uniform<B>> {
    match uni_and {
        Left(x) => Left(Left(hooo_and(x).0)),
        Right(para_and) => match para_and_to_or(para_and) {
            Left(para_a) => Left(Right(para_a)),
            Right(para_b) => Right(Right(para_b)),
        }
    }
}

/// `uniform(a) ∧ uniform(b) => uniform(a ⋁ b)`.
pub fn uniform_dual_rev_or<A: Prop, B: Prop>(
    a: Uniform<A>,
    b: Uniform<B>,
) -> Uniform<Or<A, B>> {
    match (a, b) {
        (Left(tauto_a), _) => Left(tauto_or_left(tauto_a)),
        (_, Left(tauto_b)) => Left(tauto_or_right(tauto_b)),
        (Right(para_a), Right(para_b)) => Right(para_to_or(para_a, para_b)),
    }
}

/// `uniform(a) => (a ⋁ ¬a)^true`.
pub fn uniform_to_tauto_excm<A: Prop>(
    uni: Uniform<A>
) -> Tauto<ExcM<A>> {
    match uni {
        Left(t) => tauto_or_left(t),
        Right(p) => tauto_or_right(para_to_tauto_not(p)),
    }
}

/// `(a ⋁ ¬a)^true => uniform(a)`.
pub fn tauto_excm_to_uniform<A: Prop>(x: Tauto<ExcM<A>>) -> Uniform<A> {
    match tauto_excm_to_or(x) {
        Left(tauto_a) => Left(tauto_a),
        Right(tauto_na) => Right(tauto_not_to_para(tauto_na)),
    }
}

/// `¬theory(a)`.
pub fn not_theory<A: DProp>() -> Not<Theory<A>> {
    fn f<A: DProp>(_: True) -> ExcM<A> {A::decide()}
    Rc::new(move |theory_a| imply::in_left(theory_a, |x| tauto_excm_to_uniform(x))(f))
}

/// `(a ⋁ ¬a)^true => ¬theory(a)`.
pub fn tauto_excm_to_not_theory<A: Prop>(x: Tauto<ExcM<A>>) -> Not<Theory<A>> {
    not::double(tauto_excm_to_uniform(x))
}

/// `theory(a) => ¬(a^true)`.
pub fn theory_to_not_tauto<A: Prop>(x: Theory<A>) -> Not<Tauto<A>> {
    imply::in_left(x, |y| Left(y))
}

/// `theory(a) => ¬(false^a)`.
pub fn theory_to_not_para<A: Prop>(x: Theory<A>) -> Not<Para<A>> {
    imply::in_left(x, |y| Right(y))
}

/// `¬(a^true) ⋀ ¬(false^a) => theory(a)`.
pub fn not_tauto_not_para_to_theory<A: Prop>(
    ntauto_a: Not<Tauto<A>>,
    npara_a: Not<Para<A>>
) -> Theory<A> {and::to_de_morgan((ntauto_a, npara_a))}

/// `(false^a)^(a^true) ⋀ (a^true)^(false^a) => false`.
///
/// This is also known as [Liar's paradox](https://en.wikipedia.org/wiki/Liar_paradox).
pub fn para_liar<A: DProp>(
    f: And<Pow<Para<A>, Tauto<A>>, Pow<Tauto<A>, Para<A>>>
) -> False {
    let f = pow_eq_to_tauto_eq(f);
    Para::<A>::nnexcm()(Rc::new(move |excm: ExcM<Para<A>>| {
        match excm {
            Left(para_a) => para_a(f(True).1(para_a)(True)),
            Right(npara_a) => {
                let ntauto_a = eq::modus_tollens(f(True)).0(npara_a.clone());
                let tauto_na = hooo_rev_not(ntauto_a);
                let para_a = tauto_not_to_para(tauto_na);
                npara_a(para_a)
            }
        }
    }))
}

/// `b^a => (a => b)`.
pub fn pow_to_imply<A: Prop, B: Prop>(pow_ba: Pow<B, A>) -> Imply<A, B> {
    Rc::new(move |a| pow_ba(a))
}

/// `b^a  =>  (a => b)^c`.
pub fn pow_to_imply_lift<A: Prop, B: Prop, C: Prop>(pow_ba: Pow<B, A>) -> Pow<Imply<A, B>, C> {
    fn f<A: Prop, B: Prop, C: Prop>(_: C) -> Imply<Tauto<Imply<A, B>>, Imply<A, B>> {
        Rc::new(move |x| x(True))
    }
    hooo_imply(f)(pow_lift(pow_to_tauto_imply(pow_ba)))
}

/// `(a => b)^true => b^a`.
pub fn tauto_imply_to_pow<A: Prop, B: Prop>(
    x: Tauto<Imply<A, B>>
) -> Pow<B, A> {
    fn f<A: Prop, B: Prop>(a: A) -> Imply<Tauto<Imply<A, B>>, B> {
        Rc::new(move |x| x(True)(a.clone()))
    }
    hooo_imply(f)(pow_lift(x))
}

/// `b^a => (a => b)^true`.
pub fn pow_to_tauto_imply<A: Prop, B: Prop>(
    x: Pow<B, A>
) -> Tauto<Imply<A, B>> {
    fn f<A: Prop, B: Prop>(_: True) -> Imply<Pow<B, A>, Imply<A, B>> {
        Rc::new(|pow_ba| Rc::new(move |a| pow_ba(a)))
    }
    let f: Imply<Pow<Pow<B, A>, True>, Tauto<Imply<A, B>>> = hooo_imply(f);
    f(pow_lift(x))
}

/// `(a => b)^true => (b^a)^true`.
pub fn tauto_pow_imply<A: Prop, B: Prop>(
    x: Tauto<Imply<A, B>>
) -> Pow<Pow<B, A>, True> {
    pow_lift(tauto_imply_to_pow(x))
}

/// `(b^a)^true => (a => b)^true`.
pub fn tauto_imply_pow<A: Prop, B: Prop>(
    x: Pow<Pow<B, A>, True>
) -> Tauto<Imply<A, B>> {
    pow_to_tauto_imply(x(True))
}

/// `(a => b)^true => b^(a^true)`.
pub fn tauto_imply_to_pow_tauto<A: Prop, B: Prop>(
    x: Tauto<Imply<A, B>>
) -> Pow<B, Tauto<A>> {
    fn f<A: Prop>(tauto_a: Tauto<A>) -> A {tauto_a(True)}
    pow_transitivity(f, tauto_imply_to_pow(x))
}

/// `b^a => b^(a^true)`.
pub fn pow_to_pow_tauto<A: Prop, B: Prop>(
    x: Pow<B, A>
) -> Pow<B, Tauto<A>> {
    tauto_imply_to_pow_tauto(pow_to_tauto_imply(x))
}

/// `(¬a)^a => (¬a)^(¬¬a)`.
pub fn pow_contra_to_pow_contra_nn<A: Prop>(x: Pow<Not<A>, A>) -> Pow<Not<A>, Not<Not<A>>> {
    tauto_imply_to_pow(pow_transitivity(pow_to_imply_lift(x), imply::modus_tollens))
}

/// `(¬a)^a => false^a`.
pub fn para_pow_contra<A: Prop>(pow_na_a: Pow<Not<A>, A>) -> Para<A> {
    pow_transitivity(hooo_rev_and((pow_na_a, not::double)), and::paradox)
}

/// `(¬a)^(¬¬a) => false^(¬¬a)`.
pub fn para_pow_contra_nn<A: Prop>(pow_na_nna: Pow<Not<A>, Not<Not<A>>>) -> Para<Not<Not<A>>> {
    pow_transitivity(hooo_rev_and((pow_na_nna, pow_refl)), and::paradox)
}

/// `((a ⋁ ¬a) == (b ⋁ ¬b))^true => ((a == b) ⋁ ¬(a == b))^true`.
pub fn tauto_eq_excm_to_tauto_excm_eq<A: Prop, B: Prop>(
    x: Tauto<Eq<ExcM<A>, ExcM<B>>>
) -> Tauto<ExcM<Eq<A, B>>> {
    let (excm_a, excm_b) = tauto_eq_to_pow_eq(x);
    let y2 = match hooo_or(excm_a) {
        Left(pow_b_excm_a) => Left(hooo_dual_or(pow_b_excm_a)),
        Right(pow_nb_excm_a) => Right(hooo_dual_or(pow_nb_excm_a)),
    };
    let y3 = match hooo_or(excm_b) {
        Left(pow_a_excm_b) => Left(hooo_dual_or(pow_a_excm_b)),
        Right(pow_na_excm_b) => Right(hooo_dual_or(pow_na_excm_b)),
    };
    match (y2, y3) {
        (Left((pow_ba, _)), Left((pow_ab, _))) =>
            tauto_or_left(pow_eq_to_tauto_eq((pow_ba, pow_ab))),
        (Left((_, pow_b_na)), Right((pow_na_b, _))) => {
            let y = pow_eq_to_tauto_eq((pow_b_na, pow_na_b));
            let y = pow_transitivity(tauto_eq_symmetry(y), eq::eq_not_to_neq);
            tauto_or_right(pow_transitivity(y, eq::neq_symmetry))
        }
        (Right((pow_nb_a, _)), Left((_, pow_a_nb))) => {
            let y = pow_eq_to_tauto_eq((pow_nb_a, pow_a_nb));
            tauto_or_right(pow_transitivity(y, eq::eq_not_to_neq))
        }
        (Right((pow_nb_a, pow_nb_na)), Right((pow_na_b, pow_na_nb))) => {
            let para_a = para_pow_contra(pow_transitivity(pow_nb_a, pow_na_nb));
            let para_b = para_pow_contra(pow_transitivity(pow_na_b, pow_nb_na));
            tauto_or_left(pow_eq_to_tauto_eq((pow_transitivity(para_a, fa()),
                                              pow_transitivity(para_b, fa()))))
        }
    }
}

/// `(a ⋁ ¬a)^(¬¬a) => a^(¬¬a)`.
pub fn pow_excm_nn_to_rev_double<A: Prop>(x: Pow<ExcM<A>, Not<Not<A>>>) -> Pow<A, Not<Not<A>>> {
    match hooo_or(x) {
        Left(x) => x,
        Right(nx) => pow_transitivity(para_pow_contra_nn(nx), fa()),
    }
}
