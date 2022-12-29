//! Tactics for Logical EQ.

#![allow(unreachable_code)]

use crate::*;

/// `(a == b) ∧ (b == c) => (a == c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>((f0, f1): Eq<A, B>, (g0, g1): Eq<B, C>) -> Eq<A, C> {
    (Rc::new(move |x| g0(f0(x))), Rc::new(move |x| f1(g1(x))))
}

/// `a => (a == ¬¬a)`.
pub fn double_neg<A: Prop>(a: A) -> Eq<A, Not<Not<A>>> {
    let double_neg = a.double_neg();
    (Rc::new(move |x| not::double(x)), Rc::new(move |x| double_neg(x)))
}

/// `(a == b) => (b == a)`.
pub fn symmetry<A: Prop, B: Prop>((f0, f1): Eq<A, B>) -> Eq<B, A> {
    (f1, f0)
}

/// `¬(a == b) => ¬(b == a)`.
pub fn neq_symmetry<A: Prop, B: Prop>(neq: Not<Eq<A, B>>) -> Not<Eq<B, A>> {
    Rc::new(move |eq| neq(symmetry(eq)))
}

/// `(a => b) = (¬a ∨ b)`.
pub fn imply_to_or_da<A: DProp, B: Prop>() -> Eq<Imply<A, B>, Or<Not<A>, B>> {
    (Rc::new(move |x| imply::to_or_da(x)), Rc::new(move |x| imply::from_or(x)))
}

/// `(a => b) = (¬a ∨ b)`.
pub fn imply_to_or_db<A: Prop, B: DProp>() -> Eq<Imply<A, B>, Or<Not<A>, B>> {
    (Rc::new(move |x| imply::to_or_db(x)), Rc::new(move |x| imply::from_or(x)))
}

/// `a == a`.
pub fn refl<A: Prop>() -> Eq<A, A> {
    (Rc::new(move |x| x), Rc::new(move |x| x))
}

/// `(a == ¬a) => false`.
pub fn anti<A: Prop>((f0, f1): Eq<A, Not<A>>) -> False {
    let na: Not<A> = Rc::new(move |a| f0(a.clone())(a));
    let a = f1(na.clone());
    na(a)
}

/// There is an `a : A` is the same as `A` being true.
///
/// With other words, a proof means it is true,
/// and if it is true then there is a proof.
pub fn true_eq<A: Prop>(a: A) -> Eq<A, True> {
    (True.map_any(), Rc::new(move |_| a.clone()))
}

/// `(a == b) => (¬b == ¬a)`
pub fn modus_tollens<A: Prop, B: Prop>((f0, f1): Eq<A, B>) -> Eq<Not<B>, Not<A>> {
    let f02 = imply::modus_tollens(f0);
    let f12 = imply::modus_tollens(f1);
    (f02, f12)
}

/// `(¬a == ¬b) => (b == a)`.
pub fn rev_modus_tollens<A: DProp, B: DProp>((f0, f1): Eq<Not<A>, Not<B>>) -> Eq<B, A> {
    let f02 = imply::rev_modus_tollens(f0);
    let f12 = imply::rev_modus_tollens(f1);
    (f02, f12)
}

/// `(¬a == ¬b) ∧ (a ∨ ¬a) ∧ (b ∨ ¬b)  =>  (b == a)`.
pub fn rev_modus_tollens_excm<A: Prop, B: Prop>(
    (f0, f1): Eq<Not<A>, Not<B>>,
    excm_a: ExcM<A>,
    excm_b: ExcM<B>,
) -> Eq<B, A> {
    let f02 = imply::rev_modus_tollens_excm(f0, excm_b.clone(), excm_a.clone());
    let f12 = imply::rev_modus_tollens_excm(f1, excm_a, excm_b);
    (f02, f12)
}

/// `(¬a == ¬b) ∧ ((a ∨ ¬a) == (b ∨ ¬b))  =>  (b == a)`.
pub fn rev_modus_tollens_eq_excm<A: Prop, B: Prop>(
    (f0, f1): Eq<Not<A>, Not<B>>,
    eq_excm_a_excm_b: Eq<ExcM<A>, ExcM<B>>,
) -> Eq<B, A> {
    let f02 = imply::rev_modus_tollens_eq_excm(f0, eq::symmetry(eq_excm_a_excm_b.clone()));
    let f12 = imply::rev_modus_tollens_eq_excm(f1, eq_excm_a_excm_b);
    (f02, f12)
}

/// `(¬a == ¬b) ∧ (a => (b ∨ ¬b)) ∧ (b => (b ∨ ¬b))  =>  (b == a)`.
pub fn rev_modus_tollens_imply_excm<A: Prop, B: Prop>(
    (f0, f1): Eq<Not<A>, Not<B>>,
    a_excm_b: Imply<A, ExcM<B>>,
    b_excm_a: Imply<B, ExcM<A>>,
) -> Eq<B, A> {
    let f02 = imply::rev_modus_tollens_imply_excm(f0, b_excm_a);
    let f12 = imply::rev_modus_tollens_imply_excm(f1, a_excm_b);
    (f02, f12)
}

/// `(true == a) => a`.
pub fn is_true<A: Prop>((f0, _): Eq<True, A>) -> A {
    f0(True)
}

/// `(false == a) => ¬a`.
pub fn is_false<A: Prop>((_, f1): Eq<False, A>) -> Not<A> {
    f1
}

/// `¬a => (a == false)`.
pub fn to_eq_false<A: Prop>(n_a: Not<A>) -> Eq<A, False> {
    (n_a, imply::absurd())
}

/// `¬(a == b) ∧ a  =>  ¬b`.
pub fn contra<A: Prop, B: DProp>(f: Not<Eq<A, B>>, a: A) -> Not<B> {
    contra_excm(f, a, B::decide())
}

/// `¬(a == b) ∧ a  =>  ¬b`.
pub fn contra_excm<A: Prop, B: Prop>(
    f: Not<Eq<A, B>>,
    a: A,
    excm_b: ExcM<B>
) -> Not<B> {
    match excm_b {
        Left(b) => not::absurd(f, and::to_eq_pos((a, b))),
        Right(not_b) => not_b,
    }
}

/// `(a == b) == c  =>  a => (b == c)`
pub fn assoc_right<A: DProp, B: DProp, C: DProp>((f0, f1): Eq<Eq<A, B>, C>) -> Imply<A, Eq<B, C>> {
    match (A::decide(), C::decide()) {
        (Right(not_a), _) => Rc::new(move |x| match not_a.clone()(x) {}),
        (_, Left(c)) =>
            Rc::new(move |x| (c.clone().map_any(), f1.clone()(c.clone()).0(x).map_any())),
        (Left(a), Right(not_c)) => {
            // `!(a = b)`
            let g = imply::rev_modus_ponens(f0, not_c.clone());
            let not_b = eq::contra(g, a);
            and::to_eq_neg((not_b, not_c)).map_any()
        }
    }
}

/// `(a == b) == c  =>  (b == c) => a`.
pub fn assoc_left<A: DProp, B: DProp, C: DProp>((f0, f1): Eq<Eq<A, B>, C>) -> Imply<Eq<B, C>, A> {
    match (A::decide(), B::decide(), C::decide()) {
        (Left(a), _, _) => a.map_any(),
        (Right(not_a), Right(not_b), Right(not_c)) =>
            match not_c(f0(and::to_eq_neg((not_a, not_b)))) {},
        (_, Left(b), Right(not_c)) =>
            Rc::new(move |(fb, _)| match not_c.clone()(fb(b.clone())) {}),
        (_, Right(not_b), Left(c)) =>
            Rc::new(move |(_, fc)| match not_b.clone()(fc(c.clone())) {}),
        (Right(not_a), Left(b), Left(c)) => {
            // `a = b`.
            let (_, g1) = f1(c);
            let a = g1(b);
            match not_a(a) {}
        }
    }
}

/// `(a == b) == c  =>  a == (b == c)`.
pub fn assoc<A: DProp, B: DProp, C: DProp>(f: Eq<Eq<A, B>, C>) -> Eq<A, Eq<B, C>> {
    (assoc_right(f.clone()), assoc_left(f))
}

/// `a == (b == c)  =>  a == (c == b)`.
pub fn swap_right<A: Prop, B: Prop, C: Prop>((f0, f1): Eq<A, Eq<B, C>>) -> Eq<A, Eq<C, B>> {
    (Rc::new(move |x| {let (g0, g1) = f0(x); (g1, g0)}),
     Rc::new(move |(g1, g0)| f1((g0, g1))))
}

/// `(a == b) == c  =>  (b == a) == c`.
pub fn swap_left<A: Prop, B: Prop, C: Prop>(f: Eq<Eq<A, B>, C>) -> Eq<Eq<B, A>, C> {
    symmetry(swap_right(symmetry(f)))
}

/// `(a == b) ∧ (a == c)  =>  (c == b)`
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>(f: Eq<A, B>, g: Eq<A, C>) -> Eq<C, B> {
    symmetry(transitivity(symmetry(f), g))
}

/// See transitivity.
pub fn in_right_arg<A: Prop, B: Prop, C: Prop>(f: Eq<A, B>, g: Eq<B, C>) -> Eq<A, C> {
    transitivity(f, g)
}

/// Makes it easier to traverse.
pub fn in_left<A: Prop, B: Prop, C: Prop, F, G>(
    eq_ab: Eq<A, B>,
    f: F,
    g: G,
) -> Eq<C, B>
    where F: Fn(A) -> C + 'static,
          G: Fn(C) -> A + 'static
{
    in_left_arg(eq_ab, (Rc::new(move |a| f(a)), Rc::new(move |c| g(c))))
}

/// Makes it easier to traverse.
pub fn in_right<A: Prop, B: Prop, C: Prop, F, G>(
    eq_ab: Eq<A, B>,
    f: F,
    g: G,
) -> Eq<A, C>
    where F: Fn(B) -> C + 'static,
          G: Fn(C) -> B + 'static
{
    eq::symmetry(in_left(eq::symmetry(eq_ab), f, g))
}

/// `(a == b) == (b == a)`.
pub fn symmetry_eq<A: Prop, B: Prop>() -> Eq<Eq<A, B>, Eq<B, A>> {
    (Rc::new(move |x| eq::symmetry(x)),
     Rc::new(move |x| eq::symmetry(x)))
}

/// `((a == b) == c)  ==  (a == (b == c))`.
pub fn assoc_eq<A: DProp, B: DProp, C: DProp>() -> Eq<Eq<Eq<A, B>, C>, Eq<A, Eq<B, C>>> {
    (Rc::new(move |x| eq::assoc(x)), Rc::new(move |x| {
        let x2 = eq::symmetry(x);
        let x3 = eq::in_left_arg(x2, symmetry_eq());
        let x4 = eq::assoc(x3);
        let x5 = eq::symmetry(x4);
        eq::in_left_arg(x5, symmetry_eq())
    }))
}

/// `(a == b) == (c == d)  =>  (a == c) == (b == d)`.
pub fn transpose<A: DProp, B: DProp, C: DProp, D: DProp>(
    f: Eq<Eq<A, B>, Eq<C, D>>
) -> Eq<Eq<A, C>, Eq<B, D>> {
    let f = eq::in_left_arg(f, eq::symmetry_eq());
    let f = eq::in_right_arg(f, eq::symmetry_eq());
    let f = eq::assoc(f);
    let f = eq::in_right_arg(f, eq::symmetry_eq());
    let f = eq::in_right_arg(f, eq::assoc_eq());
    let f = eq::symmetry(f);
    let f = eq::assoc(f);
    let f = eq::symmetry(f);
    let f = eq::assoc(f);
    eq::in_left_arg(f, eq::symmetry_eq())
}

/// `(a == b) = (c == b)  =>  (a == c)`.
pub fn triangle<A: DProp, B: DProp, C: DProp>(f: Eq<Eq<A, B>, Eq<C, B>>) -> Eq<A, C> {
    let f = eq::transpose(f);
    f.1(eq::refl())
}

/// `¬(a == b) = ¬(c == b)  =>  (a == c)`.
pub fn inv_triangle<A: DProp, B: DProp, C: DProp>(
    f: Eq<Not<Eq<A, B>>, Not<Eq<C, B>>>
) -> Eq<A, C> {
    let f = eq::rev_modus_tollens(f);
    let f = eq::symmetry(f);
    eq::triangle(f)
}

/// `false == false`.
pub fn absurd() -> Eq<False, False> {
    (imply::absurd(), imply::absurd())
}

/// `(a == b) ⋀ ¬(a == c) => ¬(b == c)`.
pub fn neq_left<A: Prop, B: Prop, C: Prop>(
    eq_ab: Eq<A, B>,
    neq_ac: Not<Eq<A, C>>
) -> Not<Eq<B, C>> {
    Rc::new(move |eq_bc| neq_ac(transitivity(eq_ab.clone(), eq_bc)))
}

/// `(a == b) ⋀ ¬(b == c) => ¬(a == c)`.
pub fn neq_right<A: Prop, B: Prop, C: Prop>(
    eq_ab: Eq<A, B>,
    neq_bc: Not<Eq<B, C>>
) -> Not<Eq<A, C>> {
    Rc::new(move |eq_ac| neq_bc(transitivity(symmetry(eq_ab.clone()), eq_ac)))
}

/// `¬(a == b)  =>  ¬(a ⋀ b)`.
pub fn neq_to_nand<A: Prop, B: Prop>(neq: Not<Eq<A, B>>) -> Not<And<A, B>> {
    Rc::new(move |(a, b)| neq((b.map_any(), a.map_any())))
}

/// `¬(a == b)  =>  (a == ¬b)`.
pub fn neq_to_eq_not<A: DProp, B: DProp>(x: Not<Eq<A, B>>) -> Eq<A, Not<B>> {
    let x2 = x.clone();
    (Rc::new(move |a| {
        let x = x2.clone();
        Rc::new(move |b| x.clone()((b.map_any(), a.clone().map_any())))
     }),
     Rc::new(move |nb| match A::decide() {
         Left(a) => a,
         Right(na) => not::absurd(x.clone(), eq::rev_modus_tollens((na.map_any(), nb.map_any()))),
     }))
}

/// `(a == ¬b) => ¬(a == b)`.
pub fn eq_not_to_neq<A: Prop, B: Prop>(f: Eq<A, Not<B>>) -> Not<Eq<A, B>> {
    Rc::new(move |eq_ab| anti(in_left_arg(f.clone(), eq_ab)))
}

/// `(a == b) => ((a ⋁ ¬a) == (b ⋁ ¬b))`.
pub fn eq_to_eq_excm<A: Prop, B: Prop>(x: Eq<A, B>) -> Eq<ExcM<A>, ExcM<B>> {
    let x2 = x.clone();
    (
        Rc::new(move |excm_a| {
            let x = x2.clone();
            match excm_a {
                Left(a) => Left(x.0(a)),
                Right(na) => Right(eq::modus_tollens(x).1(na)),
            }
        }),
        Rc::new(move |excm_b| {
            let x = x.clone();
            match excm_b {
                Left(b) => Left(x.1(b)),
                Right(nb) => Right(eq::modus_tollens(x).0(nb)),
            }
        })
    )
}
