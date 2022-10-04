//! # Modal Logic
//!
//! This modal logic builds upon the `hooo` module using Exponential Propositions.

use crate::*;
use hooo::*;

/// `◇a`.
#[derive(Clone)]
pub struct Pos<A>(Para<Para<A>>);
/// `□a`.
pub type Nec<A> = Not<Pos<Not<A>>>;

impl<A: Prop> Decidable for Pos<A> {
    fn decide() -> ExcM<Pos<A>> {
        match Para::<Para<A>>::decide() {
            Left(x) => Left(Pos(x)),
            Right(y) => Right(imply::in_left(y, |x| unsafe {pos_to_para_para(x)})),
        }
    }
}

/// `□a => a^true`.
pub fn nec_to_tauto<A: DProp>(nec_a: Nec<A>) -> Tauto<A> {
    match Tauto::<A>::decide() {
        Left(tauto_a) => tauto_a,
        Right(ntauto_a) => {
            let para_a = tauto_not_to_para(hooo_rev_not()(ntauto_a));
            let x: Para<Not<A>> = npos_to_para(nec_a);
            imply::absurd()(pow_rev_not(x)(para_a))
        }
    }
}

/// `a^true => □a`.
pub unsafe fn tauto_to_nec<A: Prop>(tauto_a: Tauto<A>) -> Nec<A> {
    Rc::new(move |pos_na| {
        match Para::<Not<A>>::decide() {
            Left(para_na) => pos_to_para_para(pos_na)(para_na),
            Right(npara_na) => {
                let para_a = para_not_rev_double(pow_not(npara_na));
                para_a(tauto_a(True))
            }
        }
    })
}

/// `¬◇a => false^a`.
pub fn npos_to_para<A: Prop>(npos: Not<Pos<A>>) -> Para<A> {
    match Para::<A>::decide() {
        Left(para_a) => para_a,
        Right(npara_a) => imply::absurd()(pos_not(npos)(npara_a)),
    }
}

/// `false^a => ¬◇a`.
pub unsafe fn para_to_npos<A: Prop>(para_a: Para<A>) -> Not<Pos<A>> {
    Rc::new(move |pos_a| pos_to_para_para(pos_a)(para_a))
}

/// `¬□¬a <=> ◇a`.
pub fn eq_nnecn_pos<A: Prop>() -> Eq<Not<Nec<Not<A>>>, Pos<A>> {
    fn f<A: Prop>(_: True) -> Eq<Not<Para<A>>, Not<Para<Not<Not<A>>>>> {
        (
            Rc::new(move |x| pow_rev_not(para_not_triple(pow_not(x)))),
            Rc::new(move |x| pow_rev_not(para_not_rev_triple(pow_not(x))))
        )
    }
    fn g<A: Prop>(_: True) -> Eq<Para<A>, Para<Not<Not<A>>>> {
        (Rc::new(move |x| para_not_double(x)), Rc::new(move |x| para_not_rev_double(x)))
    }
    (
        Rc::new(move |nnec_na| {
            match Pos::<A>::decide() {
                Left(pos_a) => pos_a,
                Right(npos_a) => {
                    let x = pos_not(npos_a);
                    let x = para_in_arg(x, f);
                    let x = pow_rev_not(x);
                    let x = imply::in_left(x, |y| unsafe {pos_to_para_para(y)});
                    imply::absurd()(nnec_na(x))
                }
            }
        }),
        Rc::new(move |x| {
            let x = unsafe {pos_to_para_para(x)};
            not::double(Pos(para_in_arg(x, g)))
        })
    )
}

/// `¬◇¬a <=> □a`.
pub fn eq_nposn_nec<A: Prop>() -> Eq<Not<Pos<Not<A>>>, Nec<A>> {
    eq::refl()
}

/// `¬□a == ◇¬a`.
pub fn eq_nnec_posn<A: Prop>() -> Eq<Not<Nec<A>>, Pos<Not<A>>> {
    fn g<A: Prop>(_: True) -> Eq<Not<Not<Para<Not<A>>>>, Para<Not<A>>> {
        fn f<A: Prop>(_: True) -> Eq<Not<Not<Not<A>>>, Not<A>> {
            (Rc::new(move |x| not::rev_triple(x)), Rc::new(move |x| not::double(x)))
        }
        (
            Rc::new(move |x| {
                let x = imply::in_left(x, |y| pow_rev_not(y));
                para_in_arg(pow_not(x), f)
            }),
            Rc::new(move |x| {
                let x = para_in_arg(x, tauto_eq_symmetry(f));
                let x: Not<Para<Not<Not<A>>>> = pow_rev_not(x);
                imply::in_left(x, |y| pow_not(y))
            })
        )
    }
    (
        Rc::new(move |nnec_a: Not<Not<Pos<Not<A>>>>| {
            let x = nnpos_to_nnpara_para(nnec_a);
            let x = imply::in_left(x, |y| pow_rev_not(y));
            let x = pow_not(x);
            Pos(para_in_arg(x, g))
        }),
        Rc::new(move |pos_na| {
            let x = unsafe {pos_to_para_para(pos_na)};
            let x: Para<Not<Not<Para<Not<A>>>>> = para_in_arg(x, tauto_eq_symmetry(g));
            let x = pow_rev_not(x);
            let x: Not<Not<Para<Para<Not<A>>>>> = imply::in_left(x, |y| pow_not(y));
            imply::in_left(x, |y| imply::in_left(y, |x| Pos(x)))
        })
    )
}

/// `¬◇a == □¬a`.
pub fn eq_posn_nnec<A: Prop>() -> Eq<Not<Pos<A>>, Nec<Not<A>>> {
    fn f<A: Prop>(_: True) -> Eq<Not<Para<A>>, Not<Para<Not<Not<A>>>>> {
        fn g<A: Prop>(_: True) -> Eq<Not<Not<Not<A>>>, Not<A>> {
            (Rc::new(move |x| not::rev_triple(x)), Rc::new(move |x| not::double(x)))
        }
        (
            Rc::new(move |x| {
                let x = pow_not(x);
                let x = para_in_arg(x, tauto_eq_symmetry(g));
                pow_rev_not(x)
            }),
            Rc::new(move |x| {
                let x = pow_not(x);
                let x = para_in_arg(x, g);
                pow_rev_not(x)
            })
        )
    }
    (
        Rc::new(move |x| {
            let x = pos_not(x);
            let x = para_in_arg(x, f);
            imply::in_left(pow_rev_not(x), |y| unsafe {pos_to_para_para(y)})
        }),
        Rc::new(move |x| {
            let x = pos_not(x);
            let x = para_in_arg(x, tauto_eq_symmetry(f));
            imply::in_left(pow_rev_not(x), |y| unsafe {pos_to_para_para(y)})
        })
    )
}

/// `◇a => (false^(false^a))`.
pub unsafe fn pos_to_para_para<A: Prop>(Pos(x): Pos<A>) -> Para<Para<A>> {x}

/// `¬¬◇a => ¬¬(false^(false^a))`.
pub fn nnpos_to_nnpara_para<A: Prop>(x: Not<Not<Pos<A>>>) -> Not<Not<Para<Para<A>>>> {
    imply::in_left(x, |y| imply::in_left(y, |x| unsafe {pos_to_para_para(x)}))
}

/// `(false^(false^a) => ◇a)^true) => (false^(false^a) == ◇a)^true)`.
pub fn to_pos_tauto_eq<A: Prop>(
    y: Tauto<Imply<Para<Para<A>>, Pos<A>>>
) -> Tauto<Eq<Para<Para<A>>, Pos<A>>> {
    fn f<A: Prop>(_: True) -> Imply<Pos<A>, Para<Para<A>>> {
        Rc::new(move |pos_a| unsafe {pos_to_para_para(pos_a)})
    }
    hooo_rev_and()((y, f::<A>))
}

/// `¬◇a => false^(¬(false^a))`.
pub fn pos_not<A: Prop>(x: Not<Pos<A>>) -> Para<Not<Para<A>>> {
    pow_not(imply::in_left(x, |y| Pos(y)))
}
