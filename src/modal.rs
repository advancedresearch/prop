//! # Modal Logic
//!
//! This modal logic builds upon the `hooo` module using Exponential Propositions.

use crate::*;
use hooo::*;

/// `◇a`.
type Pos<A> = Para<Para<A>>;
/// `□a`.
type Nec<A> = Not<Pos<Not<A>>>;

/// `¬◇a => false^a`.
pub fn npos_to_para<A: DProp>(npos: Not<Pos<A>>) -> Para<A> {
    match Para::<A>::decide() {
        Left(para_a) => para_a,
        Right(npara_a) => imply::absurd()(pow_not(npos)(npara_a)),
    }
}

/// `false^a => ¬◇a`.
pub fn para_to_npos<A: Prop>(para_a: Para<A>) -> Not<Pos<A>> {
    Rc::new(move |pos_a| pos_a(para_a))
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
                    let x = pow_not(npos_a);
                    let x = para_in_arg(x, f);
                    let x = pow_rev_not(x);
                    imply::absurd()(nnec_na(x))
                }
            }
        }),
        Rc::new(move |x| not::double(para_in_arg(x, g))),
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
        Rc::new(move |nnec_a: Not<Not<Para<Para<Not<A>>>>>| {
            let x = imply::in_left(nnec_a, |y| pow_rev_not(y));
            let x = pow_not(x);
            para_in_arg(x, g)
        }),
        Rc::new(move |pos_na| {
            let x: Para<Not<Not<Para<Not<A>>>>> = para_in_arg(pos_na, tauto_eq_symmetry(g));
            let x = pow_rev_not(x);
            imply::in_left(x, |y| pow_not(y))
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
            let x = pow_not(x);
            let x = para_in_arg(x, f);
            pow_rev_not(x)
        }),
        Rc::new(move |x| {
            let x = pow_not(x);
            let x = para_in_arg(x, tauto_eq_symmetry(f));
            pow_rev_not(x)
        })
    )
}
