//! # Modal Logic
//!
//! This modal logic builds upon the `hooo` module using Exponential Propositions.

use crate::*;
use hooo::*;

/// `□a`.
type Nec<A> = Tauto<A>;
/// `◇a`.
type Pos<A> = Para<Para<A>>;

/// `¬◇a => false^a`.
pub fn npos_to_para<A: DProp>(npos: Not<Pos<A>>) -> Para<A> {
    match Para::<A>::decide() {
        Left(para_a) => para_a,
        Right(npara_a) => imply::absurd()(pow_not(npos)(npara_a)),
    }
}

/// `¬□¬a <=> ◇a`.
pub fn eq_nnecn_pos<A: Prop>() -> Eq<Not<Nec<Not<A>>>, Pos<A>> {
    (
        Rc::new(move |n_nec_na| {
            fn f<A: Prop>(para_a: Para<A>) -> Not<A> {
                Rc::new(move |a| para_a(a))
            }
            let x: Pow<Not<Not<A>>, True> = hooo_rev_not()(n_nec_na);
            let x: Pow<Para<Not<A>>, True> = pow_imply(x);
            let x: Para<Not<A>> = x(True);
            pow_transitivity(f, x)
        }),
        Rc::new(move |pos_a| {
            Rc::new(move |nec_na| {
                let x = pow_imply(nec_na);
                pos_a(x(True))
            })
        }),
    )
}

/// `□p => ¬◇¬p`.
pub fn nec_to_nposn<A: Prop>(nec_a: Nec<A>) -> Not<Pos<Not<A>>> {
    Rc::new(move |pos_na| {
        let x = Rc::new(move |x| pos_na(x));
        pow_not(x)(not::double(nec_a(True)))
    })
}

/// `¬◇¬a <=> □a`.
pub fn eq_nposn_nec<A: DProp>() -> Eq<Not<Pos<Not<A>>>, Nec<A>> {
    (
        Rc::new(move |n_pos_na| {
            fn f<A: Prop>(_: True) -> Eq<Not<Para<Not<A>>>, Not<Not<Para<A>>>> {
                (
                    Rc::new(move |x: Not<Para<Not<A>>>| {
                        imply::in_left(x, |y| pow_not(y))
                    }),
                    Rc::new(move |y: Not<Not<Para<A>>>| {
                        imply::in_left(y, |x| pow_rev_not(x))
                    })
                )
            }
            match Tauto::<A>::decide() {
                Left(tauto_a) => tauto_a,
                Right(ntauto_a) => {
                    let x = pow_not(n_pos_na);
                    let x: Para<Not<Not<Para<A>>>> = para_in_arg(x, f::<A>);
                    let y: Tauto<Para<A>> = pow_imply(hooo_rev_not()(ntauto_a));
                    imply::absurd()(x(not::double(y(True))))
                }
            }
        }),
        Rc::new(move |nec_a| nec_to_nposn(nec_a)),
    )
}

/// `¬□a == □¬a`.
pub fn listing_mobius<A: Prop>() -> Eq<Not<Nec<A>>, Nec<Not<A>>> {
    (
        Rc::new(move |nnec_a| hooo_rev_not()(nnec_a)),
        Rc::new(move |nec_na| hooo_not()(nec_na)),
    )
}
