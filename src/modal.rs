//! # Modal Logic
//!
//! This modal logic builds upon the `hooo` module using Exponential Propositions.
//!
//! The Modal Logic variant derived is S5 or stronger.
//! For more information about variants of Modal Logic, see [wikipedia article](https://en.wikipedia.org/wiki/Modal_logic).
//!
//! It is currently known that HOOO Exponential Propositions implies S5,
//! but it is unknown whether S5 implies HOOO Exponential Propositions.

use crate::*;
use hooo::*;

/// A proposition is possibly true if it is either a tautology or a theory.
pub type Pos<A> = Or<Tauto<A>, Theory<A>>;

/// A proposition is necessarily true if it is a tautology.
pub type Nec<A> = Tauto<A>;

/// `□¬□⊥`.
pub fn nec_consistency() -> Nec<Not<Nec<False>>> {
    fn f(_: True) -> Not<Nec<False>> {hooo::consistency()}
    f
}

/// `⊥^(¬□⊥ => ¬□¬□⊥)`.
pub fn para_godel(x: Imply<Not<Nec<False>>, Not<Nec<Not<Nec<False>>>>>) -> False {
    x(nec_consistency()(True))(nec_consistency())
}

/// `□¬(¬□⊥ => ¬□¬□⊥)`.
pub fn nec_not_godel() -> Nec<Not<Imply<Not<Nec<False>>, Not<Nec<Not<Nec<False>>>>>>> {
    hooo::para_to_tauto_not(para_godel)
}

/// `¬(false^a) => ◇a`.
pub fn npara_to_pos<A: DProp>(npara: Not<Para<A>>) -> Pos<A> {
    match program::<A>() {
        Left(Left(tauto_a)) => Left(tauto_a),
        Left(Right(para_a)) => not::absurd(npara, para_a),
        Right(para_uni_a) => Right(Rc::new(move |x| para_uni_a(x))),
    }
}

/// `◇a => ¬(false^a)`.
pub fn pos_to_npara<A: Prop>(pos: Pos<A>) -> Not<Para<A>> {
    Rc::new(move |para_a| {
        match pos.clone() {
            Left(tauto_a) => para_a(tauto_a(True)),
            Right(theory_a) => theory_a(Right(para_a)),
        }
    })
}

/// `false^(false^a) => ◇a`.
pub fn para_para_to_pos<A: DProp>(para_para_a: Para<Para<A>>) -> Pos<A> {
    npara_to_pos(hooo::para_para_to_not_para(para_para_a))
}

/// `◇a => false^(false^a)`.
pub fn pos_to_para_para<A: DProp>(pos: Pos<A>) -> Para<Para<A>> {
    hooo::not_para_to_para_para(pos_to_npara(pos))
}

/// `¬◇a => false^a`.
pub fn npos_to_para<A: DProp>(npos: Not<Pos<A>>) -> Para<A> {
    match para_decide::<A>() {
        Left(para_a) => para_a,
        Right(npara_a) => not::absurd(npos, npara_to_pos(npara_a)),
    }
}

/// `false^a => ¬◇a`.
pub fn para_to_npos<A: Prop>(para_a: Para<A>) -> Not<Pos<A>> {
    Rc::new(move |pos| match pos {
        Left(tauto_a) => para_a(tauto_a(True)),
        Right(theory_a) => theory_a(Right(para_a))
    })
}

/// `¬◇a => ◇¬a`.
pub fn npos_to_posn<A: DProp>(npos_a: Not<Pos<A>>) -> Pos<Not<A>> {
    let para_a = npos_to_para(npos_a);
    Left(para_to_tauto_not(para_a))
}

/// `◇¬a => ¬◇a`.
pub fn posn_to_npos<A: DProp>(pos_na: Pos<Not<A>>) -> Not<Pos<A>> {
    Rc::new(move |pos_a| {
        match (pos_a, pos_na.clone()) {
            (Left(tauto_a), Left(tauto_na)) => tauto_not_to_para(tauto_na)(tauto_a(True)),
            (Left(tauto_a), Right(theory_na)) => theory_na(Right(tauto_to_para_not(tauto_a))),
            (Right(theory_a), Left(tauto_na)) => theory_a(Right(tauto_not_to_para(tauto_na))),
            (Right(theory_a), Right(theory_na)) => {
                let (ntauto_a, _) = and::from_de_morgan(theory_a);
                theory_na(Left(hooo_rev_not(ntauto_a)))
            }
        }
    })
}

/// `□a => ¬◇¬a`.
pub fn nec_to_nposn<A: DProp>(tauto_a: Nec<A>) -> Not<Pos<Not<A>>> {
    Rc::new(move |pos_na| posn_to_npos(pos_na)(Left(tauto_a)))
}

/// `¬◇¬a => □a`.
pub fn nposn_to_nec<A: DProp>(npos_na: Not<Pos<Not<A>>>) -> Nec<A> {
    match program::<A>() {
        Left(Left(tauto_a)) => tauto_a,
        Left(Right(para_a)) => not::absurd(npos_na, npos_to_posn(para_to_npos(para_a))),
        Right(para_uni_a) => {
            let x: Not<Uniform<A>> = Rc::new(move |x| para_uni_a(x));
            let (ntauto_a, _) = and::from_de_morgan(x);
            not::absurd(npos_na, Left(hooo_rev_not(ntauto_a)))
        }
    }
}

/// `◇a => ¬□¬a`.
pub fn pos_to_nnecn<A: Prop>(pos_a: Pos<A>) -> Not<Nec<Not<A>>> {
    Rc::new(move |tauto_na| match pos_a.clone() {
        Left(tauto_a) => tauto_na(True)(tauto_a(True)),
        Right(theory_a) => theory_a(Right(tauto_not_to_para(tauto_na))),
    })
}

/// `¬□¬a => ◇a`.
pub fn nnecn_to_pos<A: DProp>(ntauto_na: Not<Nec<Not<A>>>) -> Pos<A> {
    match program::<A>() {
        Left(Left(tauto_a)) => Left(tauto_a),
        Left(Right(para_a)) => {
            not::absurd(imply::in_left(ntauto_na, |x| para_to_tauto_not(x)), para_a)
        }
        Right(para_uni_a) => {
            let x: Not<Uniform<A>> = Rc::new(move |x| para_uni_a(x));
            let (ntauto_a, _) = and::from_de_morgan(x);
            not::absurd(ntauto_na, hooo_rev_not(ntauto_a))
        }
    }
}

/// `(|- a) => (|- □a)`.
///
/// This is added as an axiom since Rust can't prove `fn(()) -> A` is the same as `fn() -> A`.
pub fn n<A: Prop>(_: fn() -> A) -> fn() -> Nec<A> {
    unimplemented!()
}

/// `□(a => b) => (□a => □b)`.
pub fn k<A: Prop, B: Prop>(x: Nec<Imply<A, B>>) -> Imply<Nec<A>, Nec<B>> {
    hooo_imply(x)
}

/// `□a => a`.
pub fn t<A: Prop>(x: Nec<A>) -> A {x(True)}

/// `a => □◇a`.
pub fn b<A: DProp>(a: A) -> Nec<Pos<A>> {
    match program::<Pos<A>>() {
        Left(Left(tauto_pos_a)) => tauto_pos_a,
        Left(Right(para_pos_a)) => {
            let x: Not<Pos<A>> = Rc::new(move |x| para_pos_a(x));
            imply::absurd()(npos_to_para(x)(a))
        }
        Right(para_uni_pos_a) => {
            let x: Not<Uniform<Pos<A>>> = Rc::new(move |x| para_uni_pos_a(x));
            let (ntauto_pos_a, _) = and::from_de_morgan(x);
            let x: Not<Pos<A>> = hooo_rev_not(ntauto_pos_a)(True);
            match npos_to_posn(x.clone()) {
                Left(tauto_na) => not::absurd(tauto_na(True), a),
                Right(theory_na) => {
                    let (y, _) = and::from_de_morgan(theory_na);
                    let y: Not<Para<A>> = imply::in_left(y, |x| para_to_tauto_not(x));
                    not::absurd(x, npara_to_pos(y))
                }
            }
        }
    }
}

/// `□a => □□a`.
pub fn four<A: Prop>(nec_a: Nec<A>) -> Nec<Nec<A>> {pow_lift(nec_a)}

/// `◇a => □◇a`.
pub fn five<A: DProp>(pos_a: Pos<A>) -> Nec<Pos<A>> {
    match program::<Pos<A>>() {
        Left(Left(tauto_pos_a)) => tauto_pos_a,
        Left(Right(para_pos_a)) => imply::absurd()(para_pos_a(pos_a)),
        Right(para_uni_pos_a) => {
            let x: Not<Uniform<Pos<A>>> = Rc::new(move |x| para_uni_pos_a(x));
            let (ntauto_pos_a, _) = and::from_de_morgan(x);
            not::absurd(hooo_rev_not(ntauto_pos_a)(True), pos_a)
        }
    }
}
