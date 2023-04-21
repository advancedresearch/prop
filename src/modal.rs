//! # Modal Logic
//!
//! This modal logic builds upon the [hooo] module using Exponential Propositions (HOOO EP).
//!
//! The Modal Logic variant derived is S5 or stronger for decidable propositions.
//! For more information about variants of Modal Logic, see [wikipedia article](https://en.wikipedia.org/wiki/Modal_logic).
//!
//! It is currently known that HOOO EP implies S5,
//! but it is unknown whether S5 implies HOOO EP.

use crate::*;
use hooo::*;

/// `◇p := p^true ⋁ theory(p)`.
///
/// A proposition is possibly true if it is either a tautology or a theory.
pub type Pos<A> = Or<Tauto<A>, Theory<A>>;

/// `□p := p^true`.
///
/// A proposition is necessarily true if it is a tautology.
pub type Nec<A> = Tauto<A>;

/// `□¬□⊥`.
pub fn nec_consistency() -> Nec<Not<Nec<False>>> {
    fn f(_: True) -> Not<Nec<False>> {hooo::consistency()}
    f
}

/// `□(□p => p)`.
///
/// Shows that the premise of [Löb's theorem](https://en.wikipedia.org/wiki/L%C3%B6b%27s_theorem)
/// is trivial in this model.
///
/// This means Löb's theorem is absurd. See [hooo_traits::Lob].
pub fn lob_triv<P: Prop>() -> Nec<Imply<Nec<P>, P>> {
    pow_to_tauto_imply(pow_to_pow_tauto(pow_refl))
}

/// `⊥^(□(□⊥ => ⊥) => □⊥)`.
pub fn para_lob(x: Imply<Nec<Imply<Nec<False>, False>>, Nec<False>>) -> False {x(lob_triv())(True)}

/// `□¬(□(□⊥ => ⊥) => □⊥)`.
pub fn nec_not_lob() -> Nec<Not<Imply<Nec<Imply<Nec<False>, False>>, Nec<False>>>> {
    hooo::para_to_tauto_not(para_lob)
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
    match uniform::<A>() {
        Left(tauto_a) => Left(tauto_a),
        Right(para_a) => not::absurd(npara, para_a),
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
    match uniform::<A>() {
        Left(tauto_a) => tauto_a,
        Right(para_a) => not::absurd(npos_na, npos_to_posn(para_to_npos(para_a))),
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
    match uniform::<A>() {
        Left(tauto_a) => Left(tauto_a),
        Right(para_a) => {
            not::absurd(imply::in_left(ntauto_na, |x| para_to_tauto_not(x)), para_a)
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
    match uniform::<Pos<A>>() {
        Left(tauto_pos_a) => tauto_pos_a,
        Right(para_pos_a) => {
            let x: Not<Pos<A>> = Rc::new(para_pos_a);
            imply::absurd()(npos_to_para(x)(a))
        }
    }
}

/// `□a => □□a`.
pub fn four<A: Prop>(nec_a: Nec<A>) -> Nec<Nec<A>> {pow_lift(nec_a)}

/// `◇a => □◇a`.
pub fn five<A: DProp>(pos_a: Pos<A>) -> Nec<Pos<A>> {
    match uniform::<Pos<A>>() {
        Left(tauto_pos_a) => tauto_pos_a,
        Right(para_pos_a) => imply::absurd()(para_pos_a(pos_a)),
    }
}

/// `◇a => ∃ true { a }`.
pub fn pos_to_exists_true<A: Prop>(x: Pos<A>) -> Exists<True, A> {
    Rc::new(move |tauto_na| {
        match x.clone() {
            Left(tauto_a) => not::absurd(tauto_na(True), tauto_a(True)),
            Right(theory_a) => not::absurd(theory_a, Right(tauto_not_to_para(tauto_na))),
        }
    })
}

/// `¬¬◇a => ∃ true { a }`.
pub fn not_not_pos_to_exists_true<A: Prop>(x: Not<Not<Pos<A>>>) -> Exists<True, A> {
    not::rev_triple(imply::modus_tollens(imply::modus_tollens(Rc::new(pos_to_exists_true)))(x))
}

/// `∃ true { a } => ¬¬◇a`.
pub fn exists_true_to_not_not_pos<A: Prop>(x: Exists<True, A>) -> Not<Not<Pos<A>>> {
    Rc::new(move |npos_a| {
        let y = and::from_de_morgan(npos_a);
        y.1(and::to_de_morgan((y.0, hooo::exists_to_not_para(x.clone()))))
    })
}

/// `a  =>  ¬¬◇a`.
pub fn to_not_not_pos<A: Prop>(a: A) -> Not<Not<Pos<A>>> {
    Rc::new(move |npos_a| {
        let x = and::from_de_morgan(npos_a);
        imply::in_left(x.1, and::to_de_morgan)((x.0,
            hooo::exists_to_not_para(hooo::exists_true(a.clone()))))
    })
}
