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
/// A proposition is theoretical possibly true if it is either a tautology or a theory.
///
/// This is a stronger notion of possibly true than in most modal logics.
/// For a corresponding weaker notion of possibly true, see [NNPos].
pub type Pos<A> = Or<Tauto<A>, Theory<A>>;

/// `¬¬◇p`.
///
/// A proposition is existential possibly true if it is not not theoretical possibly true.
/// This is also the same as not necessary not true `¬□¬p` or `∃ true { p }` (using [hooo::Exists]).
///
/// This corresponds to possibly true in most modal logics.
/// However, in this model, this is weaker due to use of [hooo::Theory] in the definition.
pub type NNPos<A> = Not<Not<Pos<A>>>;

/// `□p := p^true`.
///
/// A proposition is necessarily true if it is a tautology.
pub type Nec<A> = Tauto<A>;

/// `strong_pos(a) := p^true ⋁ false^(p^true ⋁ false^p)`.
///
/// This is a strong theoretical possibility which is equal to `□◇p` (see [eq_nec_pos_strong_pos]).
pub type StrongPos<A> = Or<Tauto<A>, Para<Uniform<A>>>;

/// `□¬□⊥`.
pub fn nec_consistency() -> Nec<Not<Nec<False>>> {
    fn f(_: True) -> Not<Nec<False>> {consistency()}
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
    para_to_tauto_not(para_lob)
}

/// `⊥^(¬□⊥ => ¬□¬□⊥)`.
pub fn para_godel(x: Imply<Not<Nec<False>>, Not<Nec<Not<Nec<False>>>>>) -> False {
    x(nec_consistency()(True))(nec_consistency())
}

/// `□¬(¬□⊥ => ¬□¬□⊥)`.
pub fn nec_not_godel() -> Nec<Not<Imply<Not<Nec<False>>, Not<Nec<Not<Nec<False>>>>>>> {
    para_to_tauto_not(para_godel)
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
    npara_to_pos(para_para_to_not_para(para_para_a))
}

/// `◇a => false^(false^a)`.
pub fn pos_to_para_para<A: DProp>(pos: Pos<A>) -> Para<Para<A>> {
    not_para_to_para_para(pos_to_npara(pos))
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

/// `¬¬◇a => ¬□¬a`.
pub fn nnpos_to_nnecn<A: Prop>(x: Not<Not<Pos<A>>>) -> Not<Nec<Not<A>>> {
    not::rev_triple(imply::modus_tollens(imply::modus_tollens(Rc::new(pos_to_nnecn)))(x))
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

/// `¬□¬a => ¬¬◇a`.
pub fn nnecn_to_nnpos<A: Prop>(x: Not<Nec<Not<A>>>) -> NNPos<A> {
    Rc::new(move |npos_a| {
        let y = and::from_de_morgan(npos_a);
        y.1(and::to_de_morgan((y.0, exists_to_not_para(x.clone()))))
    })
}

/// `¬¬◇a  ==  ¬□¬a`.
pub fn eq_nnpos_nnecn<A: Prop>() -> Eq<NNPos<A>, Not<Nec<Not<A>>>> {
    (Rc::new(nnpos_to_nnecn), Rc::new(nnecn_to_nnpos))
}

/// `a  =>  ¬¬◇a`.
pub fn to_nnpos<A: Prop>(a: A) -> NNPos<A> {
    Rc::new(move |npos_a| {
        let x = and::from_de_morgan(npos_a);
        imply::in_left(x.1, and::to_de_morgan)((x.0,
            exists_to_not_para(exists_true(a.clone()))))
    })
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

/// `□a => ◇a`.
pub fn nec_to_pos<A: Prop>(nec_a: Nec<A>) -> Pos<A> {Left(nec_a)}

/// `□◇a => strong_pos(a)`.
pub fn nec_pos_to_strong_pos<A: Prop>(x: Nec<Pos<A>>) -> StrongPos<A> {
    match hooo_or(x) {
        Left(tauto_tauto_a) => Left(tauto_tauto_a(True)),
        Right(tauto_theory_a) => Right(tauto_not_to_para(tauto_theory_a)),
    }
}

/// `strong_pos(a) => □◇a`.
pub fn strong_pos_to_nec_pos<A: Prop>(x: StrongPos<A>) -> Nec<Pos<A>> {
    use hooo::pow::PowExt;

    match x {
        Left(tauto_a) => tauto_a.lift().trans(Left),
        Right(para_uni_a) => para_to_tauto_not(para_uni_a).trans(Right),
    }
}

/// `□◇a  ==  strong_pos(a)`.
pub fn eq_nec_pos_strong_pos<A: Prop>() -> Eq<Nec<Pos<A>>, StrongPos<A>> {
    (Rc::new(nec_pos_to_strong_pos), Rc::new(strong_pos_to_nec_pos))
}

