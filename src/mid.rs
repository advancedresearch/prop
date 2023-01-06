//! # Middle Exponential Logic
//!
//! By building on Existential Logic and Exponential Propositions (HOOO),
//! it is possible to talk about nuances of middle propositions.
//!
//! All middle exponential propositions implies a theory (in HOOO EP).
//!
//! ### Up, Down and Middle
//!
//! The basic middle exponential propositions are:
//!
//! ```text
//! up(a) = (¬¬a ⋀ ¬(a^true))
//! down(a) = (¬a ⋀ ¬(false^a))
//! mid(a) = up(a) ⋁ down(a)
//! ```
//!
//! - The `up(a)` proposition is close to `a^true`
//! - The `down(a)` proposition is close to `false^a`
//! - The `mid(a)` proposition is close to `theory(a)`
//!
//! ### Lifting existential propositions to middle exponential propositions
//!
//! `theory(a) => mid(a)`
//!
//! This theorem is provable when `¬¬a ⋁ ¬a` (Excluded Middle of Non-Existence).

use crate::*;
use existence::*;
use hooo::*;

/// An up proposition `¬¬a ⋀ ¬(a^true)`.
pub type Up<A> = And<Not<Not<A>>, Not<Tauto<A>>>;
/// A down proposition `¬a ⋀ ¬(false^a)`.
pub type Down<A> = And<Not<A>, Not<Para<A>>>;
/// A middle proposition `(¬¬a ⋀ ¬(a^true)) ⋁ (¬a ⋀ ¬(false^a))`.
pub type Mid<A> = Or<Up<A>, Down<A>>;
/// A virtual middle proposition `a ⋀ ¬(a^true)`.
pub type Virtual<A> = And<A, Not<Tauto<A>>>;

/// A middle Catuṣkoṭi proposition `(a^true ⋁ false^a) ⋁ (up(a) ⋁ down(a))`.
pub type MidCatuskoti<A> = Or<Uniform<A>, Mid<A>>;

/// `theory(a) => mid(a)`.
pub fn theory_to_mid<A: EProp>(th_a: Theory<A>) -> Mid<A> {
    let (ntauto_a, npara_a) = and::from_de_morgan(th_a);
    match A::e() {
        Left(nna) => Left((nna, ntauto_a)),
        Right(na) => Right((na, npara_a)),
    }
}

/// `mid(a) => theory(a)`.
pub fn mid_to_theory<A: Prop>(ma: Mid<A>) -> Theory<A> {
    match ma {
        Left(up) => up_to_theory(up),
        Right(down) => down_to_theory(down),
    }
}

/// `virtual(a) => theory(a)`.
pub fn virtual_to_theory<A: Prop>((a, ntauto_a): Virtual<A>) -> Theory<A> {
    Rc::new(move |uni_a| {
        match uni_a {
            Left(tauto_a) => ntauto_a(tauto_a),
            Right(para_a) => para_a(a.clone())
        }
    })
}

/// `up(a) => theory(a)`.
pub fn up_to_theory<A: Prop>((nna, ntauto_a): Up<A>) -> Theory<A> {
    and::to_de_morgan((ntauto_a, not_not_to_not_para(nna)))
}

/// `theory(a) => up(a)`.
pub fn theory_to_up<A: EProp>(theory_a: Theory<A>) -> Up<A> {
    let (ntauto_a, npara_a) = and::from_de_morgan(theory_a);
    (Rc::new(move |na| {
        pow_not_e(npara_a.clone())(na)
    }), ntauto_a)
}

/// `down(a) => theory(a)`.
pub fn down_to_theory<A: Prop>((na, npara_a): Down<A>) -> Theory<A> {
    Rc::new(move |uni_a| {
        match uni_a {
            Left(tauto_a) => na(tauto_a(True)),
            Right(para_a) => npara_a(para_a)
        }
    })
}

/// `down(a) => up(a)`.
pub fn down_to_up<A: EProp>(x: Down<A>) -> Up<A> {
    theory_to_up(down_to_theory(x))
}

/// `up(a) => ¬down(a)`.
pub fn up_to_not_down<A: Prop>(up: Up<A>) -> Not<Down<A>> {
    Rc::new(move |down| up.clone().0(down.0))
}

/// `down(a) => ¬up(a)`.
pub fn down_to_not_up<A: Prop>(down: Down<A>) -> Not<Up<A>> {
    Rc::new(move |up| up.0(down.clone().0))
}

/// `up(a) => (¬¬a ⋁ ¬a)`.
pub fn up_to_e<A: Prop>(up: Up<A>) -> E<A> {
    Left(up.0)
}

/// `down(a) => (a ⋁ ¬a)`.
pub fn down_to_excm<A: Prop>(down: Down<A>) -> ExcM<A> {
    Right(down.0)
}

/// `down(a) => (¬¬a ⋁ ¬a)`.
pub fn down_to_e<A: Prop>(down: Down<A>) -> E<A> {
    excm_to_e(down_to_excm(down))
}

/// `mid(a) => (¬¬a ⋁ ¬a)`.
pub fn mid_to_e<A: Prop>(mid: Mid<A>) -> E<A> {
    match mid {
        Left(up) => up_to_e(up),
        Right(down) => down_to_e(down),
    }
}

/// `mid(a) => ((¬¬a ⋁ ¬a) ⋀ theory(a))`.
pub fn mid_to_and_e_theory<A: Prop>(mid: Mid<A>) -> And<E<A>, Theory<A>> {
    (mid_to_e(mid.clone()), mid_to_theory(mid))
}

/// `((¬¬a ⋁ ¬a) ⋀ theory(a)) => mid(a)`.
pub fn and_e_theory_to_mid<A: Prop>((ea, th_a): And<E<A>, Theory<A>>) -> Mid<A> {
    let (ntauto_a, npara_a) = and::from_de_morgan(th_a);
    match ea {
        Left(nna) => Left((nna, ntauto_a)),
        Right(na) => Right((na, npara_a)),
    }
}

/// `mica(a) => (¬¬a ⋁ ¬a)`.
pub fn mica_to_e<A: Prop>(c: MidCatuskoti<A>) -> E<A> {
    match c {
        Left(Left(tauto_a)) => Left(not::double(tauto_a(True))),
        Left(Right(para_a)) => Right(para_to_not(para_a)),
        Right(mid_a) => mid_to_e(mid_a),
    }
}

/// `(up(a) ⋀ down(a)) => false`.
pub fn paradox<A: Prop>((up_a, down_a): And<Up<A>, Down<A>>) -> False {
    down_to_not_up(down_a)(up_a)
}

/// `up(a) => a`.
pub fn up<A: DProp>(up: Up<A>) -> A {up_excm(up, A::decide())}

/// `up(a) ⋀ (a ⋁ ¬a)  =>  a`.
pub fn up_excm<A: Prop>(up: Up<A>, excm: ExcM<A>) -> A {
    match excm {
        Left(a) => a,
        Right(na) => not::absurd(up.0, na),
    }
}

/// `down(a) => ¬a`.
pub fn down<A: Prop>((na, _): Down<A>) -> Not<A> {na}

/// `up(a) => virtual(a)`.
pub fn up_to_virtual<A: DProp>(up: Up<A>) -> Virtual<A> {up_to_virtual_excm(up, A::decide())}

/// `up(a) ⋀ (a ⋁ ¬a)  =>  virtual(a)`.
pub fn up_to_virtual_excm<A: Prop>(up: Up<A>, excm: ExcM<A>) -> Virtual<A> {
    (up_excm(up.clone(), excm), up.1)
}

/// `down(a) => virtual(¬a)`.
pub fn down_to_virtual_not<A: Prop>(down_a: Down<A>) -> Virtual<Not<A>> {
    (down(down_a.clone()), imply::in_left(down_a.1, |x| tauto_not_to_para(x)))
}

/// `down(a) => false`.
pub fn absurd_down<A: EProp>(x: Down<A>) -> False {
    up_to_not_down(down_to_up(x.clone()))(x)
}

/// `theory(a) => false`.
pub fn absurd_theory<A: DProp>(x: Theory<A>) -> False {
    not_theory()(x)
}

/// `theory(a) ⋀ (a ⋁ ¬a)^true  =>  false`.
pub fn absurd_theory_tauto_excm<A: Prop>(x: Theory<A>, y: Tauto<ExcM<A>>) -> False {
    tauto_excm_to_not_theory(y)(x)
}
