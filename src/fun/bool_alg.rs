//! Boolean algebra

use super::*;

/// Boolean type.
#[derive(Clone, Copy)]
pub struct Bool(());
/// True value.
#[derive(Clone, Copy)]
pub struct Tr(());
/// False value.
#[derive(Clone, Copy)]
pub struct Fa(());

/// `bool : type(0)`.
pub fn bool_ty() -> Ty<Bool, Type<Z>> {unimplemented!()}
/// True type.
pub fn tr_ty() -> Ty<Tr, Bool> {unimplemented!()}
/// False type.
pub fn fa_ty() -> Ty<Fa, Bool> {unimplemented!()}
/// Boolean values.
pub fn bool_values<A: Prop>(_ty_a: Ty<A, Bool>) -> Or<Eq<A, Tr>, Eq<A, Fa>> {unimplemented!()}
/// True and false are exclusive.
pub fn para_eq_tr_fa(_: Eq<Tr, Fa>) -> False {unimplemented!()}
/// True and false are exclusive in products.
pub fn para_eq_and_tr_and_fa<A: Prop>(
    _ty_a: Ty<A, Bool>,
    _: Eq<And<A, Tr>, And<A, Fa>>
) -> False {unimplemented!()}

/// False1 function.
#[derive(Clone, Copy)]
pub struct FFalse1(());

/// Type of False1.
pub fn false1_ty() -> Ty<FFalse1, Pow<Bool, Bool>> {unimplemented!()}
/// False1 definition.
pub fn false1_def<A: Prop>(_: Ty<A, Bool>) -> Eq<App<FFalse1, A>, Tr> {unimplemented!()}

/// `(inv(false1) ~~ f) => false`.
pub fn para_inv_false1<F: Prop>(x: Q<Inv<FFalse1>, F>) -> False {
    let y0 = inv_val(x.clone(), false1_def(fa_ty()));
    let y1 = inv_val(x, false1_def(tr_ty()));
    para_eq_tr_fa(eq::transitivity(eq::symmetry(y1), y0))
}

/// Not function.
#[derive(Clone, Copy)]
pub struct FNot(());

/// Type of Not.
pub fn not_ty() -> Ty<FNot, Pow<Bool, Bool>> {unimplemented!()}
/// `not(false) = true`.
pub fn not_fa() -> Eq<App<FNot, Fa>, Tr> {unimplemented!()}
/// `not(true) = false`.
pub fn not_tr() -> Eq<App<FNot, Tr>, Fa> {unimplemented!()}
/// `inv(not) ~~ not`.
pub fn not_q() -> Q<Inv<FNot>, FNot> {unimplemented!()}

/// True1 function.
#[derive(Clone, Copy)]
pub struct FTrue1(());

/// Type of True1.
pub fn true1_ty() -> Ty<FTrue1, Pow<Bool, Bool>> {unimplemented!()}
/// True1 definition.
pub fn true1_def<A: Prop>(_: Ty<A, Bool>) -> Eq<App<FTrue1, A>, Tr> {unimplemented!()}

/// `(inv(true1) ~~ f) => false`.
pub fn para_inv_true1<F: Prop>(x: Q<Inv<FTrue1>, F>) -> False {
    let y0 = inv_val(x.clone(), true1_def(fa_ty()));
    let y1 = inv_val(x, true1_def(tr_ty()));
    para_eq_tr_fa(eq::transitivity(eq::symmetry(y1), y0))
}

/// And function.
#[derive(Copy, Clone)]
pub struct FAnd(());

/// Type of And.
pub fn and_ty() -> Ty<FAnd, Pow<Bool, And<Bool, Bool>>> {unimplemented!()}

/// `and(true, a) = a`.
pub fn and_tr<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FAnd, And<Tr, A>>, A> {unimplemented!()}

/// `and(false, a) = false`.
pub fn and_fa<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FAnd, And<Fa, A>>, Fa> {unimplemented!()}

/// `(inv(and) ~~ f) => false`.
pub fn para_inv_and<F: Prop>(x: Q<Inv<FAnd>, F>) -> False {
    let y0 = inv_val(x.clone(), and_fa(tr_ty()));
    let y1 = inv_val(x.clone(), and_fa(fa_ty()));
    let y2: Eq<And<Fa, Fa>, And<Fa, Tr>> = eq::transitivity(eq::symmetry(y1), y0);
    para_eq_and_tr_and_fa(fa_ty(), eq::symmetry(y2))
}

/// Or function.
#[derive(Copy, Clone)]
pub struct FOr(());

/// Type of Or.
pub fn or_ty() -> Ty<FOr, Pow<Bool, And<Bool, Bool>>> {unimplemented!()}

/// `or(true, a) = true`.
pub fn or_tr<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FOr, And<Tr, A>>, Tr> {unimplemented!()}

/// `or(false, a) = a`.
pub fn or_fa<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FOr, And<Fa, A>>, A> {unimplemented!()}

/// `(inv(or) ~~ f) => false`.
pub fn para_inv_or<F: Prop>(x: Q<Inv<FOr>, F>) -> False {
    let y0: Eq<App<Inv<FOr>, Tr>, And<Tr, Tr>> = inv_val(x.clone(), or_tr(tr_ty()));
    let y1: Eq<App<Inv<FOr>, Tr>, And<Tr, Fa>> = inv_val(x.clone(), or_tr(fa_ty()));
    para_eq_and_tr_and_fa(tr_ty(), eq::transitivity(eq::symmetry(y0), y1))
}
