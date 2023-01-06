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
/// `is_const(bool)`.
pub fn bool_is_const() -> IsConst<Bool> {unimplemented!()}
/// True type.
pub fn tr_ty() -> Ty<Tr, Bool> {unimplemented!()}
/// `is_const(true)`.
pub fn tr_is_const() -> IsConst<Tr> {unimplemented!()}
/// False type.
pub fn fa_ty() -> Ty<Fa, Bool> {unimplemented!()}
/// `is_const(false)`.
pub fn fa_is_const() -> IsConst<Fa> {unimplemented!()}
/// Boolean values.
pub fn bool_values<A: Prop>(_ty_a: Ty<A, Bool>) -> Or<Eq<A, Tr>, Eq<A, Fa>> {unimplemented!()}
/// True and false are exclusive.
pub fn para_eq_tr_fa(_: Eq<Tr, Fa>) -> False {unimplemented!()}
/// True and false are exclusive in tuples.
pub fn para_eq_tup_tr_tup_fa<A: Prop>(
    _ty_a: Ty<A, Bool>,
    _: Eq<Tup<A, Tr>, Tup<A, Fa>>
) -> False {unimplemented!()}

/// False1 function.
#[derive(Clone, Copy)]
pub struct FFalse1(());

/// Type of False1.
pub fn false1_ty() -> Ty<FFalse1, Pow<Bool, Bool>> {unimplemented!()}
/// `is_const(false1)`.
pub fn false1_is_const() -> IsConst<FFalse1> {unimplemented!()}
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
/// `is_const(not)`.
pub fn not_is_const() -> IsConst<FNot> {unimplemented!()}
/// `not(false) = true`.
pub fn not_fa() -> Eq<App<FNot, Fa>, Tr> {unimplemented!()}
/// `not(true) = false`.
pub fn not_tr() -> Eq<App<FNot, Tr>, Fa> {unimplemented!()}
/// `inv(not) ~~ not`.
pub fn not_q() -> Q<Inv<FNot>, FNot> {unimplemented!()}

/// `(not . not) == id`.
pub fn eq_not_not_id() -> Eq<Comp<FNot, FNot>, FId> {
    self_inv_to_eq_id(quality::to_eq(not_q()))
}

/// True1 function.
#[derive(Clone, Copy)]
pub struct FTrue1(());

/// Type of True1.
pub fn true1_ty() -> Ty<FTrue1, Pow<Bool, Bool>> {unimplemented!()}
/// `is_const(true1)`.
pub fn true1_is_const() -> IsConst<FTrue1> {unimplemented!()}
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
pub fn and_ty() -> Ty<FAnd, Pow<Bool, Tup<Bool, Bool>>> {unimplemented!()}
/// `is_const(and)`.
pub fn and_is_const() -> IsConst<FAnd> {unimplemented!()}
/// `and(true, a) = a`.
pub fn and_tr<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FAnd, Tup<Tr, A>>, A> {unimplemented!()}
/// `and(false, a) = false`.
pub fn and_fa<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FAnd, Tup<Fa, A>>, Fa> {unimplemented!()}

/// `(inv(and) ~~ f) => false`.
pub fn para_inv_and<F: Prop>(x: Q<Inv<FAnd>, F>) -> False {
    let y0 = inv_val(x.clone(), and_fa(tr_ty()));
    let y1 = inv_val(x.clone(), and_fa(fa_ty()));
    let y2: Eq<Tup<Fa, Fa>, Tup<Fa, Tr>> = eq::transitivity(eq::symmetry(y1), y0);
    para_eq_tup_tr_tup_fa(fa_ty(), eq::symmetry(y2))
}

/// Or function.
#[derive(Copy, Clone)]
pub struct FOr(());

/// Type of Or.
pub fn or_ty() -> Ty<FOr, Pow<Bool, Tup<Bool, Bool>>> {unimplemented!()}
/// `is_const(or)`.
pub fn or_is_const() -> IsConst<FOr> {unimplemented!()}
/// `or(true, a) = true`.
pub fn or_tr<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FOr, Tup<Tr, A>>, Tr> {unimplemented!()}
/// `or(false, a) = a`.
pub fn or_fa<A: Prop>(_ty_a: Ty<A, Bool>) -> Eq<App<FOr, Tup<Fa, A>>, A> {unimplemented!()}

/// `(inv(or) ~~ f) => false`.
pub fn para_inv_or<F: Prop>(x: Q<Inv<FOr>, F>) -> False {
    let y0 = inv_val(x.clone(), or_tr(tr_ty()));
    let y1 = inv_val(x.clone(), or_tr(fa_ty()));
    para_eq_tup_tr_tup_fa(tr_ty(), eq::transitivity(eq::symmetry(y0), y1))
}

/// Nand function.
pub type FNand = Comp<FNot, FAnd>;

/// Type of Nand.
pub fn nand_ty() -> Ty<FNand, Pow<Bool, Tup<Bool, Bool>>> {comp_ty(and_ty(), not_ty())}
/// `nand(true, a) = not(a)`.
pub fn nand_tr<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FNand, Tup<Tr, A>>, App<FNot, A>> {
    eq::in_left_arg(app_eq(and_tr(ty_a)), eq_app_comp())
}
/// `nand(false, a) = true`.
pub fn nand_fa<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FNand, Tup<Fa, A>>, Tr> {
    eq::transitivity(eq::in_left_arg(app_eq(and_fa(ty_a)), eq_app_comp()), not_fa())
}
