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
/// `false^(tr == fa)`.
///
/// True and false are exclusive.
pub fn para_eq_tr_fa(_: Eq<Tr, Fa>) -> False {unimplemented!()}
/// `∃ tr : bool { x } ⋀ ∃ fa : bool { x }  =>  x`.
pub fn bool_exists<X: Prop>(
    _case_tr: Exists<Ty<Tr, Bool>, X>,
    _case_fa: Exists<Ty<Fa, Bool>, X>
) -> X {unimplemented!()}

/// `(f : bool -> bool) ⋀ (g : bool -> bool) ⋀
//  (f(tr) == g(tr))^true ⋀ (f(fa) == g(fa))^true  =>  (f == g)^true`.
pub fn bool1_fun_ext<F: Prop, G: Prop>(
    ty_f: Ty<F, Pow<Bool, Bool>>,
    ty_g: Ty<G, Pow<Bool, Bool>>,
    case_tr: Tauto<Eq<App<F, Tr>, App<G, Tr>>>,
    case_fa: Tauto<Eq<App<F, Fa>, App<G, Fa>>>
) -> Eq<F, G> {
    bool_exists(app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_tr)),
                app_fun_ext(ty_f, ty_g, hooo::tr().trans(case_fa)))
}

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
/// `f : bool -> bool  =>  f[false1] == false1`.
pub fn eq_norm1_by_false1<F: Prop>(
    ty_f: Tauto<Ty<F, Pow<Bool, Bool>>>
) -> Eq<SymNorm1<F, FFalse1>, FFalse1> {
    fn case<F: Prop, A: Prop>((ty_f, ty_a): And<Ty<F, Pow<Bool, Bool>>, Ty<A, Bool>>) ->
    Eq<App<SymNorm1<F, FFalse1>, A>, App<FFalse1, A>> {
        eq::in_right_arg(eq::in_left_arg(false1_def(app_fun_ty(ty_f, app_fun_ty(inv_ty(false1_ty()),
            ty_a.clone()))), eq_app_norm1()), eq::symmetry(false1_def(ty_a)))
    }
    bool1_fun_ext(
        sym_norm1_ty(ty_f(True), false1_ty()),
        false1_ty(),
        hooo::hooo_rev_and((ty_f, tauto!(tr_ty()))).trans(case),
        hooo::hooo_rev_and((ty_f, tauto!(fa_ty()))).trans(case),
    )
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
/// `not[not] == not`.
pub fn eq_norm1_not_not() -> Eq<SymNorm1<FNot, FNot>, FNot> {
    (Rc::new(move |x| comp_id_left().0(comp_in_left_arg(comp_in_right_arg(x.0,
        quality::to_eq(not_q())), eq_not_not_id()))),
     Rc::new(move |x| Norm1(comp_in_right_arg(comp_in_left_arg(comp_id_left().1(x),
        eq::symmetry(eq_not_not_id())), eq::symmetry(quality::to_eq(not_q()))))))
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
/// `f : bool -> bool  =>  f[true1] == true1`.
pub fn eq_norm1_by_true1<F: Prop>(
    ty_f: Tauto<Ty<F, Pow<Bool, Bool>>>
) -> Eq<SymNorm1<F, FTrue1>, FTrue1> {
    fn case<F: Prop, A: Prop>((ty_f, ty_a): And<Ty<F, Pow<Bool, Bool>>, Ty<A, Bool>>) ->
    Eq<App<SymNorm1<F, FTrue1>, A>, App<FTrue1, A>> {
        eq::in_right_arg(eq::in_left_arg(true1_def(app_fun_ty(ty_f, app_fun_ty(inv_ty(true1_ty()),
            ty_a.clone()))), eq_app_norm1()), eq::symmetry(true1_def(ty_a)))
    }
    bool1_fun_ext(
        sym_norm1_ty(ty_f(True), true1_ty()),
        true1_ty(),
        hooo::hooo_rev_and((ty_f, tauto!(tr_ty()))).trans(case),
        hooo::hooo_rev_and((ty_f, tauto!(fa_ty()))).trans(case),
    )
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
    para_eq_tr_fa(tup_rev_eq_snd(fa_ty(), eq::symmetry(y2)))
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
    para_eq_tr_fa(tup_rev_eq_snd(tr_ty(), eq::transitivity(eq::symmetry(y0), y1)))
}

/// Nand function.
#[derive(Copy, Clone)]
pub struct FNand(pub Comp<FNot, FAnd>);

/// `nand  ==  not . and`.
pub fn nand_def() -> Eq<FNand, Comp<FNot, FAnd>> {eqx!(def FNand)}
/// Type of Nand.
pub fn nand_ty() -> Ty<FNand, Pow<Bool, Tup<Bool, Bool>>> {
    eqx!(comp_ty(and_ty(), not_ty()), nand_def, tyl)
}
/// `is_const(nand)`.
pub fn nand_is_const() -> IsConst<FNand> {
    eqx!(comp_is_const(and_is_const(), not_is_const()), nand_def, co)
}
/// `nand(true, a) = not(a)`.
pub fn nand_tr<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FNand, Tup<Tr, A>>, App<FNot, A>> {
    eqx!(eq::in_left_arg(app_eq(and_tr(ty_a)), eq_app_comp()), nand_def, am, l)
}
/// `nand(false, a) = true`.
pub fn nand_fa<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FNand, Tup<Fa, A>>, Tr> {
    let x = eq::transitivity(eq::in_left_arg(app_eq(and_fa(ty_a)), eq_app_comp()), not_fa());
    eqx!(x, nand_def, am, l)
}

/// Imply function.
#[derive(Copy, Clone)]
pub struct FImply(pub Comp<FOr, Par<FNot, FId>>);

/// `imply  ==  or . (not x id)`.
pub fn imply_def() -> Eq<FImply, Comp<FOr, Par<FNot, FId>>> {eqx!(def FImply)}
/// Type of Imply.
pub fn imply_ty() -> Ty<FImply, Pow<Bool, Tup<Bool, Bool>>> {
    eqx!(comp_ty(par_tup_fun_ty(not_ty(), id_ty()), or_ty()), imply_def, tyl)
}
/// `is_const(imply)`.
pub fn imply_is_const() -> IsConst<FImply> {
    let x = comp_is_const(par_tup_app_is_const(not_is_const(), id_is_const()), or_is_const());
    eqx!(x, imply_def, co)
}

/// `imply(true, a) = a`.
pub fn imply_tr<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FImply, Tup<Tr, A>>, A> {
    eqx!(eq::symmetry(eq::in_left_arg(eq::in_left_arg(eq_app_comp(), app_eq(
        par_tup_def(not_tr(), id_def(bool_ty(), ty_a.clone())))), or_fa(ty_a))), imply_def, am, l)
}
/// `imply(false, a) = true`.
pub fn imply_fa<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FImply, Tup<Fa, A>>, Tr> {
    eqx!(eq::symmetry(eq::in_left_arg(eq::in_left_arg(eq_app_comp(), app_eq(
        par_tup_def(not_fa(), id_def(bool_ty(), ty_a.clone())))), or_tr(ty_a))), imply_def, am, l)
}

/// Composable equality.
#[derive(Copy, Clone)]
pub struct FEq(());

/// `eq{t : type(0)} : t x t -> bool`.
pub fn eq_ty<T: Prop>(_ty_t: Ty<T, Type<Z>>) -> Ty<FEq, Pow<Bool, Tup<T, T>>> {unimplemented!()}
/// `is_const(eq)`.
pub fn eq_is_const() -> IsConst<FEq> {unimplemented!()}
/// `eq((a, a)) = true`.
pub fn eq_refl<A: Prop>() -> Eq<App<FEq, Tup<A, A>>, Tr> {unimplemented!()}

/// `(a == b)  =>  eq((a, b)) = true`.
pub fn eq_lift<A: Prop, B: Prop>(x: Eq<A, B>) -> Eq<App<FEq, Tup<A, B>>, Tr> {
    eq::eq_left(app_eq(tup_eq_snd(x))).0(eq_refl())
}
/// `eq((a, b)) = false  =>  ¬(a == b)`.
pub fn eq_fa_lower<A: Prop, B: Prop>(x: Eq<App<FEq, Tup<A, B>>, Fa>) -> Not<Eq<A, B>> {
    Rc::new(move |eq_ab| para_eq_tr_fa(eq::in_left_arg(x.clone(), eq_lift(eq_ab))))
}

/// `and . ((f x (not . eq)) . dup)`.
///
/// For any `a, b`, this is `f((a, b)) & !eq((a, b))`.
#[derive(Copy, Clone)]
pub struct AndNotEq<F: Prop>(pub Comp<FAnd, Comp<Par<F, Comp<FNot, FEq>>, Dup>>);
