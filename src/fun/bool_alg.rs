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
pub fn bool1_exists<X: Prop>(
    _case_fa: Exists<Ty<Fa, Bool>, X>,
    _case_tr: Exists<Ty<Tr, Bool>, X>,
) -> X {unimplemented!()}
/// `∃ (fa, fa) : (bool, bool) { x } ⋀
///  ∃ (fa, tr) : (bool, bool) { x } ⋀
///  ∃ (tr, fa) : (bool, bool) { x } ⋀
///  ∃ (tr, tr) : (bool, bool) { x }`.
pub fn bool2_exists<X: Prop>(
    _case_fa_fa: Exists<Ty<Tup<Fa, Fa>, Tup<Bool, Bool>>, X>,
    _case_fa_tr: Exists<Ty<Tup<Fa, Tr>, Tup<Bool, Bool>>, X>,
    _case_tr_fa: Exists<Ty<Tup<Tr, Fa>, Tup<Bool, Bool>>, X>,
    _case_tr_tr: Exists<Ty<Tup<Tr, Tr>, Tup<Bool, Bool>>, X>,
) -> X {unimplemented!()}

/// `(f : bool -> bool) ⋀ (g : bool -> bool) ⋀
//  (f(tr) == g(tr))^true ⋀ (f(fa) == g(fa))^true  =>  (f == g)^true`.
pub fn bool1_fun_ext<F: Prop, G: Prop>(
    ty_f: Ty<F, Pow<Bool, Bool>>,
    ty_g: Ty<G, Pow<Bool, Bool>>,
    case_tr: Tauto<Eq<App<F, Tr>, App<G, Tr>>>,
    case_fa: Tauto<Eq<App<F, Fa>, App<G, Fa>>>
) -> Eq<F, G> {
    bool1_exists(app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_fa)),
                app_fun_ext(ty_f, ty_g, hooo::tr().trans(case_tr)))
}
/// `(f : (bool, bool) -> bool) ⋀ (g : (bool, bool) -> bool) ⋀
/// (f(fa, fa) == g(fa, fa))^true ⋀
/// (f(fa, tr) == g(fa, tr))^true ⋀
/// (f(tr, fa) == g(tr, fa))^true ⋀
/// (f(tr, tr) == g(tr, tr))^true`.
pub fn bool2_fun_ext<F: Prop, G: Prop>(
    ty_f: Ty<F, Pow<Bool, Tup<Bool, Bool>>>,
    ty_g: Ty<G, Pow<Bool, Tup<Bool, Bool>>>,
    case_fa_fa: Tauto<Eq<App<F, Tup<Fa, Fa>>, App<G, Tup<Fa, Fa>>>>,
    case_fa_tr: Tauto<Eq<App<F, Tup<Fa, Tr>>, App<G, Tup<Fa, Tr>>>>,
    case_tr_fa: Tauto<Eq<App<F, Tup<Tr, Fa>>, App<G, Tup<Tr, Fa>>>>,
    case_tr_tr: Tauto<Eq<App<F, Tup<Tr, Tr>>, App<G, Tup<Tr, Tr>>>>,
) -> Eq<F, G> {
    bool2_exists(app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_fa_fa)),
                 app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_fa_tr)),
                 app_fun_ext(ty_f.clone(), ty_g.clone(), hooo::tr().trans(case_tr_fa)),
                 app_fun_ext(ty_f, ty_g, hooo::tr().trans(case_tr_tr)))
}
/// `(a : bool) ⋀ x^(a == tr) ⋀ x^(a == fa)  =>  x`.
pub fn bool1_cover<A: Prop, X: Prop>(
    ty_a: Ty<A, Bool>,
    pow_x_eq_a_tr: Pow<X, Eq<A, Tr>>,
    pow_x_eq_a_fa: Pow<X, Eq<A, Fa>>,
) -> X {cover(ty_a, bool_values, pow_x_eq_a_tr, pow_x_eq_a_fa)}
/// `a : bool  =>  (a == tr) ⋁ ¬(a == tr)`.
pub fn bool_excm_eq_tr<A: Prop>(ty_a: Ty<A, Bool>) -> ExcM<Eq<A, Tr>> {
    match bool_values(ty_a) {
        Left(x) => Left(x),
        Right(x) =>
            Right(Rc::new(move |y| para_eq_tr_fa(eq::transitivity(eq::symmetry(y), x.clone()))))
    }
}
/// `a : bool  =>  (a == fa) ⋁ ¬(a == fa)`.
pub fn bool_excm_eq_fa<A: Prop>(ty_a: Ty<A, Bool>) -> ExcM<Eq<A, Fa>> {
    match bool_values(ty_a) {
        Left(x) =>
            Right(Rc::new(move |y| para_eq_tr_fa(eq::transitivity(eq::symmetry(x.clone()), y)))),
        Right(x) => Left(x)
    }
}
/// `∃ a : bool { a == tr }  =>  (a == tr)^(a : bool)`.
pub fn bool_exists_to_pow_eq_tr<A: Prop>(
    x: Exists<Ty<A, Bool>, Eq<A, Tr>>
) -> Pow<Eq<A, Tr>, Ty<A, Bool>> {hooo::exists_excm_to_pow(x, bool_excm_eq_tr)}
/// `∃ a : bool { a == fa }  =>  (a == fa)^(a : bool)`.
pub fn bool_exists_to_pow_eq_fa<A: Prop>(
    x: Exists<Ty<A, Bool>, Eq<A, Fa>>
) -> Pow<Eq<A, Fa>, Ty<A, Bool>> {hooo::exists_excm_to_pow(x, bool_excm_eq_fa)}

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

/// `idb := id{bool}`.
pub type FIdb = App<FId, Bool>;

/// `idb(a)`.
pub type Idb<A> = App<FIdb, A>;

/// `idb : bool -> bool`.
pub fn idb_ty() -> Ty<FIdb, Pow<Bool, Bool>> {id_ty(bool_ty())}
/// `is_const(idb)`.
pub fn idb_is_const() -> IsConst<FIdb> {id_is_const(bool_is_const())}
/// `a : bool  =>  idb(a) = a`.
pub fn idb_def<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<Idb<A>, A> {
    id_def(bool_ty(), ty_a)
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

/// `(not . not) == idb`.
pub fn eq_not_not_idb() -> Eq<Comp<FNot, FNot>, FIdb> {
    self_inv_to_eq_id(not_ty(), quality::to_eq(not_q()))
}
/// `not[not] == not`.
pub fn eq_norm1_not_not() -> Eq<SymNorm1<FNot, FNot>, FNot> {
    (Rc::new(move |x| comp_id_left(not_ty()).0(comp_in_left_arg(comp_in_right_arg(x.0,
        quality::to_eq(not_q())), eq_not_not_idb()))),
     Rc::new(move |x| Norm1(comp_in_right_arg(comp_in_left_arg(comp_id_left(not_ty()).1(x),
        eq::symmetry(eq_not_not_idb())), eq::symmetry(quality::to_eq(not_q()))))))
}
/// `x : bool  =>  not(not(x)) == x`.
pub fn eq_not_not<X: Prop>(ty_x: Ty<X, Bool>) -> Eq<App<FNot, App<FNot, X>>, X> {
    use eq::transitivity as trans;

    trans(eq_app_comp(), trans(app_map_eq(eq_not_not_idb()), id_def(bool_ty(), ty_x)))
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
/// `and[not] == or`.
pub fn eq_norm2_and_not_or() -> Eq<SymNorm2<FAnd, FNot>, FOr> {
    fn bridge<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop>(
        eq_a_c: Eq<A, C>, eq_b_d: Eq<B, D>,
        x: Eq<App<SymNorm2<FAnd, FNot>, Tup<C, D>>, E>, or_c_d: Eq<App<FOr, Tup<C, D>>, E>,
    ) -> Eq<App<SymNorm2<FAnd, FNot>, Tup<A, B>>, App<FOr, Tup<A, B>>> {
        let y: Eq<Tup<A, B>, Tup<C, D>> = tup_eq(eq_a_c, eq_b_d);
        eq::in_right_arg(eq::in_right_arg(app_eq(y.clone()),
            eq::in_right_arg(x, eq::symmetry(or_c_d))), eq::symmetry(app_eq(y)))
    }
    fn case<A: Prop, B: Prop>(ty_a: Ty<A, Bool>, ty_b: Ty<B, Bool>) ->
    Eq<App<SymNorm2<FAnd, FNot>, Tup<A, B>>, App<FOr, Tup<A, B>>> {
        match (bool_values(ty_a), bool_values(ty_b)) {
            (Right(eq_a_fa), Right(eq_b_fa)) => bridge(eq_a_fa, eq_b_fa, sym_norm2_app(
                not_q(), not_tr(), not_tr(), and_tr(tr_ty()), not_tr()), or_fa(fa_ty())),
            (Right(eq_a_fa), Left(eq_b_tr)) => bridge(eq_a_fa, eq_b_tr, sym_norm2_app(
                not_q(), not_tr(), not_fa(), and_tr(fa_ty()), not_fa()), or_fa(tr_ty())),
            (Left(eq_a_tr), Right(eq_b_fa)) => bridge(eq_a_tr, eq_b_fa, sym_norm2_app(
                not_q(), not_fa(), not_tr(), and_fa(tr_ty()), not_fa()), or_tr(fa_ty())),
            (Left(eq_a_tr), Left(eq_b_tr)) => bridge(eq_a_tr, eq_b_tr, sym_norm2_app(
                not_q(), not_fa(), not_fa(), and_fa(fa_ty()), not_fa()), or_tr(tr_ty())),
        }
    }
    bool2_fun_ext(sym_norm2_ty(and_ty(), not_ty()), or_ty(),
        tauto!(case(fa_ty(), fa_ty())), tauto!(case(fa_ty(), tr_ty())),
        tauto!(case(tr_ty(), fa_ty())), tauto!(case(tr_ty(), tr_ty())))
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
/// `or[not] == and`.
pub fn eq_norm2_or_not_and() -> Eq<SymNorm2<FOr, FNot>, FAnd> {
    fn bridge<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop>(
        eq_a_c: Eq<A, C>, eq_b_d: Eq<B, D>,
        x: Eq<App<SymNorm2<FOr, FNot>, Tup<C, D>>, E>, or_c_d: Eq<App<FAnd, Tup<C, D>>, E>,
    ) -> Eq<App<SymNorm2<FOr, FNot>, Tup<A, B>>, App<FAnd, Tup<A, B>>> {
        let y: Eq<Tup<A, B>, Tup<C, D>> = tup_eq(eq_a_c, eq_b_d);
        eq::in_right_arg(eq::in_right_arg(app_eq(y.clone()),
            eq::in_right_arg(x, eq::symmetry(or_c_d))), eq::symmetry(app_eq(y)))
    }
    fn case<A: Prop, B: Prop>(ty_a: Ty<A, Bool>, ty_b: Ty<B, Bool>) ->
    Eq<App<SymNorm2<FOr, FNot>, Tup<A, B>>, App<FAnd, Tup<A, B>>> {
        match (bool_values(ty_a), bool_values(ty_b)) {
            (Right(eq_a_fa), Right(eq_b_fa)) => bridge(eq_a_fa, eq_b_fa, sym_norm2_app(
                not_q(), not_tr(), not_tr(), or_tr(tr_ty()), not_tr()), and_fa(fa_ty())),
            (Right(eq_a_fa), Left(eq_b_tr)) => bridge(eq_a_fa, eq_b_tr, sym_norm2_app(
                not_q(), not_tr(), not_fa(), or_tr(fa_ty()), not_tr()), and_fa(tr_ty())),
            (Left(eq_a_tr), Right(eq_b_fa)) => bridge(eq_a_tr, eq_b_fa, sym_norm2_app(
                not_q(), not_fa(), not_tr(), or_fa(tr_ty()), not_tr()), and_tr(fa_ty())),
            (Left(eq_a_tr), Left(eq_b_tr)) => bridge(eq_a_tr, eq_b_tr, sym_norm2_app(
                not_q(), not_fa(), not_fa(), or_fa(fa_ty()), not_fa()), and_tr(tr_ty())),
        }
    }
    bool2_fun_ext(sym_norm2_ty(or_ty(), not_ty()), and_ty(),
        tauto!(case(fa_ty(), fa_ty())), tauto!(case(fa_ty(), tr_ty())),
        tauto!(case(tr_ty(), fa_ty())), tauto!(case(tr_ty(), tr_ty())))
}

/// `eqb`.
pub type FEqb = App<FEq, Bool>;

/// `eqb(a, b)`.
pub type Eqb<A, B> = App<FEqb, Tup<A, B>>;

/// `eqb : (bool, bool) -> bool`.
pub fn eqb_ty() -> Ty<FEqb, Pow<Bool, Tup<Bool, Bool>>> {equal_ty(bool_ty())}
/// `eqb(fa, fa) == tr`.
pub fn eqb_fa_fa() -> Eq<Eqb<Fa, Fa>, Tr> {equal_refl(fa_ty())}
/// `eqb(tr, fa) == fa`.
pub fn eqb_tr_fa() -> Eq<Eqb<Tr, Fa>, Fa> {equal_from_para_eq(tr_ty(), fa_ty(), para_eq_tr_fa)}
/// `eqb(fa, tr) == fa`.
pub fn eqb_fa_tr() -> Eq<Eqb<Fa, Tr>, Fa> {
    equal_from_para_eq(fa_ty(), tr_ty(), hooo::pow_transitivity(eq::symmetry, para_eq_tr_fa))
}
/// `eqb(tr, tr) == tr`.
pub fn eqb_tr_tr() -> Eq<Eqb<Tr, Tr>, Tr> {equal_refl(tr_ty())}
/// `a : bool  =>  eqb(tr, a) == a`.
pub fn eqb_tr<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<Eqb<Tr, A>, A> {
    match bool_values(ty_a) {
        Left(eq_a_tr) =>
            eq::trans3(app_eq(tup_eq_snd(eq_a_tr.clone())), eqb_tr_tr(), eq::symmetry(eq_a_tr)),
        Right(eq_a_fa) =>
            eq::trans3(app_eq(tup_eq_snd(eq_a_fa.clone())), eqb_tr_fa(), eq::symmetry(eq_a_fa)),
    }
}
/// `a : bool  =>  eqb(fa, a) == not(a)`.
pub fn eqb_fa<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<Eqb<Fa, A>, App<FNot, A>> {
    match bool_values(ty_a) {
        Left(eq_a_tr) => eq::trans4(app_eq(tup_eq_snd(eq_a_tr.clone())), eqb_fa_tr(),
            eq::symmetry(not_tr()), app_eq(eq::symmetry(eq_a_tr))),
        Right(eq_a_fa) => eq::trans4(app_eq(tup_eq_snd(eq_a_fa.clone())), eqb_fa_fa(),
            eq::symmetry(not_fa()), app_eq(eq::symmetry(eq_a_fa))),
    }
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
pub struct FImply(pub Comp<FOr, Par<FNot, FIdb>>);

/// `imply  ==  or . (not x id)`.
pub fn imply_def() -> Eq<FImply, Comp<FOr, Par<FNot, FIdb>>> {eqx!(def FImply)}
/// `imply : (bool, bool) -> bool`.
pub fn imply_ty() -> Ty<FImply, Pow<Bool, Tup<Bool, Bool>>> {
    eqx!(comp_ty(par_tup_fun_ty(not_ty(), id_ty(bool_ty())), or_ty()), imply_def, tyl)
}
/// `is_const(imply)`.
pub fn imply_is_const() -> IsConst<FImply> {
    let x = comp_is_const(par_tup_app_is_const(not_is_const(), idb_is_const()), or_is_const());
    eqx!(x, imply_def, co)
}
/// `a : bool  =>  imply(true, a) = a`.
pub fn imply_tr<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FImply, Tup<Tr, A>>, A> {
    eqx!(eq::symmetry(eq::in_left_arg(eq::in_left_arg(eq_app_comp(), app_eq(
        par_tup_def(not_tr(), id_def(bool_ty(), ty_a.clone())))), or_fa(ty_a))), imply_def, am, l)
}
/// `a : bool  =>  imply(false, a) = true`.
pub fn imply_fa<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<App<FImply, Tup<Fa, A>>, Tr> {
    eqx!(eq::symmetry(eq::in_left_arg(eq::in_left_arg(eq_app_comp(), app_eq(
        par_tup_def(not_fa(), id_def(bool_ty(), ty_a.clone())))), or_tr(ty_a))), imply_def, am, l)
}

/// Xor function.
#[derive(Copy, Clone)]
pub struct FXor(pub Comp<FNot, FEqb>);

/// `xor(a, b)`.
pub type Xor<A, B> = App<FXor, Tup<A, B>>;

/// `xor  ==  not . eqb`.
pub fn xor_def() -> Eq<FXor, Comp<FNot, FEqb>> {eqx!(def FXor)}
/// `xor : (bool, bool) -> bool`.
pub fn xor_ty() -> Ty<FXor, Pow<Bool, Tup<Bool, Bool>>> {
    eqx!(comp_ty(eqb_ty(), not_ty()), xor_def, tyl)
}
/// `a : bool  =>  xor(tr, a) = not(a)`.
pub fn xor_tr<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<Xor<Tr, A>, App<FNot, A>> {
    eqx!(eq::transitivity(eq::symmetry(eq_app_comp()), app_eq(eqb_tr(ty_a))), xor_def, am, l)
}
/// `a : bool  =>  xor(fa, a) = a`.
pub fn xor_fa<A: Prop>(ty_a: Ty<A, Bool>) -> Eq<Xor<Fa, A>, A> {
    eqx!(eq::trans5(eq::symmetry(eq_app_comp()), app_eq(eqb_fa(ty_a.clone())), eq_app_comp(),
        app_map_eq(eq_not_not_idb()), idb_def(ty_a)), xor_def, am, l)
}

/// `and . ((f x (not . eq)) . dup)`.
///
/// For any `a, b`, this is `f((a, b)) & !eq((a, b))`.
#[derive(Copy, Clone)]
pub struct AndNotEq<F: Prop>(pub Comp<FAnd, Comp<Par<F, Comp<FNot, FEq>>, Dup>>);

/// `all(f) := true1 . f == f`.
///
/// This is a point-free version of a for-all quantifier.
pub type All<F> = Eq<Comp<FTrue1, F>, F>;

/// `any(f) := ¬all(not . f)`.
///
/// This is a point-free version of a there-exists quantifier.
pub type Any<F> = Not<All<Comp<FNot, F>>>;
