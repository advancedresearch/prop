#![deny(unsafe_op_in_unsafe_fn)]

//! # Model of Types in Path Semantics

use super::*;

/// Models a type relation `a : t`.
pub type Ty<A, T> = And<Imply<A, T>, POrdProof<A, T>>;

/// `x_{n} : ltrue{n+1}`.
pub fn ltrue<X: LProp>() -> Ty<X, LTrue<S<X::N>>>
    where X::N: Lt<S<X::N>> + Default
{
    (LTrue(Default::default()).map_any(), POrdProof::default())
}

/// `(a : b) ⋀ (a == c)  =>  (c : b)`.
pub fn in_left_arg<A: Prop, B: Prop, C: Prop>((ab, pord): Ty<A, B>, eq: Eq<A, C>) -> Ty<C, B> {
    (imply::in_left_arg(ab, eq.clone()), pord.by_eq_left(eq))
}

/// `(a : b) ⋀ (b == c)  =>  (a : c)`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [POrdProof::by_eq_right].
pub unsafe fn in_right_arg<A: Prop, B: Prop, C: Prop>(
    (ab, pord): Ty<A, B>, eq: Eq<B, C>
) -> Ty<A, C> {
    (imply::in_right_arg(ab, eq.clone()), unsafe {pord.by_eq_right(eq)})
}

/// `(a == b)  =>  (a : c) == (b : c)`.
pub fn eq_left<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Ty<A, C>, Ty<B, C>> {
    let x2 = eq::symmetry(x.clone());
    (Rc::new(move |ty_a| in_left_arg(ty_a, x.clone())),
     Rc::new(move |ty_b| in_left_arg(ty_b, x2.clone())))
}
/// `(b == c)  =>  (a : b) == (a : c)`.
///
/// # Safety
///
/// This theorem is unsafe due to use oof [in_right_arg].
pub unsafe fn eq_right<A: Prop, B: Prop, C: Prop>(x: Eq<B, C>) -> Eq<Ty<A, B>, Ty<A, C>> {
    let x2 = eq::symmetry(x.clone());
    (Rc::new(move |ty_a| unsafe {in_right_arg(ty_a, x.clone())}),
     Rc::new(move |ty_a| unsafe {in_right_arg(ty_a, x2.clone())}))
}

/// `(a : b) ⋀ (b => c)  =>  (a : c)`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [POrdProof::by_imply_right].
pub unsafe fn imply_right<A: Prop, B: Prop, C: Prop>(x: Ty<A, B>, y: Imply<B, C>) -> Ty<A, C> {
    (imply::transitivity(x.0, y.clone()), unsafe {x.1.by_imply_right(y)})
}

/// `(x : false) => ¬x`.
pub fn ty_false<X: Prop>(ty_x_false: Ty<X, False>) -> Not<X> {ty_x_false.0}

/// `(true : x) => x`.
pub fn ty_true<X: Prop>(ty_true_x: Ty<True, X>) -> X {ty_true_x.0(True)}

/// `a => (true : a)`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [in_right_arg].
pub unsafe fn ty_rev_true<A: Prop>(a: A) -> Ty<True, A> {
    unsafe {in_right_arg(true_true(), (a.map_any(), True.map_any()))}
}

/// `(a : x) ⋀ a => (true : x)`.
pub fn triv<A: Prop, X: Prop>(ty_a_x: Ty<A, X>, a: A) -> Ty<True, X> {
    in_left_arg(ty_a_x, (True.map_any(), a.map_any()))
}

/// `(x : a) ⋀ ¬a => (x : false)`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [in_right_arg].
pub unsafe fn non_triv<X: Prop, A: Prop>(
    ty_x_a: Ty<X, A>,
    na: Not<A>,
) -> Ty<X, False> {
    let eq_a_false: Eq<A, False> =
        (Rc::new(move |a| na(a)), Rc::new(move |fa| imply::absurd()(fa)));
    unsafe {in_right_arg(ty_x_a, eq_a_false)}
}

/// `true == ltrue{n}`.
pub fn eq_true_ltrue<N: Nat>() -> Eq<True, LTrue<N>> {
    (LTrue(Default::default()).map_any(), True.map_any())
}

/// `true : ltrue{n+1}`.
pub fn true_ltrue<N: Nat>() -> Ty<True, LTrue<S<N>>> {
    in_left_arg(ltrue(), eq::symmetry(eq_true_ltrue()))
}

/// `true : true`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [in_right_arg].
pub unsafe fn true_true() -> Ty<True, True> {
    let x = in_left_arg(ltrue(), eq::symmetry(eq_true_ltrue::<Z>()));
    unsafe {in_right_arg(x, eq::symmetry(eq_true_ltrue::<S<Z>>()))}
}

/// `(x : a) ⋀ (y : b)  =>  ((x ⋀ y) : (a ⋀ b))`.
pub fn and<X: Prop, Y: Prop, A: Prop, B: Prop>(
    (xa, pord_xa): Ty<X, A>,
    (yb, pord_yb): Ty<Y, B>,
) -> Ty<And<X, Y>, And<A, B>> {
    let imply_and_xy_and_ab: Imply<And<X, Y>, And<A, B>> = Rc::new(move |(x, y)| (xa(x), yb(y)));
    (imply_and_xy_and_ab, pord_xa.and(pord_yb))
}

/// `(x : a) ⋀ (y : b)  =>  ((x ⋁ y) : (a ⋁ b))`.
pub fn or<X: Prop, Y: Prop, A: Prop, B: Prop>(
    (xa, pord_xa): Ty<X, A>,
    (yb, pord_yb): Ty<Y, B>,
) -> Ty<Or<X, Y>, Or<A, B>> {
    let or_xy_or_ab: Imply<Or<X, Y>, Or<A, B>> = Rc::new(move |or_xy| {
        match or_xy {
            Left(x) => Left(xa(x)),
            Right(y) => Right(yb(y)),
        }
    });
    (or_xy_or_ab, pord_xa.or(pord_yb))
}

/// `(x : a) ⋀ (y : b) ⋀ hom(x, y)  =>  ((x => y) : (a => b))`.
pub fn hom_imply<X: Prop, Y: Prop, A: Prop, B: Prop>(
    (xa, pord_xa): Ty<X, A>,
    (yb, pord_yb): Ty<Y, B>,
    hom: Hom<X, Y>,
) -> Ty<Imply<X, Y>, Imply<A, B>> {
    let pord = pord_xa.clone().imply(pord_yb.clone());
    let xy_ab = Rc::new(move |xy| {
        let q_xy = hom(xy);
        let psem = assume();
        let q_ab = psem(((q_xy, (pord_xa.clone(), pord_yb.clone())), (xa.clone(), yb.clone())));
        quality::to_eq(q_ab).0
    });
    (xy_ab, pord)
}

/// `(x : a) ⋀ (y : b) ⋀ eqq(x, y)  =>  ((x => y) : (a => b))`.
pub fn eqq_imply<X: DProp, Y: DProp, A: Prop, B: Prop>(
    (xa, pord_xa): Ty<X, A>,
    (yb, pord_yb): Ty<Y, B>,
    eqq_xy: EqQ<X, Y>,
) -> Ty<Imply<X, Y>, Imply<A, B>> {
    let pord = pord_xa.clone().imply(pord_yb.clone());
    let xy_ab: Imply<Imply<X, Y>, Imply<A, B>> = match (X::decide(), Y::decide()) {
        (Left(x), _) => Rc::new(move |xy| yb(xy(x.clone())).map_any()),
        (_, Left(y)) => {
            let ab: Imply<A, B> = yb(y).map_any();
            ab.map_any()
        }
        (Right(nx), Right(ny)) => {
            let eq_xy: Eq<X, Y> = eq::rev_modus_tollens(and::to_eq_pos((ny, nx)));
            let q_xy = eqq_xy(eq_xy);
            let q_ab = assume()(((q_xy, (pord_xa, pord_yb)), (xa, yb)));
            let ab = quality::to_eq(q_ab).0;
            ab.map_any()
        }
    };
    (xy_ab, pord)
}

/// `(a : (b ⋁ c)) ⋀ a  =>  (a : b) ⋁ (a : c)`.
pub fn or_split<A: Prop, B: Prop, C: Prop>(
    (ty_a, pord): Ty<A, Or<B, C>>,
    a: A
) -> Or<Ty<A, B>, Ty<A, C>> {
    match ty_a(a) {
        Left(b) => Left((b.map_any(), pord.or_left())),
        Right(c) => Right((c.map_any(), pord.or_right()))
    }
}

/// `(a : (b ⋁ c))  =>  (a : b) ⋁ (a : c)`.
pub fn or_split_da<A: DProp, B: Prop, C: Prop>(
    (ty_a_or_b_c, pord): Ty<A, Or<B, C>>
) -> Or<Ty<A, B>, Ty<A, C>> {
    match imply::or_split_da(ty_a_or_b_c) {
        Left(ty_a_b) => Left((ty_a_b, pord.or_left())),
        Right(ty_a_c) => Right((ty_a_c, pord.or_right()))
    }
}

/// `(a : (b ⋁ c))  =>  (a : b) ⋁ (a : c)`.
pub fn or_split_db<A: Prop, B: DProp, C: Prop>(
    (ty_a_or_b_c, pord): Ty<A, Or<B, C>>
) -> Or<Ty<A, B>, Ty<A, C>> {
    match imply::or_split_db(ty_a_or_b_c) {
        Left(ty_a_b) => Left((ty_a_b, pord.or_left())),
        Right(ty_a_c) => Right((ty_a_c, pord.or_right()))
    }
}

/// `(a : (b ⋁ c))  =>  (a : b) ⋁ (a : c)`.
pub fn or_split_dc<A: Prop, B: Prop, C: DProp>(
    (ty_a_or_b_c, pord): Ty<A, Or<B, C>>
) -> Or<Ty<A, B>, Ty<A, C>> {
    match imply::or_split_dc(ty_a_or_b_c) {
        Left(ty_a_b) => Left((ty_a_b, pord.or_left())),
        Right(ty_a_c) => Right((ty_a_c, pord.or_right()))
    }
}

/// `(a : T) ⋀ (b : U)  =>  ((a ~~ b) : (T ~~ U))`.
pub fn q_formation<A: Prop, B: Prop, T: Prop, U: Prop>(
    (a_t, pord_a_t): Ty<A, T>,
    (b_u, pord_b_u): Ty<B, U>,
) -> Ty<Q<A, B>, Q<T, U>> {
    let pord_a_t_2 = pord_a_t.clone();
    let pord_b_u_2 = pord_b_u.clone();
    (Rc::new(move |q_ab| {
        let p = assume();
        p(((q_ab, (pord_a_t_2.clone(), pord_b_u_2.clone())), (a_t.clone(), b_u.clone())))
    }), {
        pord_a_t.q(pord_b_u)
    })
}

/// `(a : T)  =>  (~a : ~T)`.
pub fn qu_formation<A: Prop, T: Prop>((a_t, pord_a_t): Ty<A, T>) -> Ty<Qu<A>, Qu<T>> {
    let pord_a_t_2 = pord_a_t.clone();
    (Rc::new(move |qu_ab| {
        Qu::from_q(assume()(((Qu::to_q(qu_ab), (pord_a_t_2.clone(), pord_a_t_2.clone())),
            (a_t.clone(), a_t.clone()))))
    }), {
        pord_a_t.qu()
    })
}

/// `(a : T) ⋀ (b : U) ⋀ ¬(T == U)  =>  ¬(a ~~ b)`.
pub fn neq_to_sesh<A: Prop, B: Prop, T: Prop, U: Prop>(
    ty_a: Ty<A, T>,
    ty_b: Ty<B, U>,
    neq_tu: Not<Eq<T, U>>,
) -> Not<Q<A, B>> {
    imply::modus_tollens(q_formation(ty_a, ty_b).0)(quality::neq_to_sesh(neq_tu))
}

/// `(a : T) ⋀ (a : U) ⋀ ¬(T == U)  =>  ¬~a`.
pub fn neq_to_not_qu<A: Prop, T: Prop, U: Prop>(
    ty_a_t: Ty<A, T>,
    ty_a_u: Ty<A, U>,
    neq_t_u: Not<Eq<T, U>>
) -> Not<Qu<A>> {imply::in_left(neq_to_sesh(ty_a_t, ty_a_u, neq_t_u), Qu::to_q)}

/// `(a : b) ⋀ (b : c) => (a : c)`.
pub fn transitivity<A: Prop, B: Prop, C: Prop>(
    (ab, pord_ab): Ty<A, B>,
    (bc, pord_bc): Ty<B, C>
) -> Ty<A, C> {
    (imply::transitivity(ab, bc), pord_ab.transitivity(pord_bc))
}

/// `(a : x) => (a : (a : x))`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [POrdProof::by_imply_right].
pub unsafe fn lift<A: Prop, X: Prop>(ty_a: Ty<A, X>) -> Ty<A, Ty<A, X>> {
    let pord1 = unsafe {ty_a.1.clone().by_imply_right(Rc::new(|x| x.map_any()))};
    let pord2 = unsafe {ty_a.1.clone().by_imply_right(ty_a.1.clone().map_any())};
    (ty_a.map_any(), pord1.merge_right(pord2))
}

/// `(a : (a : x)) => (a : x)`.
///
/// # Safety
///
/// This theorem is unsafe due to use of [POrdProof::by_imply_right].
pub unsafe fn lower<A: Prop, X: Prop>((a_ty_a, pord_a_ty_a): Ty<A, Ty<A, X>>) -> Ty<A, X> {
    let ax = imply::reduce(Rc::new(move |a| a_ty_a(a).0));
    let x: POrdProof<A, Imply<A, X>> = unsafe {pord_a_ty_a.by_imply_right(ax.clone().map_any())};
    (ax, x.imply_reduce())
}
