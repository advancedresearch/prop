use super::*;

/// Models a type relation `a : t`.
pub type Ty<A, T> = And<Imply<A, T>, POrdProof<A, T>>;

/// `x : ltrue`.
pub fn ty_ltrue<X: LProp>() -> Ty<X, LTrue<S<X::N>>>
    where X::N: Lt<S<X::N>> + Default
{
    (LTrue(Default::default()).map_any(), POrdProof::default())
}

/// `(a : b) ⋀ (a == c)  =>  (c : b)`.
pub fn ty_in_left_arg<A: Prop, B: Prop, C: Prop>((ab, pord): Ty<A, B>, eq: Eq<A, C>) -> Ty<C, B> {
    (imply::in_left_arg(ab, eq.clone()), pord.by_eq_left(eq))
}

/// `(a : b) ⋀ (b == c)  =>  (a : c)`.
pub fn ty_in_right_arg<A: Prop, B: Prop, C: Prop>((ab, pord): Ty<A, B>, eq: Eq<B, C>) -> Ty<A, C> {
    (imply::in_right_arg(ab, eq.clone()), pord.by_eq_right(eq))
}

/// `(a == b)  =>  (a : c) == (b : c)`.
pub fn ty_eq_left<A: Prop, B: Prop, C: Prop>(x: Eq<A, B>) -> Eq<Ty<A, C>, Ty<B, C>> {
    let x2 = eq::symmetry(x.clone());
    (Rc::new(move |ty_a| ty_in_left_arg(ty_a, x.clone())),
     Rc::new(move |ty_b| ty_in_left_arg(ty_b, x2.clone())))
}

/// `(x : false) => ¬x`.
pub fn ty_false<X: Prop>(ty_x_false: Ty<X, False>) -> Not<X> {ty_x_false.0}

/// `(true : x) => x`.
pub fn ty_true<X: Prop>(ty_true_x: Ty<True, X>) -> X {ty_true_x.0(True)}

/// `a => (true : a)`.
pub fn ty_rev_true<A: Prop>(a: A) -> Ty<True, A> {
    ty_in_right_arg(ty_true_true(), (a.map_any(), True.map_any()))
}

/// `(a : x) ⋀ a => (true : x)`.
pub fn ty_triv<A: Prop, X: Prop>(ty_a_x: Ty<A, X>, a: A) -> Ty<True, X> {
    ty_in_left_arg(ty_a_x, (True.map_any(), a.map_any()))
}

/// `(x : a) ⋀ ¬a => (x : false)`.
pub fn ty_non_triv<X: Prop, A: Prop>(
    ty_x_a: Ty<X, A>,
    na: Not<A>,
) -> Ty<X, False> {
    let eq_a_false: Eq<A, False> =
        (Rc::new(move |a| na(a)), Rc::new(move |fa| imply::absurd()(fa)));
    ty_in_right_arg(ty_x_a, eq_a_false)
}

/// `true == ltrue`.
pub fn eq_true_ltrue<N: Nat>() -> Eq<True, LTrue<N>> {
    (LTrue(Default::default()).map_any(), True.map_any())
}

/// `true : true`.
pub fn ty_true_true() -> Ty<True, True> {
    let x = ty_in_left_arg(ty_ltrue(), eq::symmetry(eq_true_ltrue::<Z>()));
    ty_in_right_arg(x, eq::symmetry(eq_true_ltrue::<S<Z>>()))
}

/// `(x : a) ⋀ (y : b)  =>  ((x ⋀ y) : (a ⋀ b))`.
pub fn ty_and<X: Prop, Y: Prop, A: Prop, B: Prop>(
    (xa, pord_xa): Ty<X, A>,
    (yb, pord_yb): Ty<Y, B>,
) -> Ty<And<X, Y>, And<A, B>> {
    let imply_and_xy_and_ab: Imply<And<X, Y>, And<A, B>> = Rc::new(move |(x, y)| {
        let a = xa(x);
        let b = yb(y);
        let and_ab = (a, b);
        and_ab
    });
    (imply_and_xy_and_ab, pord_xa.and(pord_yb))
}

/// `(x : a) ⋀ (y : b)  =>  ((x ⋁ y) : (a ⋁ b))`.
pub fn ty_or<X: Prop, Y: Prop, A: Prop, B: Prop>(
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
pub fn ty_hom_imply<X: Prop, Y: Prop, A: Prop, B: Prop>(
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
pub fn ty_eqq_imply<X: DProp, Y: DProp, A: Prop, B: Prop>(
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
pub fn ty_or_split<A: Prop, B: Prop, C: Prop>(
    (ty_a, pord): Ty<A, Or<B, C>>,
    a: A
) -> Or<Ty<A, B>, Ty<A, C>> {
    match ty_a(a) {
        Left(b) => Left((b.map_any(), pord.or_left())),
        Right(c) => Right((c.map_any(), pord.or_right()))
    }
}

/// `(a : (b ⋁ c))  =>  (a : b) ⋁ (a : c)`.
pub fn ty_or_split_da<A: DProp, B: Prop, C: Prop>(
    (ty_a_or_b_c, pord): Ty<A, Or<B, C>>
) -> Or<Ty<A, B>, Ty<A, C>> {
    match imply::or_split_da(ty_a_or_b_c) {
        Left(ty_a_b) => Left((ty_a_b, pord.or_left())),
        Right(ty_a_c) => Right((ty_a_c, pord.or_right()))
    }
}

/// `(a : (b ⋁ c))  =>  (a : b) ⋁ (a : c)`.
pub fn ty_or_split_db<A: Prop, B: DProp, C: Prop>(
    (ty_a_or_b_c, pord): Ty<A, Or<B, C>>
) -> Or<Ty<A, B>, Ty<A, C>> {
    match imply::or_split_db(ty_a_or_b_c) {
        Left(ty_a_b) => Left((ty_a_b, pord.or_left())),
        Right(ty_a_c) => Right((ty_a_c, pord.or_right()))
    }
}

/// `(a : (b ⋁ c))  =>  (a : b) ⋁ (a : c)`.
pub fn ty_or_split_dc<A: Prop, B: Prop, C: DProp>(
    (ty_a_or_b_c, pord): Ty<A, Or<B, C>>
) -> Or<Ty<A, B>, Ty<A, C>> {
    match imply::or_split_dc(ty_a_or_b_c) {
        Left(ty_a_b) => Left((ty_a_b, pord.or_left())),
        Right(ty_a_c) => Right((ty_a_c, pord.or_right()))
    }
}

/// `(a : T) ⋀ (b : U)  =>  ((a ~~ b) : (T ~~ U))`.
pub fn ty_q_formation<A: Prop, B: Prop, T: Prop, U: Prop>(
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

/// `(a : b) ⋀ (b : c) => (a : c)`.
pub fn ty_transitivity<A: Prop, B: Prop, C: Prop>(
    (ab, pord_ab): Ty<A, B>,
    (bc, _): Ty<B, C>
) -> Ty<A, C> {
    (imply::transitivity(ab, bc.clone()), pord_ab.by_imply_right(bc))
}
