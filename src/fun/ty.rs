use super::*;

/// Cumulative type hierarchy.
#[derive(Copy, Clone)]
pub struct Type<N>(N);

impl<N: 'static + Clone> path_semantics::LProp for Type<N> {
    type N = N;
    type SetLevel<T: 'static + Clone> = Type<T>;
}

/// `type(n) => type(n+1)`.
pub fn type_imply<N: Nat>(Type(n): Type<N>) -> Type<S<N>> {Type(S(n))}
/// `is_const(type(n))`.
pub fn type_is_const<N: Nat>() -> IsConst<Type<N>> {unimplemented!()}
/// `(a : x) ⋀ (b : y)  =>  (a -> b) : (x -> y)`.
pub fn fun_ty<A: Prop, B: Prop, X: Prop, Y: Prop>(
    _: Ty<A, X>,
    _: Ty<B, Y>
) -> Ty<Pow<B, A>, Pow<Y, X>> {unimplemented!()}
/// `(type(n) -> type(m)) : type(0)`.
pub fn fun_type_ty<N: Nat, M: Nat>() -> Ty<Pow<Type<M>, Type<N>>, Type<Z>> {unimplemented!()}
/// `(b : type(n))  =>  (a : b) : type(n)`.
pub fn judgement_ty<A: Prop, B: Prop, N: Nat>(_ty_b: Ty<B, Type<N>>) -> Ty<Ty<A, B>, Type<N>> {
    unimplemented!()
}

/// `type(n) : type(n+1)`.
pub fn type_ty<N: Nat>() -> Ty<Type<N>, Type<S<N>>> {
    (hooo::pow_to_imply(type_imply), POrdProof::new())
}
/// `(a : type(n)) ⋀ (b : type(m))  =>  (a -> b) : type(0)`.
pub fn fun_type0<A: Prop, B: Prop, N: Nat, M: Nat>(
    ty_a: Ty<A, Type<N>>,
    ty_b: Ty<B, Type<M>>
) -> Ty<Pow<B, A>, Type<Z>> {path_semantics::ty_transitivity(fun_ty(ty_a, ty_b), fun_type_ty())}
/// `(f : A -> B) ⋀ (inv(f) ~~ g) => ((f ~~ g) : ((A -> B) ~~ (B -> A)))`.
pub fn q_inv_ty<F: Prop, G: Prop, A: Prop, B: Prop>(
    ty_f: Ty<F, Pow<B, A>>,
    q: Q<Inv<F>, G>,
) -> Ty<Q<F, G>, Q<Pow<B, A>, Pow<A, B>>> {
    use quality::transitivity as trans;

    let y = self_inv_ty(ty_f);
    let q2 = q.clone();
    let x: Eq<Q<F, Inv<F>>, Q<F, G>> = (
        Rc::new(move |x| trans(x, q2.clone())),
        Rc::new(move |x| trans(x, quality::symmetry(q.clone())))
    );
    path_semantics::ty_in_left_arg(y, x)
}
