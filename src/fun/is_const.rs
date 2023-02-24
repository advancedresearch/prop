use super::*;

/// Whether some symbol is a constant.
///
/// When a symbol `x` is a constant, `x[a := b] == x` (invariant under substitution).
#[derive(Copy, Clone)]
pub struct IsConst<A>(A);

/// A proof that some symbol is not a constant.
///
/// This is used to prevent collapse of propositions into constants,
/// e.g. when doing a proof by induction.
pub type IsVar<A> = Not<IsConst<A>>;

/// Implemented by variable propositions.
pub trait VProp: Prop {
    /// Constructs a proof that the proposition is variable.
    fn is_var() -> IsVar<Self>;
}

/// `is_const(a) ⋀ is_const(b)  =>  is_const((a, b))`.
pub fn const_tup<A: Prop, B: Prop>(a: IsConst<A>, b: IsConst<B>) -> IsConst<Tup<A, B>> {
    tup_is_const(a, b)
}
/// `is_const((a, b))  =>  is_const(a) ⋀ is_const(b)`.
pub fn tup_const<A: Prop, B: Prop>(_x: IsConst<Tup<A, B>>) -> And<IsConst<A>, IsConst<B>> {
    unimplemented!()
}
/// `(a == b)  =>  (is_const(a) == is_const(b))`.
///
/// This is an axiom since it accesses the inner value, which is not sound as a theorem.
pub fn const_eq<A: Prop, B: Prop>((ab, ba): Eq<A, B>) -> Eq<IsConst<A>, IsConst<B>> {
    (Rc::new(move |a| IsConst(ab(a.0))), Rc::new(move |b| IsConst(ba(b.0))))
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(a ⋀ b)`.
pub fn and_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<And<A, B>> {
    unimplemented!()
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(a ⋁ b)`.
pub fn or_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<Or<A, B>> {
    unimplemented!()
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(a => b)`.
pub fn imply_is_const<A: Prop, B: Prop>(_a: IsConst<A>, _b: IsConst<B>) -> IsConst<Imply<A, B>> {
    unimplemented!()
}
/// `is_const(a) ⋀ is_const(b)  =>  is_const(pord(a, b))`.
pub fn pord_is_const<A: Prop, B: Prop>(
    _a: IsConst<A>,
    _b: IsConst<B>
) -> IsConst<POrdProof<A, B>> {
    unimplemented!()
}

/// `is_const(a) ⋀ is_const(b)  =>  is_const(a : b)`.
pub fn ty_is_const<A: Prop, B: Prop>(a: IsConst<A>, b: IsConst<B>) -> IsConst<Ty<A, B>> {
    and_is_const(imply_is_const(a.clone(), b.clone()), pord_is_const(a, b))
}

/// `is_const(a) ⋀ (a == b)  =>  is_const(b)`.
pub fn const_in_arg<A: Prop, B: Prop>(a: IsConst<A>, x: Eq<A, B>) -> IsConst<B> {
    const_eq(x).0(a)
}
