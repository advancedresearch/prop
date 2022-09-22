//! # Type Theoretic Existential Philosophy
//!
//! When reasoning about existence in existential philosophy,
//! one can not assume that one's own existence is of the
//! form of a universal existence.
//!
//! The logical nature of existence is unknown.
//!
//! See this [blog post](https://advancedresearch.github.io/blog/2022-02-16-lets-abandon-the-cogito-and-use-type-theory-instead)
//! for more information.
//!
//! However, one can make a weaker assumption `¬¬a ⋁ ¬a`,
//! which is that either one has a negative negative existence,
//! or one has a negative existence.
//! This assumption is called "Excluded Middle of Non-Existence".
//!
//! Descartes' "I think, therefore I am." might be thought of as
//! "I think, therefore I don't non-exist." in this logic.
//!
//! This logic is abbreviated EP (normal) or EPS (path semantical).
//! One property of these logics is that De Morgan's laws hold,
//! even though the excluded middle is not assumed.
//!
//! It means that it can be absurd if I do not exist,
//! or I might not exist, but I have no proof that I exist or not exist.
//!
//! The reason `¬¬a ⋁ ¬a` is used, is to investigate
//! existential philosophy without assuming that the logical nature of existence
//! has something like the excluded middle,
//! yet still allow some reasoning that does not hold in ordinary constructive logic.
//!
//! To assume an existential proposition, use the `EProp` trait.
//!
//! The excluded middle implies an existential proposition.
//! Therefore, a decidable proposition `DProp` automatically implementes `EProp`.

use crate::*;

/// Shorthand for `¬¬x`.
pub type NN<X> = Not<Not<X>>;
/// `∀ x { ¬¬x ⋁ ¬x }`.
pub type E<X> = Or<NN<X>, Not<X>>;
/// `¬¬a == ¬¬b`.
pub type EqNN<A, B> = Eq<NN<A>, NN<B>>;
/// `a =x= b`, defined as `(a => ¬¬b) ⋀ (b => ¬¬a)`.
pub type CrossEq<A, B> = And<Imply<A, NN<B>>, Imply<B, NN<A>>>;
/// A Catuṣkoṭi that uses cross equality in excluded middle relation.
pub type CrossCatus<A, B> = CrossEq<ExcM<A>, Not<ExcM<B>>>;

/// Implemented by existential types.
pub trait Existential: Prop {
    /// Get existential rule.
    fn e() -> E<Self>;
}

impl<T: Decidable> Existential for T {
    fn e() -> E<Self> {
        match Self::decide() {
            Left(a) => Left(not::double(a)),
            Right(na) => Right(na),
        }
    }
}

/// Shorthand for existential proposition.
pub trait EProp: Existential {}
impl<T: Existential> EProp for T {}

/// `¬¬(¬¬x ⋁ ¬x)`.
pub fn double_neg_e<A: Prop>() -> NN<E<A>> {
    Rc::new(move |nexcm| {
        let nexcm2 = nexcm.clone();
        let nnna = Rc::new(move |a| nexcm2(Left(a)));
        let nna = Rc::new(move |na| nexcm(Right(na)));
        not::absurd(nnna, nna)
    })
}

/// `(a ∨ ¬a) => (¬¬a ∨ ¬a)`.
pub fn excm_to_e<A: Prop>(excm: ExcM<A>) -> E<A> {
    match excm {
        Left(a) => Left(not::double(a)),
        Right(na) => Right(na),
    }
}

/// `(¬¬a ∨ ¬a) => (¬¬¬a ∨ ¬¬a)`.
pub fn en<A: Prop>(en: E<A>) -> E<Not<A>> {
    match en {
        Left(nna) => Right(nna),
        Right(na) => Left(not::double(na)),
    }
}

/// `(¬¬¬a ∨ ¬¬a) => (¬¬a ∨ ¬a)`.
pub fn rev_en<A: Prop>(en: E<Not<A>>) -> E<A> {
    match en {
        Left(nnna) => Right(not::rev_triple(nnna)),
        Right(nna) => Left(nna),
    }
}

/// `¬(¬¬a ∧ ¬¬b) => (¬a ∨ ¬b)`.
pub fn or_from_de_morgan<A: EProp, B: EProp>(
    p: Not<And<NN<A>, NN<B>>>
) -> Or<Not<A>, Not<B>> {
    match (A::e(), B::e()) {
        (Left(nna), Left(nnb)) => not::absurd(p, (nna, nnb)),
        (Right(na), _) => Left(na),
        (_, Right(nb)) => Right(nb),
    }
}

/// `(a == b) => (a =x= b)`.
pub fn eq_to_crosseq<A: Prop, B: Prop>(
    f: Eq<A, B>
) -> CrossEq<A, B> {
    eqnn_to_crosseq(eq::modus_tollens(eq::modus_tollens(f)))
}

/// `(a =x= b) => (¬a == ¬b)`.
pub fn crosseq_to_eqn<A: Prop, B: Prop>(
    (a_nnb, b_nna): CrossEq<A, B>
) -> Eq<Not<A>, Not<B>> {
    (
        Rc::new(move |na| imply::modus_tollens(b_nna.clone())(not::double(na))),
        Rc::new(move |nb| imply::modus_tollens(a_nnb.clone())(not::double(nb))),
    )
}

/// `(a =x= b) => (¬¬a == ¬¬b)`.
pub fn crosseq_to_eqnn<A: Prop, B: Prop>(cross_eq: CrossEq<A, B>) -> EqNN<A, B> {
    eq::symmetry(eq::modus_tollens(crosseq_to_eqn(cross_eq)))
}

/// `(¬¬a == ¬¬b) => (a =x= b)`.
pub fn eqnn_to_crosseq<A: Prop, B: Prop>(eq: EqNN<A, B>) -> CrossEq<A, B> {
    let eq2 = eq.clone();
    (
        Rc::new(move |a| eq.0(not::double(a))),
        Rc::new(move |b| eq2.1(not::double(b))),
    )
}

/// `(¬a == ¬b) => (a =x= b)`.
pub fn eqn_to_crosseq<A: Prop, B: Prop>(eq: Eq<Not<A>, Not<B>>) -> CrossEq<A, B> {
    eqnn_to_crosseq(eq::symmetry(eq::modus_tollens(eq)))
}

/// `(a =x= b) => ((¬¬a ∨ ¬a) == (¬¬b ∨ ¬b))`.
pub fn crosseq_to_eqe<A: Prop, B: Prop>(cross_eq: CrossEq<A, B>) -> Eq<E<A>, E<B>> {
    let (eqnn0, eqnn1) = crosseq_to_eqnn(cross_eq.clone());
    let (eqn0, eqn1) = crosseq_to_eqn(cross_eq.clone());
    (
        Rc::new(move |ea| {
            match ea {
                Left(nna) => Left(eqnn0(nna)),
                Right(na) => Right(eqn0(na)),
            }
        }),
        Rc::new(move |eb| {
            match eb {
                Left(nnb) => Left(eqnn1(nnb)),
                Right(nb) => Right(eqn1(nb)),
            }
        })
    )
}

/// `(¬a =x= b) => ((¬¬a ∨ ¬a) == (¬¬b ∨ ¬b))`.
pub fn crosseq_adj_to_eqe<A: Prop, B: Prop>(cross_eq: CrossEq<Not<A>, B>) -> Eq<E<A>, E<B>> {
    let eq_en_e: Eq<E<Not<A>>, E<A>> = (Rc::new(move |en| rev_en(en)), Rc::new(move |e| en(e)));
    eq::in_left_arg(crosseq_to_eqe(cross_eq), eq_en_e)
}

/// `(¬a =x= b) => ¬(a =x= b)`.
pub fn crosseq_adj_to_ncrosseq<A: Prop, B: Prop>(
    f: CrossEq<Not<A>, B>
) -> Not<CrossEq<A, B>> {
    Rc::new(move |cross_eq| {
        let g: EqNN<B, A> = eq::symmetry(crosseq_to_eqnn(cross_eq));
        let g2: EqNN<Not<A>, B> = crosseq_to_eqnn(f.clone());
        eq::anti(eq::symmetry(eq::in_right_arg(g2, g)))
    })
}

/// `((¬¬a ∨ ¬a) ⋀ (¬¬b ∨ ¬b)) => ((a =x= b) ⋁ (¬a =x= b))`.
pub fn and_ea_eb_to_or_crosseq<A: Prop, B: Prop>(
    ea: E<A>,
    eb: E<B>
) -> Or<CrossEq<A, B>, CrossEq<Not<A>, B>> {
    match (ea, eb) {
        (Left(nna), Left(nnb)) =>
            Left(eqnn_to_crosseq(and::to_eq_pos((nna, nnb)))),
        (Right(na), Right(nb)) =>
            Left(eqn_to_crosseq(and::to_eq_pos((na, nb)))),
        (Left(nna), Right(nb)) =>
            Right(eqn_to_crosseq(and::to_eq_pos((nna, nb)))),
        (Right(na), Left(nnb)) =>
            Right(rev_crosseq_adjoint(eqn_to_crosseq(and::to_eq_pos((na, nnb))))),
    }
}

/// `((¬¬a ∨ ¬a) ⋀ (¬¬b ∨ ¬b)) => ((a =x= b) ⋁ ¬(a =x= b))`.
pub fn and_ea_eb_to_excm_crosseq<A: Prop, B: Prop>(
    ea: E<A>,
    eb: E<B>
) -> ExcM<CrossEq<A, B>> {
    match and_ea_eb_to_or_crosseq(ea, eb) {
        Left(x) => Left(x),
        Right(y) => Right(crosseq_adj_to_ncrosseq(y)),
    }
}

/// `a =x= a`.
pub fn crosseq_refl<A: Prop>() -> CrossEq<A, A> {
    let a_nna = Rc::new(move |a| not::double(a));
    (a_nna.clone(), a_nna)
}

/// `(a =x= b) => (b =x= a)`.
pub fn crosseq_symmetry<A: Prop, B: Prop>(
    cross_eq: CrossEq<A, B>
) -> CrossEq<B, A> {
    and::symmetry(cross_eq)
}

/// `(a =x= b) ⋀ (b =x= c) => (a =x= c)`.
pub fn crosseq_transitivity<A: Prop, B: Prop, C: Prop>(
    ab: CrossEq<A, B>,
    bc: CrossEq<B, C>,
) -> CrossEq<A, C> {
    eqnn_to_crosseq(eq::transitivity(crosseq_to_eqnn(ab), crosseq_to_eqnn(bc)))
}

/// `(¬a =x= b) => (a =x= ¬b)`.
pub fn crosseq_adjoint<A: Prop, B: Prop>(
    f: CrossEq<Not<A>, B>
) -> CrossEq<A, Not<B>> {
    let g: EqNN<Not<A>, B> = crosseq_to_eqnn(f);
    let g2: EqNN<Not<B>, NN<A>> = eq::modus_tollens(g);
    let g3: Eq<NN<NN<A>>, NN<A>> = (
        Rc::new(move |nnnna| not::rev_triple(nnnna)),
        Rc::new(move |nna| not::double(nna))
    );
    let g4: EqNN<Not<B>, A> = eq::in_right_arg(g2, g3);
    crosseq_symmetry(eqnn_to_crosseq(g4))
}

/// `(a =x= ¬b) => (¬a =x= b)`.
pub fn rev_crosseq_adjoint<A: Prop, B: Prop>(
    f: CrossEq<A, Not<B>>
) -> CrossEq<Not<A>, B> {
    crosseq_symmetry(crosseq_adjoint(crosseq_symmetry(f)))
}

/// Proves that any Catuṣkoṭi with relative excluded middle is absurd.
///
/// A Catuṣkoṭi is a 4-value logic.
/// For more information, see https://en.wikipedia.org/wiki/Catu%E1%B9%A3ko%E1%B9%ADi
pub fn catuskoti_excm_absurd<A: Prop, B: Prop>(
    catus: Not<Eq<ExcM<A>, ExcM<B>>>
) -> False {
    let catus2 = catus.clone();
    let a_nexcm_b: Imply<A, Not<ExcM<B>>> =
        Rc::new(move |a| {
            let catus2 = catus2.clone();
            Rc::new(move |excm_b| {
                let eq = (excm_b.map_any(), Left(a.clone()).map_any());
                catus2.clone()(eq)
            })
        });
    let catus2 = catus.clone();
    let na_nexcm_b: Imply<Not<A>, Not<ExcM<B>>> =
        Rc::new(move |na| {
            let catus2 = catus2.clone();
            Rc::new(move |excm_b| {
                let eq = (excm_b.map_any(), Right(na.clone()).map_any());
                catus2.clone()(eq)
            })
        });
    let a_nexcm_b2 = a_nexcm_b.clone();
    let a_nb: Imply<A, Not<B>> =
        Rc::new(move |a| {
            let nexcm_b = a_nexcm_b2(a);
            Rc::new(move |b| nexcm_b(Left(b)))
        });
    let a_nnb: Imply<A, Not<Not<B>>> =
        Rc::new(move |a| {
            let nexcm_b = a_nexcm_b(a);
            Rc::new(move |nb| nexcm_b(Right(nb)))
        });
    let na: Not<A> = Rc::new(move |a| a_nnb(a.clone())(a_nb(a)));
    let na2 = na.clone();
    let nb: Not<B> = Rc::new(move |b| na_nexcm_b(na2.clone())(Left(b)));
    let eq: Eq<ExcM<A>, ExcM<B>> = (Right(nb).map_any(), Right(na).map_any());
    catus(eq)
}

/// Proves that any Catuṣkoṭi with relative excluded middle of non-existence is absurd.
///
/// A Catuṣkoṭi is a 4-value logic.
/// For more information, see https://en.wikipedia.org/wiki/Catu%E1%B9%A3ko%E1%B9%ADi
pub fn catuskoti_e_absurd<A: Prop, B: Prop>(
    catus: Not<Eq<E<A>, E<B>>>
) -> False {
    let catus2 = catus.clone();
    let a_ne_b: Imply<A, Not<E<B>>> =
        Rc::new(move |a| {
            let catus2 = catus2.clone();
            Rc::new(move |e_b| {
                let eq = (e_b.map_any(), Left(not::double(a.clone())).map_any());
                catus2.clone()(eq)
            })
        });
    let catus2 = catus.clone();
    let na_ne_b: Imply<Not<A>, Not<E<B>>> =
        Rc::new(move |na| {
            let catus2 = catus2.clone();
            Rc::new(move |e_b| {
                let eq = (e_b.map_any(), Right(na.clone()).map_any());
                catus2.clone()(eq)
            })
        });
    let a_ne_b2 = a_ne_b.clone();
    let a_nb: Imply<A, Not<B>> =
        Rc::new(move |a| {
            let ne_b = a_ne_b2(a);
            Rc::new(move |b| ne_b(Left(not::double(b))))
        });
    let a_nnb: Imply<A, Not<Not<B>>> =
        Rc::new(move |a| {
            let ne_b = a_ne_b(a);
            Rc::new(move |nb| ne_b(Right(nb)))
        });
    let na: Not<A> = Rc::new(move |a| a_nnb(a.clone())(a_nb(a)));
    let na2 = na.clone();
    let nb: Not<B> = Rc::new(move |b| na_ne_b(na2.clone())(Left(not::double(b))));
    let eq: Eq<E<A>, E<B>> = (Right(nb).map_any(), Right(na).map_any());
    catus(eq)
}

/// Implemented by Catuṣkoṭi expressions.
pub trait Catuskoti<A: Prop, B: Prop>: Prop {
    /// A Catuṣkoṭi can not relate excluded middles with `eq`.
    fn not_eq() -> Not<Eq<Self, Eq<ExcM<A>, ExcM<B>>>>;
    /// A Catuṣkoṭi can not relate excluded middles with `or`.
    fn not_or() -> Not<Eq<Self, Or<ExcM<A>, ExcM<B>>>>;
    /// Get excluded corners from `a`.
    fn exc_a(self, a: A) -> Not<Or<Not<A>, ExcM<B>>>;
    /// Get excluded corners from `¬a`.
    fn exc_na(self, na: Not<A>) -> Not<Or<A, ExcM<B>>>;
    /// Get excluded corners from `b`.
    fn exc_b(self, b: B) -> Not<Or<ExcM<A>, Not<B>>>;
    /// Get excluded corners from `¬b`.
    fn exc_nb(self, nb: Not<B>) -> Not<Or<ExcM<A>, B>>;

    /// Proves that excluded middle of `a` makes `b` nonsense.
    fn excm_a_nexcm_b(self, excm_a: ExcM<A>) -> Not<ExcM<B>> {
        Rc::new(move |excm_b: ExcM<B>| {
            let neq = Self::not_eq();
            let eq_excm_a_excm_b = (excm_b.map_any(), excm_a.clone().map_any());
            let neq_excm = eq::contra_excm(
                neq,
                self.clone(),
                Left(eq_excm_a_excm_b.clone()),
            );
            neq_excm(eq_excm_a_excm_b)
        })
    }

    /// Proves that excluded middle of `b` makes `b` nonsense.
    fn excm_b_nexcm_a(self, excm_b: ExcM<B>) -> Not<ExcM<A>> {
        let f: Imply<ExcM<A>, Not<ExcM<B>>> = Rc::new(move |excm_a| self.clone().excm_a_nexcm_b(excm_a));
        imply::flip_neg_right(f)(excm_b)
    }

    /// Proves that none of the four corners make sense,
    /// when the excluded middles are equal.
    fn eq_excm_outside(self, eq: Eq<ExcM<A>, ExcM<B>>) -> And<Not<ExcM<A>>, Not<ExcM<B>>> {
        let self2 = self.clone();
        let eq2 = eq.clone();
        let nexcm_a: Not<ExcM<A>> = Rc::new(move |excm_a| {
            let excm_b = eq2.0(excm_a.clone());
            self2.clone().excm_a_nexcm_b(excm_a)(excm_b)
        });
        let nexcm_b: Not<ExcM<B>> = Rc::new(move |excm_b| {
            let excm_a = eq.1(excm_b.clone());
            self.clone().excm_b_nexcm_a(excm_b)(excm_a)
        });
        (nexcm_a, nexcm_b)
    }

    /// Proves that none of the four corners makes sense,
    /// when the equality relation of excluded middle is decidable.
    fn excm_eq_excm_outside(
        self,
        excm_eq: ExcM<Eq<ExcM<A>, ExcM<B>>>
    ) -> And<Not<ExcM<A>>, Not<ExcM<B>>> {
        match excm_eq {
            Left(eq) => self.eq_excm_outside(eq),
            Right(neq) => imply::absurd()(existence::catuskoti_excm_absurd(neq)),
        }
    }

    /// Proves excluded middle of `b` from excluded middle of `a`.
    fn excm_a_excm_b(self, excm_a: ExcM<A>) -> ExcM<B> {
        Right(Rc::new(move |b: B| {
            let exc_b: Not<Or<ExcM<A>, Not<B>>> = self.clone().exc_b(b);
            exc_b(Left(excm_a.clone()))
        }))
    }

    /// Proves excluded middle of `a` from excluded middle of `b`.
    fn excm_b_excm_a(self, excm_b: ExcM<B>) -> ExcM<A> {
        Right(Rc::new(move |a: A| {
            let exc_a: Not<Or<Not<A>, ExcM<B>>> = self.clone().exc_a(a);
            exc_a(Right(excm_b.clone()))
        }))
    }

    /// Proves `false` from excluded middle of `a`.
    fn excm_a_absurd(self, excm_a: ExcM<A>) -> False {
        self.clone().excm_a_nexcm_b(excm_a.clone())(self.excm_a_excm_b(excm_a))
    }

    /// Proves `false` from excluded middle of `b`.
    fn excm_b_absurd(self, excm_b: ExcM<B>) -> False {
        self.clone().excm_b_nexcm_a(excm_b.clone())(self.excm_b_excm_a(excm_b))
    }

    /// Proves `false` from `self` and `or` in relation of excluded middle.
    fn or_excm_absurd(self, or: Or<ExcM<A>, ExcM<B>>) -> False {
        match or {
            Left(excm_a) => self.excm_a_absurd(excm_a),
            Right(excm_b) => self.excm_b_absurd(excm_b),
        }
    }

    /// Proves `false` from `self` and `self` implying `or` in relation of excluded middle.
    fn self_or_absurd(self, self_or: Imply<Self, Or<ExcM<A>, ExcM<B>>>) -> False {
        self.clone().or_excm_absurd(self_or(self))
    }
}

impl<A: Prop, B: Prop> Catuskoti<A, B> for CrossCatus<A, B> {
    fn not_eq() -> Not<Eq<Self, Eq<ExcM<A>, ExcM<B>>>> {
        Rc::new(move |eq| {
            let eq2 = eq::modus_tollens(eq::modus_tollens(eq.clone()));
            let nnself = eq2.1(Rc::new(move |catus| existence::catuskoti_excm_absurd(catus)));
            nnself(Rc::new(move |s: Self| {
                let eq_excm: Eq<ExcM<A>, ExcM<B>> = eq.0(s.clone());
                let s2 = s.clone();
                let eq_excm2 = eq_excm.clone();
                let excm_b = eq_excm.clone().0(Right(Rc::new(move |a| {
                    let nexcm_b: Not<ExcM<B>> = not::rev_triple(s2.0(Left(a.clone())));
                    let excm_b = eq_excm2.0(Left(a));
                    nexcm_b(excm_b)
                })));
                let excm_a = eq_excm.1(excm_b.clone());
                let nexcm_b = not::rev_triple(s.0(excm_a));
                nexcm_b(excm_b)
            }))
        })
    }
    fn not_or() -> Not<Eq<Self, Or<ExcM<A>, ExcM<B>>>> {
        Rc::new(move |eq| {
            let eq2 = eq.clone();
            let s: Self = eq.clone().1(Left(Right(Rc::new(move |a| {
                let s: Self = eq2.1(Left(Left(a.clone())));
                s.excm_a_absurd(Left(a))
            }))));

            let or = eq.0(s.clone());
            match or {
                Left(excm_a) => s.excm_a_absurd(excm_a),
                Right(excm_b) => s.excm_b_absurd(excm_b),
            }
        })
    }
    fn exc_a(self, a: A) -> Not<Or<Not<A>, ExcM<B>>> {
        let nexcm_b = not::rev_triple(self.0(Left(a.clone())));
        Rc::new(move |or| {
            match or {
                Left(na) => na(a.clone()),
                Right(excm_b) => nexcm_b.clone()(excm_b),
            }
        })
    }
    fn exc_na(self, na: Not<A>) -> Not<Or<A, ExcM<B>>> {
        let nexcm_b = not::rev_triple(self.0(Right(na.clone())));
        Rc::new(move |or| {
            match or {
                Left(a) => na.clone()(a),
                Right(excm_b) => nexcm_b.clone()(excm_b),
            }
        })
    }
    fn exc_b(self, b: B) -> Not<Or<ExcM<A>, Not<B>>> {
        Rc::new(move |or| {
            match or {
                Left(excm_a) => not::rev_triple(self.0(excm_a))(Left(b.clone())),
                Right(nb) => nb(b.clone()),
            }
        })
    }
    fn exc_nb(self, nb: Not<B>) -> Not<Or<ExcM<A>, B>> {
        Rc::new(move |or| {
            match or {
                Left(excm_a) => not::rev_triple(self.0(excm_a))(Right(nb.clone())),
                Right(b) => nb.clone()(b),
            }
        })
    }
}
