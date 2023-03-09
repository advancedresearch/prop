//! # Path Semantics
//!
//! Path Semantics has a core axiom which is used to model mathematics.
//!
//! The core axiom does not "define" all mathematics, but functions as a natural starting point
//! to build more advanced logical frameworks that in turn model mathematics.
//!
//! A logical framework is a set of axioms that are assumed to hold univerally.
//! New frameworks must not be able to prove `false` relative to the core axiom.
//! In most of mathematics, there is no need to talk about the things that the core axiom proves.
//! For this reason, it might seem like the core axiom is obscure and irrelevant.
//!
//! However, when new logical frameworks are modelled in harmony with the core axiom,
//! there are new theorems that are provable that point to deeper insights in mathematics.
//! For this reason, the core axiom is considered relevant for high dimensional mathematics.
//!
//! Other areas, such as [Continental Philosophy](https://en.wikipedia.org/wiki/Continental_philosophy),
//! might find the core axiom relevant in many applications. This is because the core axiom is
//! about propagating a partial equivalence relation, which has no analogue in normal logic,
//! but which structure is found in philosophical thinking e.g. about symbols, symbiosis, time,
//! Platonism, Seshatism (dual-Platonism) etc. There are big portions of Continental Philosophy
//! that might benefit from a perspective of Path Semantics. One area is the distinction between
//! Analytic and Continental Philosophy, which can be studied directly since Path Semantics extends
//! normal logic in a similar way that Continental Philosophy might be seen as an extension of
//! Analytic Philosophy. Path Semantics does not fully bridge this grap,
//! but blurs the boundary between Analytic and Continental Philosophy.
//!
//! It takes years to master Path Semantics, so if you do not understand everything immediately,
//! do not panic! Think about it as a logical instrument that requires practice to perform well.
//! Path Semantics is to normal logic what quantum mechanics is to classical mechanics.
//!
//! ### About This Module
//!
//! This module formalizes the core axiom and models types as propositions.
//!
//! PSI = Path Semantical Intuitionistic Propositional Logic
//!
//! PSI is a generalization of IPL where propositions can be organized in path semantical levels.
//! A path semantical level is like a local IPL, or a kind of "moment in time" where IPL holds.
//! Just like time, each level is related to the next level, using the core axiom.
//! The core axiom might be thought of as a way to relate moments in time, or type hierarchies,
//! depending on how path semantical levels are interpreted.
//!
//! The corresponding generalization of PL is PSL. Just like adding the axiom of excluded
//! middle to IPL gets you PL, one gets PSL from PSI by adding the axiom of excluded middle.
//! PSI can be thought of as IPL plus the core axiom of Path Semantics.
//!
//! - `PL = IPL + excluded middle`
//! - `PSI = IPL + core axiom`
//! - `PSL = PL + core axiom = PSI + excluded middle`
//!
//! Compared to the axiom of exluded middle, the core axiom is a much more complex extension.
//! It is common to say "+ core axiom" to mean everything that comes with it,
//! including path semantical quality and path semantical levels.
//!
//! The core axiom does not make sense for a single level of propositions like in normal logic.
//! It requires extending propositions such that they have an associated level (a natural number).
//! In addition, one needs to add a quality operator `~~` to solve the problem of reflexivity.
//! However, not all logical languages with the core axiom requires the quality operator `~~`.
//! PSL can avoid adding the quality operator `~~` by using brute force theorem proving.
//! In this sense, Path Semantics is a whole sub-field of logic,
//! focused around the core axiom.
//!
//! ### PSI vs PSL
//!
//! PSL has a famous "Creation Theorem" (see [creation]) that makes it not entirely trustworthy
//! as a language for reasoning. It means that there are some edge cases where theorems might not
//! make sense. PSI avoids the Creation Theorem by being constructive. Thus, PSI is considered the
//! "correct" logical language in Path Semantics.
//!
//! Although PSL can be problematic to use in some edge cases, it has a pragmatic purpose.
//! PSL proves every theorem that PSI proves and has exponential speedup in brute
//! force theorem proving! Therefore, to save time, it is beneficial to check PSL first to see
//! whether something is not false in PSI, before trying to find the constructive proof.
//!
//! ### Modelling Types as Propositions
//!
//! `a : T` can be modelled as `Ty<A, T>`, which is defined as `And<Imply<A, T>, POrdProof<A, T>>`.
//! It means, there are two parts, one where `a` implies `T` and one where there is a proof that
//! `a` is at a less propositional level than `T`. Together, these two parts model types.
//!
//! ```text
//! (a : T) := (a => T) ⋀ (a < T)
//! ```
//!
//! Since there are levels of propositions, one must think about what `true` and `false` means.
//! The level of `false` is `nan` (not a number) and the level of `true` can be any level (`ltrue`).
//! To get `true` to any level, one converts back and forth using [ty::eq_true_ltrue].
//!
//! ### Symbolic Distinction
//!
//! One of the important insights in foundational Path Semantics, is that symbolic distinction is
//! safe to use, while knowledge about symbolic indistinction is unsafe. When two symbols are
//! symbolic indistinct but unequal, it leads to soundness problems. However, it is safe to reason
//! about symbolic distinction and this presents an opportunity in modern mathematics.
//!
//! In normal logic, there is no way to talk about symbolic distinction.
//! Yet, in most implementations of logical languages, symbolic distinction is possible.
//! All that is required, is adding a little bit of code.
//! Normal logic can be extended with symbolic distinction in practice and theory.
//!
//! For example, in [Avalog](https://github.com/advancedresearch/avalog) one can write the following rule:
//!
//! ```text
//! (X, q'(Y)) :- (X, Y), (Y, X), X != Y.
//! ```
//!
//! Here, `X != Y` matches only when `X` and `Y` are symbolic distinct.
//! When `X` and `Y` are symbolic indistinct, the rule does not terminate.
//! This works well in practice and allows more powerful theorem proving.
//!
//! At first, it might seem unclear how adding symbolic distinction can produce anything of value.
//! An argument in favour of symbolic distinction is that a lot of practical mathematics deal with
//! sets that have some extra structure. In some sense, a set models objects that have something
//! in common. In another sense, all objects of a set must be different. So, a set encodes how
//! objects are similar yet not completely identical. When this idea is purified, one gets a kind
//! of set where all objects are equal yet symbolic distinct. One can think about this as an idea
//! of sets as a limit, where the idea is pushed to the extreme. At this extreme limit, one loses
//! the clear definition of a set and all that remains is what a set ought to be. As if sets were
//! trying to be like this idealised symbolic distinction. This abstracts over the differences
//! between objects, such that they can be treated as the same in one way, while at the same time
//! tell whether one objects belong to the set or not.
//!
//! In modern mathematics, is common to move away from sets as models for mathematical objects.
//! One application is symbolic manipulation of expressions, where the intermediate expressions
//! between start and the goal are not important, as long one arrives at the correct answer.
//! This kind of freedom or creativity, is an important insight to understand mathematics well.
//!
//! The motivation for reasoning with symbolic distinction is to have a quality operator `~~` which
//! behaves like equality but that is not reflexive. In Path Semantics, the quality operator is
//! super important. The quality operator says when two objects are intentionally made equal,
//! as a kind of action, instead of just reasoning about logical equivalence of objects.
//! This notion of intentionality behind quality is the key to high dimensional mathematics.
//! This adds meaning to propositions that are neither `true` nor `false`, but has a richer,
//! well defined meaning on their own. With other words, Path Semantics does not only treat
//! constructive logic as merely an improved version of classical logic for proofs,
//! but as a language that has interesting structure on its own, worth studying for its own sake.
//!
//! It can be difficult to wrap your head around symbolic distinction. To some people, it seems
//! like something you would consider as "alien mathematics", since there is no obvious example
//! that can be understood with little background knowledge. Apparently, this style of doing
//! mathematics leads to profound, yet deep insights. A such insight is that to e.g. compute
//! backwards, one only needs the forward definition `f` with a proof that this definition has an
//! inverse `~inv(f)`. With other words, 50% of reversible code can be removed!
//! This is a *huge* improvement, but the road to this insight is far from easy.
//! However, it is worth to keep in mind that this journey toward improvements involve stuff like
//! symbolic distinction, as weird it might seem.
//!
//! Now, assuming you have the motivation to reason about symbolic distinction, one still faces
//! a problem: Symbolic distinction is not supported in most logical languages.
//! Yet, do not despair, just because your favourite language has no support for this!
//! It turns out that there are very clever tricks one can use, that produces satisfying results.
//! Although not all logical languages support symbolic distinction, there are ways to cheat.
//!
//! For example, `(inv(f) == f)  =>  (inv(f) ~~ f)` ([fun::inv::self_inv_to_q]).
//!
//! Here, one exploits that `(inv(f) == f)^true` is not provable in general, hence
//! `inv(f)` is symbolic distinct from `f`. Therefore, if one says `inv(f) == f`, then it must
//! be said intentionally and therefore one can lift `==` into `~~`.
//! This knowledge is impossible to express within normal logic, so one just adds an axiom!
//! There is no way to prove that this is correct, yet it is indeed safe to do so.
//! Take a moment to appreciate how deep and insightful this is:
//! Not everything in Path Semantics can be explained or justified formally in normal logic,
//! because this requires some logical language capable of expressing the ideas that one wants to
//! communicate. Since normal logic can not express symbolic distinction, there is no way for it
//! to express the ideas that goes behind designing such axioms.
//! In philosophy of mathematics, one says that this demonstrates Seshatic knowledge, which is
//! different from Platonic knowledge.
//!
//! In normal logic, there is no general way to prove that two symbols are distinct.
//! However, in some cases, due to deep knowledge of mathematics, one can create workarounds.
//! These workarounds hold for some cases, but not all.
//!
//! For more information, see [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/symbolic-distinction.pdf).
//!
//! ### Path Semantical Quality & Qubit
//!
//! The core axiom of Path Semantics can not use equality, since equality is reflexive `a == a`.
//! When using equality, the core axiom would be triggered by `a == a` and propagate relations
//! that are undesirable.
//!
//! To fix this problem, `a == b` is lifted into `a ~~ b` when `¬((a == b)^true ⋁ false^(a == b))`
//! (See [hooo::lift_q]).
//! It means, `a == b` must have been made equal intensionally, by assuming something, and also
//! without accident, e.g. by proving `false`.
//!
//! Since the `~~` operator is not reflexive, it is a partial equivalence relation and called
//! "quality" as in "equality" without the "e". When one says `a ~~ a` this is equal to `~a`
//! which is the "qubit" operator. Quality and qubit operaters can be defined from each other:
//!
//! - `(a ~~ b) == ((a == b) ⋀ ~a ⋀ ~b)`
//! - `~a == (a ~~ a)`
//!
//! One can think about qubit as "any proposition". In PSL, the truth tables with `~a` are filled
//! with random bits that uses the input `a` as seed. This means, some proofs in PSL are
//! probabilistic and the noise can be amplified or reduced, like in quantum mechanics to preserve
//! quantum superposition. Hence the name "qubit". Qubit is the unary operator analogue of quality,
//! like `-a` is the unary analogue of `b - a`. In PSI, there is no noise, but proofs must be
//! constructive.
//!
//! ### Path Semantics in Physics
//!
//! The difference between PSI and PSL is used in theoretical physics to reason about fundamental
//! physics as seen from a constructive perspective (e.g. hypergraph rewriting) or probabilistic
//! such as standard quantum mechanics. While Path Semantics does not assume enough to model our
//! physical universe precisely, it can be used to reason about our universe as one of many
//! possible ones, because fundamental physics has the same language as constructive logic.
//!
//! ### Why Path Semantics?
//!
//! In mathematics, the most important operator is equality `==`.
//! However, there are many different versions of equality.
//! In Prop, `==` means "propositional equality".
//! Propositional equality consists of two maps `a => b` and `b => a`.
//!
//! Higher dimensional mathematics is about mathematics of extended concepts and notions,
//! where the same ideas that exist in lower dimensions can be more abstract and propagate
//! along many dimensions. For example, in most programming languages, there is just one way
//! to evaluate an expression. In higher dimensional mathematics, there can be multiple dimensions
//! of evaluation, such that computation can take complex paths in some space. An example of
//! evaluation in higher dimensions is theorem proving, where expressions can be transformed in
//! more than one way and where the "answer" might not be unique.
//!
//! Another example of higher dimensional mathematics is by extending binary logic to many-valued
//! logics. Such logics can be modelled using binary logic, but when using propositional equaliy
//! `==` alone, the result is always finite. It means, one can not construct a many-valued logic
//! that has infinite dimensions. This is like a computer memory that can not be extended.
//! In normal logic we extend the memory externally, by defining new operators using more bits,
//! e.g. `and` in 4-value logic requires a new definition.
//! In infinite many-valued logic, the memory can be extended internally, meaning that one can
//! keep the existing operators without needing new definitions.
//! This means, `and` in 4-value logic has partial undefined behavior, but in a safe way.
//!
//! To get to higher dimensional mathematics, one requires a path operator `~~`.
//! This `~~` operator is called "quality" as in "equality" without the "e".
//! The expression `a ~~ b` means there is a path between `a` and `b`.
//! Unlike equality, one can not prove `a ~~ a` (a path from `a` to itself).
//! Path semantical quality is simpler than paths in Homotopy Type Theory, but allows modelling
//! types as propositions, which in turns allows modelling dependent types and Homotopy Type Theory.
//! This approach to mathematics is called "bootstrapping", where one builds a simpler language to
//! model more complex languages which in turn are better equipped to prove advanced theorems.
//!
//! Path Semantics is the framework that tells how `~~` is functioning over levels of propositions.
//! Basically, it allows, for example, doing type theoretic stuff in classical propositional logic.
//!
//! It can be very hard to understand Path Semantics, because it is abstract and high dimensional.
//! Path Semantics is not "about" some easy to understand model in particular.
//! Instead, it can be thought of as a logical language, or system of rules, that can be used in
//! combinations with other languages like building blocks to construct mathematical theories.
//!
//! For example, in physics, time might be thought of as path semantical levels, where each level
//! corresponds to a "moment" where local reasoning can take place as if time was frozen.
//!
//! There are infinite levels and each level is just as complex as normal logic.
//! The combination of the core axiom and path semantical quality makes the complexity enormous.
//! Just like chess, which has simple rules but the amount of options grow very large during play,
//! Path Semantics gets enormously complex very quickly. It dwarfs chess in complexity.
//!
//! To get a feeling of how complex Path Semantics is, consider the number of binary operators:
//!
//! - Level 1: Normal logic, `2^4` in PL, `3^9` in IPL.
//! - Level 2: Max qubit^1, `4^16` in PL, `9^81` in IPL.
//! - Level 3: Max qubit^2, `8^64` in PL, `27^729` in IPL.
//! - Level 4: Max qubit^3, `16^256` in PL, `81^6561` in IPL.
//!
//! This is how many ways there are to write `f(a, b)` where `f` is some binary operator.
//! Even with just putting two objects `a` and `b` together, it gets immensily complex very fast.
//!
//! This complexity continues toward infinity. The complexity never stops increasing and it goes
//! super-exponentially faster and faster. At level 4, if you listed every binary operator in 1 sec,
//! space would collapse into a super-massive black hole before you finished.
//!
//! Now, why should we bother extending mathematics this way, when it gets so complex?
//! The motivation is to express operators over ideas such as "you are impressively wrong" concisely.
//! This is called "Uberwrong Logic" and is the same as "Answered Modal Logic"
//! (same logic, different interpretations).
//! For example, when something is "unimpressively correct", it is the same as to say it is obvious.
//!
//! Another motivation is to understand time logically. Time is complex, so the theory is complex.
//!
//! However, one of the major motivations is to be able to model types as propositions.
//! Since types are a foundation of mathematics, modelling types as propositions makes it possible
//! to reason about mathematics within a logical framework. Using Path Semantics is beneficial
//! because it does not assume a Set theoretic model, so we can explore higher dimensional
//! mathematics without the concern that it has to correspond to something like sets.
//! For example, in language design, we are not always talking about something as "simple" as sets.
//!
//! For more information, see the
//! [Path Semantics](https://github.com/advancedresearch/path_semantics) project.

#![allow(unreachable_code)]

use crate::*;

pub use quality::Q;
pub use quality::EqQ;
pub use quality::left as refl_left;
pub use quality::right as refl_right;

pub use lprop::*;
pub use pord::*;
pub use ty::Ty;

use qubit::Qu;
use existence::EProp;
use univalence::Hom;
use nat::*;

mod lprop;
mod pord;
pub mod ty;

/// Core axiom of Path Semantics.
pub type PSem<F1, F2, X1, X2> = Imply<
    And<And<Q<F1, F2>, And<POrdProof<F1, X1>, POrdProof<F2, X2>>>,
        And<Imply<F1, X1>, Imply<F2, X2>>>,
    Q<X1, X2>,
>;

/// `(f1 : x1) ⋀ (f2 : x2)  =>  (f1 ~~ f2) => (x1 ~~ x2)`.
///
/// Core axiom of Path Semantics using type representation.
/// This contains only the implication part.
/// Equals the normal core axiom.
pub type PSemTyImply<F1, F2, X1, X2> = Imply<
    And<Ty<F1, X1>, Ty<F2, X2>>,
    Imply<Q<F1, F2>, Q<X1, X2>>,
>;

/// `(f1 : x1) ⋀ (f2 : x2)  =>  (f1 ~~ f2) : (x1 ~~ x2)`.
///
/// Stronger version of core axiom of Path Semantics using type representation.
pub type PSemTy<F1, F2, X1, X2> = Imply<
    And<Ty<F1, X1>, Ty<F2, X2>>,
    Ty<Q<F1, F2>, Q<X1, X2>>,
>;

/// Naive axiom of Path Semantics (without order assumption).
pub type PSemNaive<F1, F2, X1, X2> = Imply<
    And<Q<F1, F2>, And<Imply<F1, X1>, Imply<F2, X2>>>,
    Q<X1, X2>
>;

/// Sends first argument of Logical AND to higher level.
pub type PAndFst<A, B, C, D> = Imply<
    And<Q<And<A, B>, C>, Imply<C, D>>,
    Q<A, D>,
>;
/// Sends second argument of Logical AND to higher level.
pub type PAndSnd<A, B, C, D> = Imply<
    And<Q<And<A, B>, C>, Imply<C, D>>,
    Q<B, D>,
>;

/// Sends first argument of Logical OR to higher level.
pub type POrFst<A, B, C, D> = Imply<
    And<Q<Or<A, B>, C>, Imply<C, D>>,
    Imply<Not<B>, Q<A, D>>
>;

/// Sends second argument of Logical OR to higher level.
pub type POrSnd<A, B, C, D> = Imply<
    And<Q<Or<A, B>, C>, Imply<C, D>>,
    Imply<Not<A>, Q<B, D>>
>;

/// Normalised naive core axiom.
pub type PSemNaiveNorm<A, B, C, D> = PSemNaive<
    LN<Zero, A, B, C, D>,
    LN<One, A, B, C, D>,
    LN<Two, A, B, C, D>,
    LN<Three, A, B, C, D>
>;

/// Assumes the core axiom safely for propositions.
pub fn assume<A: Prop, B: Prop, C: Prop, D: Prop>() -> PSem<A, B, C, D> {
    unimplemented!()
}

/// `(f1 : x1) ⋀ (f2 : x2)  =>  (f1 ~~ f2) : (x1 ~~ x2)`.
///
/// Assumes the core axiom in type representation.
pub fn ty_core<A: Prop, B: Prop, C: Prop, D: Prop>() -> PSemTy<A, B, C, D> {
    Rc::new(move |(ty_a, ty_b)| ty::q_formation(ty_a, ty_b))
}

/// Converts to naive core axiom.
pub fn to_naive<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSem<A, B, C, D>
) -> PSemNaive<A, B, C, D>
    where A: POrd<C>, B: POrd<D>
{
    Rc::new(move |(f, (g, h))| p.clone()(((f, (POrdProof::new(), POrdProof::new())), (g, h))))
}

/// Converts to naive core axiom from type representation.
pub fn ty_core_to_naive<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSemTy<A, B, C, D>
) -> PSemNaive<A, B, C, D>
    where A: POrd<C>, B: POrd<D>
{
    Rc::new(move |(f, (g, h))| {
        let ty_a = (g, POrdProof::new());
        let ty_b = (h, POrdProof::new());
        p((ty_a, ty_b)).0(f)
    })
}

/// Assume naive core axiom safely.
pub fn assume_naive<A: Prop, B: Prop, C: Prop, D: Prop>() -> PSemNaive<A, B, C, D>
    where A: POrd<C>, B: POrd<D>
{
    ty_core_to_naive(ty_core())
}

/// Generates naive core axiom at increased path semantical proposition level.
pub fn assume_inc_path_level<N: Nat, A: LProp, B: LProp, C: LProp, D: LProp>()
-> PSemNaive<IncLevel<A, N>, IncLevel<B, N>, IncLevel<C, N>, IncLevel<D, N>>
    where <IncLevel<A, N> as LProp>::N: Lt<<IncLevel<C, N> as LProp>::N>,
          <IncLevel<B, N> as LProp>::N: Lt<<IncLevel<D, N> as LProp>::N>,
          (A::N, N): Add,
          (B::N, N): Add,
          (C::N, N): Add,
          (D::N, N): Add,
{
    assume_naive()
}

/// Assume a normalised naive core axiom.
///
/// The orientation is detected automatically and restored to a naive core axiom
/// which has a proof to any valid order.
pub fn assume_norm_path_level<A: LProp, B: LProp, C: LProp, D: LProp>()
-> PSemNaiveNorm<A, B, C, D>
    where
        (A::N, B::N): SortMin<A, B> + SortMax<A, B>,
        (C::N, D::N): SortMin<C, D> + SortMax<C, D>,
        (<Min<A, B> as LProp>::N, <Min<C, D> as LProp>::N):
            SortMin<Min<A, B>, Min<C, D>> +
            SortMax<Min<A, B>, Min<C, D>>,
        (<Max<A, B> as LProp>::N, <Max<C, D> as LProp>::N):
            SortMin<Max<A, B>, Max<C, D>> +
            SortMax<Max<A, B>, Max<C, D>>,
        (<MaxMin<A, B, C, D> as LProp>::N, <MinMax<A, B, C, D> as LProp>::N):
            SortMin<MaxMin<A, B, C, D>, MinMax<A, B, C, D>> +
            SortMax<MaxMin<A, B, C, D>, MinMax<A, B, C, D>>,
        <MinMin<A, B, C, D> as LProp>::N:
            Lt<<Maxi<A, B, C, D> as LProp>::N>,
        <Mixi<A, B, C, D> as LProp>::N:
            Lt<<MaxMax<A, B, C, D> as LProp>::N>,
{
    assume_naive()
}

/// Generates a naive core axiom which has reflection as end-lines.
pub fn assume_refl<A: Prop, B: Prop>() -> PSemNaive<A, A, B, B>
    where A: POrd<B>
{
    assume_naive()
}

/// Reduce naive core axiom in case of false to equality of associated propositions.
pub fn naive_red_false<A: Prop, B: Prop>(
    p: PSemNaive<False, False, A, B>,
    q: Q<False, False>,
) -> Q<A, B> {
    p((q, (imply::absurd(), imply::absurd())))
}

/// Composition.
#[allow(clippy::too_many_arguments)]
pub fn comp<F1: Prop, F2: Prop, F3: Prop, F4: Prop, X1: Prop, X2: Prop>(
    f: PSem<F1, F2, F3, F4>,
    g: PSem<F3, F4, X1, X2>,
    pr_f1_f3: POrdProof<F1, F3>,
    pr_f2_f4: POrdProof<F2, F4>,
    pr_f3_x1: POrdProof<F3, X1>,
    pr_f4_x2: POrdProof<F4, X2>,
    f1_f3: Imply<F1, F3>,
    f2_f4: Imply<F2, F4>,
    f3_x1: Imply<F3, X1>,
    f4_x2: Imply<F4, X2>,
) -> PSem<F1, F2, X1, X2> {
    Rc::new(move |((f1_eq_f2, (_pr_f1_x1, _pr_f2_x2)), (_f1_x1, _f2_x2))| {
        let f3_eq_f4 = f(((f1_eq_f2, (pr_f1_f3.clone(), pr_f2_f4.clone())),
                          (f1_f3.clone(), f2_f4.clone())));
        g(((f3_eq_f4, (pr_f3_x1.clone(), pr_f4_x2.clone())), (f3_x1.clone(), f4_x2.clone())))
    })
}

/// Composition using the naive core axiom.
pub fn naive_comp<F1: Prop, F2: Prop, F3: Prop, F4: Prop, X1: Prop, X2: Prop>(
    f: PSemNaive<F1, F2, F3, F4>,
    g: PSemNaive<F3, F4, X1, X2>,
    f1_f3: Imply<F1, F3>,
    f2_f4: Imply<F2, F4>,
    f3_x1: Imply<F3, X1>,
    f4_x2: Imply<F4, X2>,
) -> PSemNaive<F1, F2, X1, X2> {
    Rc::new(move |(f1_eq_f2, (_f1_x1, _f2_x2))| {
        let f3_eq_f4 = f((f1_eq_f2, (f1_f3.clone(), f2_f4.clone())));
        g((f3_eq_f4, (f3_x1.clone(), f4_x2.clone())))
    })
}

/// Constructs a 2D naive core axiom from two naive core axioms,
/// where one is normalised of the other.
pub fn xy_norm<
    A: LProp,
    B: LProp,
    C: LProp,
    D: LProp,
>(
    p1: PSemNaive<A, B, C, D>,
    p2: PSemNaiveNorm<A, B, C, D>,
    f_eq_a_b: Imply<Q<A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
                       B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>>,
                And<Q<A, B>, Q<LN<Zero, A, B, C, D>, LN<One, A, B, C, D>>>>,
    f_a_c: Imply<Imply<A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
                       C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>>,
                 And<Imply<A, C>, Imply<LN<Zero, A, B, C, D>, LN<Two, A, B, C, D>>>>,
    f_b_d: Imply<Imply<B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>,
                       D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>>,
                 And<Imply<B, D>, Imply<LN<One, A, B, C, D>, LN<Three, A, B, C, D>>>>,
    f_eq_c_d: Imply<And<Q<C, D>, Q<LN<Two, A, B, C, D>, LN<Three, A, B, C, D>>>,
                    Q<C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>,
                       D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>>>
) -> PSemNaive<
        A::SetLevel<(A::N, <LN<Zero, A, B, C, D> as LProp>::N)>,
        B::SetLevel<(B::N, <LN<One, A, B, C, D> as LProp>::N)>,
        C::SetLevel<(C::N, <LN<Two, A, B, C, D> as LProp>::N)>,
        D::SetLevel<(D::N, <LN<Three, A, B, C, D> as LProp>::N)>,
>
    where
        // Normalisation requirements.
        (A::N, B::N): SortMin<A, B> + SortMax<A, B>,
        (C::N, D::N): SortMin<C, D> + SortMax<C, D>,
        (<Min<A, B> as LProp>::N, <Min<C, D> as LProp>::N):
            SortMin<Min<A, B>, Min<C, D>> +
            SortMax<Min<A, B>, Min<C, D>>,
        (<Max<A, B> as LProp>::N, <Max<C, D> as LProp>::N):
            SortMin<Max<A, B>, Max<C, D>> +
            SortMax<Max<A, B>, Max<C, D>>,
        (<MaxMin<A, B, C, D> as LProp>::N, <MinMax<A, B, C, D> as LProp>::N):
            SortMin<MaxMin<A, B, C, D>, MinMax<A, B, C, D>> +
            SortMax<MaxMin<A, B, C, D>, MinMax<A, B, C, D>>,
        <MinMin<A, B, C, D> as LProp>::N:
            Lt<<Maxi<A, B, C, D> as LProp>::N>,
        <Mixi<A, B, C, D> as LProp>::N:
            Lt<<MaxMax<A, B, C, D> as LProp>::N>,
{
    Rc::new(move |(eq_a_b, (a_c, b_d))| {
        let (p1_eq_a_b, p2_eq_a_b) = f_eq_a_b.clone()(eq_a_b);
        let (p1_a_c, p2_a_c) = f_a_c.clone()(a_c);
        let (p1_b_d, p2_b_d) = f_b_d.clone()(b_d);
        let p1_eq_c_d = p1.clone()((p1_eq_a_b, (p1_a_c, p1_b_d)));
        let p2_eq_c_d = p2.clone()((p2_eq_a_b, (p2_a_c, p2_b_d)));
        f_eq_c_d.clone()((p1_eq_c_d, p2_eq_c_d))
    })
}

/// Converts core axiom to `POrFst`.
pub fn to_por_fst<A: DProp, B: Prop, C: DProp, D: Prop>(
    p: PSemNaive<Or<A, B>, C, A, D>
) -> POrFst<A, B, C, D> {
    Rc::new(move |(f, g)| {
        let p = p.clone();
        Rc::new(move |not_b| {
            let f = f.clone();
            let g = g.clone();
            match (A::decide(), C::decide()) {
                (_, Left(c)) => {
                    let or_a_b = quality::to_eq(f.clone()).1(c);
                    let a = and::exc_right((not_b, or_a_b));
                    p((f, (a.map_any(), g)))
                }
                (Left(a), Right(not_c)) => {
                    let c = quality::to_eq(f).0(Left(a));
                    match not_c(c) {}
                }
                (Right(not_a), _) => {
                    let h = Rc::new(move |or_a_b| {
                        match and::exc_both(((not_a.clone(), not_b.clone()), or_a_b)) {}
                    });
                    p((f, (h, g)))
                }
            }
        })
    })
}

/// Converts core axiom to `POrSnd`.
pub fn to_por_snd<A: Prop, B: DProp, C: DProp, D: Prop>(
    p: PSemNaive<Or<A, B>, C, B, D>
) -> POrSnd<A, B, C, D> {
    Rc::new(move |(f, g)| {
        let p = p.clone();
        Rc::new(move |not_a| {
            let f = f.clone();
            let g = g.clone();
            match (B::decide(), C::decide()) {
                (_, Left(c)) => {
                    let or_a_b = quality::to_eq(f.clone()).1(c);
                    let b = and::exc_left((not_a, or_a_b));
                    p((f, (b.map_any(), g)))
                }
                (Left(b), Right(not_c)) => {
                    let c = quality::to_eq(f).0(Right(b));
                    match not_c(c) {}
                }
                (Right(not_b), _) => {
                    let h = Rc::new(move |or_a_b| {
                        match and::exc_both(((not_a.clone(), not_b.clone()), or_a_b)) {}
                    });
                    p((f, (h, g)))
                }
            }
        })
    })
}

/// Converts core axiom to `PAndFst`.
pub fn to_pand_fst<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSemNaive<And<A, B>, C, A, D>
) -> PAndFst<A, B, C, D> {
    let y = Rc::new(move |(x, _)| x);
    Rc::new(move |(f, g)| p.clone()((f, (y.clone(), g))))
}

/// Converts core axiom to `PAndSnd`.
pub fn to_pand_snd<A: Prop, B: Prop, C: Prop, D: Prop>(
    p: PSemNaive<And<A, B>, C, B, D>
) -> PAndSnd<A, B, C, D> {
    let y = Rc::new(move |(_, x)| x);
    Rc::new(move |(f, g)| p.clone()((f, (y.clone(), g))))
}

/// Use both `PAndFst` and `PAndSnd`.
///
/// This results in a stronger statement than `PAnd` alone.
pub fn use_pand_both<A: Prop, B: Prop, C: Prop, D: Prop>(
    f: Q<And<A, B>, D>,
    g: Imply<D, C>,
    p_a: PAndFst<A, B, D, C>,
    p_b: PAndSnd<A, B, D, C>,
) -> And<Q<A, C>, Q<B, C>> {
    let eq_a_c = p_a((f.clone(), g.clone()));
    let eq_b_c = p_b((f, g));
    (eq_a_c, eq_b_c)
}

/// Use both `PAndFst` and `PAndSnd` to prove `a = b`.
pub fn pand_both_eq<A: Prop, B: Prop, C: Prop, D: Prop>(
    f: Q<And<A, B>, D>,
    g: Imply<D, C>,
    p_a: PAndFst<A, B, D, C>,
    p_b: PAndSnd<A, B, D, C>,
) -> Q<A, B> {
    let (eq_a_c, eq_b_c) = path_semantics::use_pand_both(f, g, p_a, p_b);
    quality::transitivity(eq_a_c, quality::symmetry(eq_b_c))
}

/// `(a ~~ b) ⋀ (a => (c ⋀ d)) ⋀ (b => e)  =>  (c ~~ d)`.
///
/// Proves that types are unique.
pub fn uniq_ty<A: Prop, B: Prop, C: Prop, D: Prop, E: Prop>(
    q_a_b: Q<A, B>,
    f: Imply<A, And<C, D>>,
    b_e: Imply<B, E>,
    p_a: PSemNaive<A, B, C, E>,
    p_b: PSemNaive<A, B, D, E>,
) -> Q<C, D> {
    let f_copy = f.clone();
    let a_c = Rc::new(move |x| f_copy(x).0);
    let a_d = Rc::new(move |x| f.clone()(x).1);
    let q_c_e = p_a((q_a_b.clone(), (a_c, b_e.clone())));
    let q_d_e = p_b((q_a_b, (a_d, b_e)));
    quality::transitivity(q_c_e, quality::symmetry(q_d_e))
}

/// Checks that `X` is qual to `T`.
pub fn check_q<T, X>(_: Q<X, T>) {}

/// Creation theorem.
///
/// For more information, see [paper](https://github.com/advancedresearch/path_semantics/blob/master/papers-wip2/creation-theorem.pdf).
pub fn creation<X: DProp, Y: DProp, A: Prop, B: Prop>(
    nx: Not<X>,
    ty_y_b: Ty<Y, B>,
    eqq_xy: EqQ<X, Y>,
    pord: POrdProof<X, A>,
) -> Imply<A, B> {
    let nx2 = nx.clone();
    let ty_x_a: Ty<X, A> = (Rc::new(move |x| not::absurd(nx2.clone(), x)), pord);
    let xy_ab = ty::eqq_imply(ty_x_a, ty_y_b, eqq_xy);
    let xy: Imply<X, Y> = Rc::new(move |x| not::absurd(nx.clone(), x));
    xy_ab.0(xy)
}

/// Creation theorem using homotopy map.
pub fn creation_hom<X: Prop, Y: Prop, A: Prop, B: Prop>(
    nx: Not<X>,
    ty_y_b: Ty<Y, B>,
    hom_xy: Hom<X, Y>,
    pord: POrdProof<X, A>,
) -> Imply<A, B> {
    let nx2 = nx.clone();
    let ty_x_a: Ty<X, A> = (Rc::new(move |x| not::absurd(nx2.clone(), x)), pord);
    let xy_ab = ty::hom_imply(ty_x_a, ty_y_b, hom_xy);
    let xy: Imply<X, Y> = Rc::new(move |x| not::absurd(nx.clone(), x));
    xy_ab.0(xy)
}
