//! # Improved Halting Problem
//!
//! This module is based on [hooo].
//!
//! ### Background
//!
//! The Improved Halting Problem is an attempt to change perspective of the Halting problem
//! to something more practical which can not be defeated by a simple counter-example.
//! The idea has been floating around in the AdvancedResearch forum for a couple years,
//! but since Elaine M. Landry (Ph.D.) is advancing towards an "as-if mathematics"
//! (e.g. [this lecture](https://www.youtube.com/watch?v=XRKHSlFvq4Q&t=17s))
//! we will try to make some progress in this direction before Landry's position gets misunderstood.
//!
//! It seems Landry is on the right track, but the current view in AdvancedResearch is that
//! regression of relative consistency proofs might be caused by a technicality
//! about modal fixed points (use of point free predicates of one argument),
//! thus Landry's motivation for developing "as-if mathematics" is not yet convincing.
//! It can also be that the current view of AdvancedResearch is wrong.
//!
//! However, "as-if mathematics" as an idea might be a weaker position implied by
//! Inside and Outside theories. Therefore, the current view of AdvancedResearch is stronger
//! and we would like to solve possible issues about misinterpreting "as-if mathematics".
//!
//! ### Introduction
//!
//! The standard Halting Problem can be thought of as an axiom of excluded middle:
//!
//! ```text
//! (a ⋁ ¬a)^true
//! ```
//!
//! Where `a` means "program A terminates".
//!
//! The problem with the standard Halting Problem is that by using the solver as oracle in
//! some program A, A can decide to not terminate if the solver says A terminates,
//! and if the solver says A does not terminate, then A terminates.
//! Therefore, solving the standard Halting Problem is undecidable.
//!
//! The Improved Halting Problem rephrases the problem such that there is no axiom of excluded
//! middle, but instead the solver has a stonger meta-property that it can detect paradoxes
//! caused by its own counter-factual scenario where it says a program terminates:
//!
//! ```text
//! (a^true ⋁ false^(a^true))^true
//! ```
//!
//! So, either the solver can prove a program halts without making any assumptions,
//! or it can detect a paradox. It is easy to show that ([neg_to_para]):
//!
//! ```text
//! (¬a => false^(a^true))^true
//! ```
//!
//! This means, if the program does not halt, then the solver returns `false`.

use super::*;
use hooo::*;

/// Improved Halting, implemented by Halting proposition of programs.
pub trait Halt: Prop {
    /// `a^true ⋁ false^(a^true)`.
    fn halt() -> Or<Tauto<Self>, Para<Tauto<Self>>>;
}

/// `¬a  =>  false^(a^true)`.
pub fn neg_to_para<A: Halt>(not_a: Not<A>) -> Para<Tauto<A>> {
    match A::halt() {
        Left(tauto_a) => not::absurd(not_a, tauto_a(True)),
        Right(para_tauto_a) => para_tauto_a,
    }
}
