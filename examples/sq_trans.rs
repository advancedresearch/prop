use prop::*;
use prop::queenity::{self, Sq};
use prop::quality::EqQ;

fn main() {}

/// This example shows that Seshatic Queenity
/// does not allow the conditions for transitivity when
/// propositions are symbolic distinct.
///
/// Symbolic distinction between `B` and `C`
/// is modeled as `EqQ<B, C>` which is equal to `(B == C) => (B ~~ C)`.
pub fn non_transitive_when_symbolic_distinct<A: Prop, B: Prop, C: Prop>(
    sq_ab: Sq<A, B>,
    sq_bc: Sq<B, C>,
    eq_q_bc: EqQ<B, C>,
) -> False {
    let nsq_b = queenity::nsq_left(sq_bc, eq_q_bc);
    nsq_b(queenity::sq_right(sq_ab))
}
