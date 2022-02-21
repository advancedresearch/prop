use prop::*;
use prop::queenity::{self, Sq, UniqSq};
use prop::quality::EqQ;

fn main() {}

/// This example shows that `UniqSq` can be used
/// to create a dominating queen `B` over `A`.
///
/// ```
/// a ¬> c                  (`a` is subordinate to `c`)
/// uniq_sq(a, b)           (`a` is dominated by `b` if `a` has any queen)
/// (b == c) => (b ~~ c)    (`b` and `c` are symbolic distinct)
/// ```
///
/// Domination here means that `A` can not be subordinate to another queen.
pub fn dominating_queen<A: Prop, B: Prop, C: Prop>(
    sq_ac: Sq<A, C>,
    uniq_sq_ab: impl UniqSq<A, B>,
    eq_q_bc: EqQ<B, C>,
) -> False {
    let eq_cb = uniq_sq_ab.uniq_sq(sq_ac.clone());
    let eq_bc = eq::symmetry(eq_cb.clone());
    let sq_ab = queenity::in_right_arg(sq_ac, eq_cb);
    let q_bc = eq_q_bc(eq_bc);
    let q_bb = quality::left(q_bc);
    let sq_bb = queenity::sq_right(sq_ab);
    let sesh_bb = queenity::to_sesh(sq_bb);
    sesh_bb(q_bb)
}
