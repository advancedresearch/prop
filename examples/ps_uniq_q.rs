use std::rc::Rc;
use prop::quality::{
    nq_left,
    nq_symmetry,
    right,
    symmetry,
    Q,
};
use prop::quality_traits::UniqQ;
use prop::*;

fn main() {}

/// This example shows how unique quality
/// can be used to prove something non-trivial.
///
/// ```
/// A o ------ o C
///    \      /
///     \    /
///      \  /
///       o
///       B
///
/// ¬(a ~~ c)
/// (b ~~ b) => (b ~~ a)
/// (b ~~ b) => (b ~~ c)
/// ---------------------
/// ¬(b ~~ a) ⋀ ¬(b ~~ c)
/// ```
pub fn proof<A: Prop, B: Prop, C: Prop>(
    f: impl UniqQ<B, A>,
    g: impl UniqQ<B, C>,
    sesh_ac: Not<Q<A, C>>
) -> And<Not<Q<B, A>>, Not<Q<B, C>>> {
    let sesh_ac2 = sesh_ac.clone();
    (
        Rc::new(move |q_ba| {
            let q_ab = symmetry(q_ba);
            let sesh_bc = nq_left(q_ab.clone(), sesh_ac.clone());
            let q_bb = right(q_ab);
            let q_bc = g.uniq_q(q_bb);
            sesh_bc(q_bc)
        }),
        Rc::new(move |q_bc| {
            let q_cb = symmetry(q_bc);
            let sesh_ca = nq_symmetry(sesh_ac2.clone());
            let sesh_ba = nq_left(q_cb.clone(), sesh_ca.clone());
            let q_bb = right(q_cb);
            let q_ba = f.uniq_q(q_bb);
            sesh_ba(q_ba)
        }),
    )
}
