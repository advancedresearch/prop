use prop::*;
use path_semantics::*;

/// Compose 3 layers of propositions into 2 layers.
pub fn proof<A: LProp, B: LProp, C: LProp, F2: Prop, X2: Prop, Y2: Prop>(
    a_b: Imply<A, B>,
    f2_x2: Imply<F2, X2>,
    b_c: Imply<B, C>,
    x2_y2: Imply<X2, Y2>
) -> PSemNaive<A, F2, C, Y2>
    where A::N: nat::Lt<B::N>,
          B::N: nat::Lt<C::N>
{
    naive_comp(assume_naive(), assume_naive(),
               a_b, f2_x2, b_c, x2_y2)
}

fn main() {}
