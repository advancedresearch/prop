use prop::*;
use path_semantics::*;

/// Compose 3 layers of propositions into 2 layers.
pub fn proof<A: LProp, B: LProp, C: LProp, F2: LProp, X2: LProp, Y2: LProp>(
    a_b: Imply<A, B>,
    f2_x2: Imply<F2, X2>,
    b_c: Imply<B, C>,
    x2_y2: Imply<X2, Y2>
) -> PSemNaive<A, F2, C, Y2>
    where A::N: nat::Lt<B::N>,
          B::N: nat::Lt<C::N>,
          F2::N: nat::Lt<X2::N>,
          X2::N: nat::Lt<Y2::N>,
{
    naive_comp(assume_naive(), assume_naive(),
               a_b, f2_x2, b_c, x2_y2)
}

fn main() {}
