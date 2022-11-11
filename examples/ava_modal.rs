use prop::*;
use ava_modal::*;
use hooo::*;

// `¬¬¬◇a => ¬□a`.
pub fn proof1<A: DProp>(nnnpos_a: Not<Not<Not<Pos<A>>>>) -> Not<Nec<A>> {
    imply::in_left(nnnpos_a, |x: Nec<A>| {
        let x = npos_to_para(x);
        let x = pow_rev_not(x);
        let x: Not<Not<Pos<A>>> = imply::in_left(x, npos_to_para);
        x
    })
}

// `¬◇a => ¬□a`.
pub fn proof2<A: DProp>(npos_a: Not<Pos<A>>) -> Not<Nec<A>> {
    proof1(not::double(npos_a))
}

/// `¬□a => ¬◇a`.
pub unsafe fn proof3<A: Prop>(nnec_a: Not<Nec<A>>) -> Not<Pos<A>> {
    let x = not::rev_triple(imply::in_left(nnec_a, |x: Not<Not<Pos<A>>>| {
        let x: Not<Para<A>> = imply::in_left(x, |y| para_to_npos(y));
        let x = pow_not(x);
        let x = para_to_npos(x);
        x
    }));
    x
}

fn main() {}
