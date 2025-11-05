use crate::my_vec;
use vest_lib::properties::*;
use vest_lib::regular::bytes;
use vest_lib::regular::modifier::Cond;
use vest_lib::regular::tag::*;
use vest_lib::regular::uints::*;
use vest_lib::regular::variant::*;
use vstd::prelude::*;
use vstd::slice::slice_subrange;

verus! {

broadcast use vest_lib::regular::uints::size_of_facts;

exec fn disjoint_examples(a: u32, b: u8) -> Result<(), Error> {
    let c1 = Cond { cond: a == 0 && b == 1, inner: U8 };
    let c2 = Cond { cond: 0 < a && a < 5 && b == 2, inner: U16Le };
    let c3 = Cond { cond: a >= 5 && b == 2, inner: U32Le };

    let choice = ord_choice!(c1, c2, c3);

    let mut data = my_vec![0u8, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    let mut s = my_vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0];
    let (n, val) = <_ as Combinator<&[u8], Vec<u8>>>::parse(&choice, data.as_slice())?;
    let val_ref = match &val {
        inj_ord_choice_pat!(x, *, *) => inj_ord_choice_result!(x, *, *),
        inj_ord_choice_pat!(*, x, *) => inj_ord_choice_result!(*, x, *),
        inj_ord_choice_pat!(*, *, x) => inj_ord_choice_result!(*, *, x),
    };
    let len = <_ as Combinator<&[u8], Vec<u8>>>::serialize(&choice, val_ref, &mut s, 0)?;

    Ok(())
}

} // verus!
