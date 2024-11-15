use vstd::prelude::*;
use vest::secret::{bytes::*, tail::*, pair::*, *};

verus! {

/* 
A simple format like this:
struct Foo {
    a: [secret_u8; 4],
    b: [secret_u8; 8],
    c: secret_u8_Tail,
}
*/

spec fn foo_spec() -> SecPair<SecBytes, SecPair<SecBytes, SecTail>> {
    SecPair(SecBytes(4), SecPair(SecBytes(8), SecTail))
}

exec fn mk_foo() -> (res: SecPair<SecBytes, SecPair<SecBytes, SecTail>>)
    ensures
        res@ == foo_spec(),
{
    SecPair(SecBytes(4), SecPair(SecBytes(8), SecTail))
}

} // verus!