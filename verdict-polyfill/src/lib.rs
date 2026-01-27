//! Some util functions not yet available in Verus

#![forbid(unsafe_code)]

use std::fmt::Debug;
use std::fmt::Display;
use std::fmt::Write;
use std::num::TryFromIntError;
use std::rc::Rc;
use std::str::from_utf8;
use std::sync::Arc;

use vstd::prelude::*;

verus! {

#[verifier::external_body]
pub fn str_to_rc_str(s: &str) -> (res: Rc<str>)
    ensures
        s@ == res@,
{
    s.into()
}

#[verifier::external_body]
pub fn str_to_arc_str(s: &str) -> (res: Arc<str>)
    ensures
        s@ == res@,
{
    s.into()
}

#[verifier::external_body]
pub fn rc_str_to_str(s: &Rc<str>) -> (res: &str)
    ensures
        s@ == res@,
{
    s.as_ref()
}

#[verifier::external_body]
pub fn arc_str_to_str(s: &Arc<str>) -> (res: &str)
    ensures
        s@ == res@,
{
    s.as_ref()
}

#[verifier::external_body]
pub fn rc_str_eq(s1: &Rc<str>, s2: &Rc<str>) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1 == s2
}

#[verifier::external_body]
pub fn arc_str_eq(s1: &Arc<str>, s2: &Arc<str>) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1 == s2
}

#[verifier::external_body]
pub fn rc_str_eq_str(s1: &Rc<str>, s2: &str) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1.as_ref() == s2
}

#[verifier::external_body]
pub fn arc_str_eq_str(s1: &Arc<str>, s2: &str) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1.as_ref() == s2
}

#[verifier::external_body]
pub fn str_eq_str(s1: &str, s2: &str) -> (res: bool)
    ensures
        res == (s1@ == s2@),
{
    s1 == s2
}

#[verifier::external_body]
pub fn slice_eq<T: PartialEq>(a: &[T], b: &[T]) -> (res: bool)
    ensures res == (a@ == b@)
{
    a == b
}

#[verifier::external_body]
pub fn slice_skip_copy<T: PartialEq + Copy>(a: &mut [T], skip: usize, b: &[T])
    requires old(a)@.len() >= b@.len() + skip
    ensures a@ == old(a)@.take(skip as int) + b@ + old(a)@.skip(skip + b.len())
{
    (&mut a[skip..skip + b.len()]).copy_from_slice(b)
}

#[verifier::external_body]
pub fn rc_as_ref<T: View>(rc: &Rc<T>) -> (res: &T)
    ensures
        rc.view() == res.view(),
{
    rc.as_ref()
}

#[verifier::external_body]
pub fn arc_as_ref<T: View>(arc: &Arc<T>) -> (res: &T)
    ensures
        arc.view() == res.view(),
{
    arc.as_ref()
}

#[verifier::external_body]
pub fn rc_clone<T: View>(rc: &Rc<T>) -> (res: Rc<T>)
    ensures
        rc.view() == res.view(),
{
    rc.clone()
}

#[verifier::external_body]
pub fn arc_clone<T: View>(arc: &Arc<T>) -> (res: Arc<T>)
    ensures
        arc.view() == res.view(),
{
    arc.clone()
}

#[verifier::inline]
pub open spec fn spec_option_ok_or<T, E>(option: Option<T>, err: E) -> Result<T, E>
{
    match option {
        Some(t) => Ok(t),
        None => Err(err),
    }
}

#[verifier::inline]
pub open spec fn spec_result_or<T, E, E2>(result: Result<T, E>, default: Result<T, E2>) -> Result<T, E2>
{
    match result {
        Ok(t) => Ok(t),
        Err(..) => default,
    }
}

#[verifier::external_fn_specification]
#[verifier::when_used_as_spec(spec_result_or)]
pub fn result_or<T, E, E2>(result: Result<T, E>, default: Result<T, E2>) -> (res: Result<T, E2>)
    ensures res == spec_result_or(result, default),
{
    result.or(default)
}

/// Currently we do not have a specification in Verus for UTF-8
/// so we just assume the implementation of `from_utf8` is correct
pub uninterp spec fn spec_parse_utf8(s: Seq<u8>) -> Option<Seq<char>>;
pub uninterp spec fn spec_serialize_utf8(s: Seq<char>) -> Seq<u8>;

#[verifier::external_body]
pub proof fn spec_utf8_parse_serialize_roundtrip(buf: Seq<u8>)
    ensures spec_parse_utf8(buf) matches Some(s) ==> spec_serialize_utf8(s) == buf
{}

#[verifier::external_body]
pub proof fn spec_utf8_serialize_parse_roundtrip(s: Seq<char>)
    ensures spec_parse_utf8(spec_serialize_utf8(s)) == Some(s)
{}

#[verifier::external_body]
pub fn utf8_to_str(s: &[u8]) -> (res: Option<&str>)
    ensures
        res is Some <==> spec_parse_utf8(s@) is Some,
        res matches Some(res) ==> res@ == spec_parse_utf8(s@).unwrap(),
{
    from_utf8(s).ok()
}

#[verifier::external_body]
pub fn str_to_utf8(s: &str) -> (res: &[u8])
    ensures res@ =~= spec_serialize_utf8(s.view())
{
    s.as_bytes()
}

/// We trust the implementation of `u64::to_string` for now
pub uninterp spec fn spec_u64_to_string(x: u64) -> (res: Seq<char>);

#[verifier::external_body]
pub fn char_to_string(c: char) -> (res: String)
    ensures res@ == seq![c]
{
    c.to_string()
}

#[verifier::external_body]
pub fn u64_to_string(x: u64) -> (res: String)
    ensures res@ == spec_u64_to_string(x)
{
    x.to_string()
}

#[verifier::external_body]
#[inline(always)]
pub fn u64_to_string_inplace(res: &mut String, x: u64)
    ensures res@ == old(res)@ + spec_u64_to_string(x)
{
    write!(res, "{}", x).unwrap();
}

/// From Verus tutorial
pub fn vec_map<T, U>(v: &Vec<T>, f: impl Fn(&T) -> U) -> (res: Vec<U>)
    requires
        forall|i| #![trigger v[i]] 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
    ensures
        res.len() == v.len(),
        forall|i|
            #![trigger v[i]]
            0 <= i < v.len() ==> call_ensures(f, (&v[i],), #[trigger] res[i]),
{
    let mut res = Vec::with_capacity(v.len());
    let mut j = 0;
    while j < v.len()
        invariant
            forall|i| #![trigger v[i]] 0 <= i < v.len() ==> call_requires(f, (&v[i],)),
            0 <= j <= v.len(),
            j == res.len(),
            forall|i| #![trigger v[i]] 0 <= i < j ==> call_ensures(f, (&v[i],), #[trigger] res[i]),
        decreases v.len() - j
    {
        res.push(f(&v[j]));
        j += 1;
    }
    res
}

#[verifier::external_body]
pub fn vec_set<T>(v: &mut Vec<T>, i: usize, x: T)
    requires
        0 <= i < old(v).len(),
    ensures
        v.len() == old(v).len() && (forall|j| 0 <= j < v.len() && j != i ==> v[j] == old(v)[j])
            && v[i as int] == x,
{
    v[i] = x;
}

#[verifier::external_body]
pub fn vec_push_nested<T>(v: &mut Vec<Vec<T>>, i: usize, x: T)
    requires
        0 <= i < old(v)@.len(),

    ensures
        v.len() == old(v).len(),
        forall |j| #![trigger v@[j]] 0 <= j < v@.len() ==> {
            &&& i == j ==> v@[j]@ == old(v)@[j]@.push(x)
            &&& i != j ==> v@[j] == old(v)@[j]
        },
{
    v[i].push(x);
}

/// Note: this implicitly assumes that v.clone()@ == v@
#[verifier::external_body]
pub fn vec_init_n<T: Clone + View>(n: usize, v: &T) -> (res: Vec<T>)
    ensures
        res.len() == n,
        forall |i| 0 <= i < n ==> #[trigger] res@[i]@ == v@,
{
    let mut res: Vec<T> = Vec::with_capacity(n);

    #[allow(unused_variables)]
    for i in 0..n
        invariant
            res.len() == i,
            forall |j| 0 <= j < i ==> #[trigger] res@[j]@ == v@,
    {
        res.push(v.clone());
    }

    res
}

/// Copied from Verus example
pub fn vec_reverse<T: DeepView>(v: &mut Vec<&T>)
    ensures
        v.len() == old(v).len(),
        old(v).deep_view().reverse() =~= v.deep_view(),
{
    let length = v.len();
    let ghost v1 = v.deep_view();
    for n in 0..(length / 2)
        invariant
            length == v.len(),
            forall|i: int| #![auto] 0 <= i < n ==> v[i].deep_view() == v1[length - 1 - i],
            forall|i: int| #![auto] 0 <= i < n ==> v1[i] == v[length - 1 - i].deep_view(),
            forall|i: int| n <= i && i + n < length ==> #[trigger] v[i].deep_view() == v1[i],
    {
        let x = v[n];
        let y = v[length - n - 1];
        v.set(n, y);
        v.set(length - n - 1, x);
    }
}

#[verifier::external_body]
pub fn vec_contains<T: PartialEq>(v: &Vec<T>, elem: &T) -> (res: bool)
    ensures res == v@.contains(*elem),
{
    v.contains(elem)
}

pub open spec fn is_prefix_of<T>(s1: Seq<T>, s2: Seq<T>) -> bool {
    &&& s1.len() <= s2.len()
    &&& forall |i| 0 <= i < s1.len() ==> #[trigger] s1[i] == #[trigger] s2[i]
}

/// Join elements of list by sep
pub open spec fn seq_join<T>(list: Seq<Seq<T>>, sep: Seq<T>) -> Seq<T>
    decreases list.len(),
{
    if list.len() == 0 {
        seq![]
    } else if list.len() == 1 {
        list[0]
    } else {
        seq_join(list.drop_last(), sep) + sep + list.last()
    }
}

/// Join a list of strings by the separator `sep`
pub fn join_strs(list: &Vec<&str>, sep: &str) -> (res: String)
    ensures
        res@ =~= seq_join(list@.map_values(|v: &str| v.view()), sep@),
{
    let mut res = string_new();
    assert(res@ =~= seq![]);

    let ghost list_deep_view = list@.map_values(|v: &str| v.view());

    for i in 0..list.len()
        invariant
            list_deep_view.len() == list.len(),
            forall|i| #![auto] 0 <= i < list.len() ==> list_deep_view[i] == list[i]@,
            res@ =~= seq_join(list_deep_view.take(i as int), sep@),
    {
        if i != 0 {
            let ghost old_res = res@;
            res.append(sep);
            res.append(list[i]);
            assert(list_deep_view.take((i + 1) as int).drop_last() =~= list_deep_view.take(
                i as int,
            ));
        } else {
            res.append(list[i]);
        }
    }
    assert(list_deep_view.take(list.len() as int) =~= list_deep_view);

    res
}

/// Same as above, but for vectors of Strings
/// TODO: merge?
pub fn join_strings(list: &Vec<String>, sep: &str) -> (res: String)
    ensures
        res@ =~= seq_join(list@.map_values(|v: String| v.view()), sep@),
{
    let mut res = string_new();
    assert(res@ =~= seq![]);

    let ghost list_deep_view = list@.map_values(|v: String| v.view());

    for i in 0..list.len()
        invariant
            list_deep_view.len() == list.len(),
            forall|i| #![auto] 0 <= i < list.len() ==> list_deep_view[i] == list[i]@,
            res@ =~= seq_join(list_deep_view.take(i as int), sep@),
    {
        if i != 0 {
            let ghost old_res = res@;
            res.append(sep);
            res.append(list[i].as_str());
            assert(list_deep_view.take((i + 1) as int).drop_last() =~= list_deep_view.take(
                i as int,
            ));
        } else {
            res.append(list[i].as_str());
        }
    }
    assert(list_deep_view.take(list.len() as int) =~= list_deep_view);

    res
}

/// Trusted spec
#[verifier::external_body]
#[inline(always)]
pub fn slice_subrange<V>(s: &[V], start: usize, end: usize) -> (res: &[V])
    requires start <= end <= s.len()
    ensures res@ == s@.subrange(start as int, end as int)
{
    &s[start..end]
}

pub fn slice_drop_first<V>(s: &[V]) -> (res: &[V])
    requires s.len() > 0
    ensures res@ == s@.drop_first()
{
    slice_subrange(s, 1, s.len())
}

pub fn slice_skip<V>(s: &[V], n: usize) -> (res: &[V])
    requires n <= s@.len()
    ensures res@ == s@.skip(n as int)
{
    slice_subrange(s, n, s.len())
}

pub fn slice_take<V>(s: &[V], n: usize) -> (res: &[V])
    requires n <= s@.len()
    ensures res@ == s@.take(n as int)
{
    slice_subrange(s, 0, n)
}

#[verifier::external_body]
pub fn slice_to_vec<V: Clone + Eq>(s: &[V]) -> (res: Vec<V>)
    ensures
        res@.len() == s@.len(),
        forall |i| 0 <= i < res@.len() ==> res@[i] == s@[i],
{
    s.to_vec()
}

/// Wrapper around `Chars` since Verus doesn't support all iterators yet
#[verifier::external_body]
pub struct CharsIter<'a>(std::str::Chars<'a>);

pub uninterp spec fn spec_chars_iter_str<'a>(iter: CharsIter<'a>) -> Seq<char>;
pub uninterp spec fn spec_chars_iter_index<'a>(iter: CharsIter<'a>) -> int;

#[verifier::external_body]
pub fn chars_iter_next<'a>(iter: &mut CharsIter<'a>) -> (res: Option<char>)
    ensures ({
        let raw = spec_chars_iter_str(*old(iter));
        let prev_idx = spec_chars_iter_index(*old(iter));
        let new_idx = spec_chars_iter_index(*iter);

        &&& spec_chars_iter_str(*iter) == raw
        &&& res matches Some(c) ==> prev_idx < raw.len() && c == raw[prev_idx] && new_idx == prev_idx + 1
        &&& res is None <==> new_idx == prev_idx == raw.len()
    })
{
    iter.0.next()
}

#[verifier::external_body]
pub fn str_chars<'a>(s: &'a str) -> (res: CharsIter<'a>)
    ensures
        s@.len() <= usize::MAX,
        spec_chars_iter_str(res) == s@,
        spec_chars_iter_index(res) === 0,
{
    CharsIter(s.chars())
}

#[verifier::external_body]
#[inline(always)]
pub fn string_new_with_cap(cap: usize) -> (res: String)
    ensures
        res@ == Seq::<char>::empty(),
{
    String::with_capacity(cap)
}

#[verifier::external_body]
#[inline(always)]
pub fn str_byte_len(s: &str) -> usize
{
    s.as_bytes().len()
}

#[verifier::external_body]
pub fn string_new() -> (res: String)
    ensures
        res@ == Seq::<char>::empty(),
{
    String::new()
}

#[verifier::external_body]
#[inline(always)]
pub fn string_push(s: &mut String, c: char)
    ensures s@ == old(s)@.push(c)
{
    s.push(c)
}

#[verifier::external_body]
#[inline(always)]
pub fn string_push_str(s: &mut String, r: &str)
    ensures s@ == old(s)@ + r@
{
    s.push_str(r)
}

#[verifier::external_body]
pub fn strs_to_strings(strs: &[&str]) -> (res: Vec<String>)
    ensures res.deep_view() == strs.deep_view()
{
    strs.iter().map(|s| s.to_string()).collect()
}

#[verifier::external_body]
pub fn format_dbg(a: impl Debug) -> String {
    format!("{:?}", a)
}

#[verifier::external_body]
pub fn format(a: impl Display) -> String {
    format!("{}", a)
}

#[verifier::external_body]
pub fn join_2(a: impl Display, b: impl Display) -> String {
    format!("{}{}", a, b)
}

/// A temporary replacement for format!
/// join!(a, b, c) is equivalent to format!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! join {
    ($a:expr) => {format($a)};
    ($a:expr, $($rest:expr),+) => {
        join_2($a, join!($($rest),+))
    };
}

// #[allow(unused_imports)]
// pub use join;

/// print_join!(a, b, c) is equivalent to print!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! print_join {
    ($($args:expr),+) => {
        print(join!($($args),+));
    }
}

// #[allow(unused_imports)]
// pub use print_join;

/// println_join!(a, b, c) is equivalent to println!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! println_join {
    ($($args:expr),+) => {
        println(join!($($args),+));
    }
}

// #[allow(unused_imports)]
// pub use println_join;

/// eprint_join!(a, b, c) is equivalent to eprint!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! eprint_join {
    ($($args:expr),+) => {
        eprint(join!($($args),+));
    }
}

// #[allow(unused_imports)]
// pub use eprint_join;

/// eprintln_join!(a, b, c) is equivalent to eprintln!("{}{}{}", a, b, c)
#[allow(unused_macros)]
#[macro_export]
macro_rules! eprintln_join {
    ($($args:expr),+) => {
        eprintln(join!($($args),+));
    }
}

// #[allow(unused_imports)]
// pub use eprintln_join;

} // verus!
