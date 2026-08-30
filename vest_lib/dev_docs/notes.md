# Vest++ Development Documentation

## New Theory of Format Ambiguity

Vest1.0 guarantees non-ambiguity of format composition by imposing side conditions on the components. 

* `Pair(A, B)` and `Repeat(A)` is unambiguous only if `A` is *prefix-secure*
* `Choice(A, B)` is unambiguous only if `A` and `B` are *disjoint*
* `Opt(A)` is unambiguous only if `A` is *productive*

However, while *sufficient* to prove the serialze-parse roundtrip theorem, those conditions are rather ad-hoc and strict. Specifically, it prevents several classes of unambiguous formats:

* **Sequence of optional fields**: it fails to compose `Pair(Opt(A), Opt(B))` as `Opt(A)` is not prefix-secure.
* **Repeatition until terminator** it fails to compose `(Repeat(A), B)` even if `A` and `B` are disjoint, as `Repeat(A)` is not prefix-secure.

Meanwhile, this theory surprisingly allows for composition of certain unambiguous, but *meaningless* formats:

* `(Eof, Repeat(A))` is technically allowed in Vest1.0, but it's not meaningful (as it'd never process `Repeat(A)`).

Vest++ develops a new theory of format ambiguity that is more flexible and yet *subsumes* Vest1.0. The key is to specify the serialization functions in destination-passing style (DPS):

```diff
-    fn spec_serialize(&self, v: Self::Type) -> Seq<u8>;
+    fn spec_serialize(&self, v: Self::Type, obuf: Seq<u8>) -> Seq<u8>;
```

Now instead of relying on prefix-security, disjointness, and productivity, we can state the side conditions for format unambiguity more precisely with the destination buffer. Specifically, we want:

1. Facts about `A`'s parsing behavior on the serialized output of
  `B` in `Pair<A, B>`
2. Facts about `A`'s parsing behavior on the serialized output of `B` in `Choice<A, B>`
3. Facts about `A`'s parsing behavior when `Opt<A>` serializes a `None` value
4. Facts about `A`'s parsing behavior when `Repeat<A>` serializes a `nil` (`seq![]`) value
5. etc.

For example, for `Opt<A>`, we have 

```rust
open spec fn unambiguous(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
    match v {
        None => self.0.spec_parse(obuf) is None, // <-- here
        Some(vv) => self.0.unambiguous(vv, obuf),
    }
}
```

For `Choice<A, B>`, we have

```rust
open spec fn unambiguous(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
    match v {
        Either::Left(va) => self.0.unambiguous(va, obuf),
        Either::Right(vb) => {
            &&& self.1.unambiguous(vb, obuf)
            &&& self.0.spec_parse(self.1.spec_serialize(vb, obuf)) is None // <-- here
        }
    }
}
```

For `Tail`, and `Eof` we have

```rust
open spec fn unambiguous(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
    obuf.len() == 0
}
```

In `Pair<A, B>`, we have

```rust
open spec fn unambiguous(&self, v: Self::Type, obuf: Seq<u8>) -> bool {
    &&& self.1.unambiguous(v.1, obuf)
    &&& self.0.unambiguous(v.0, self.1.spec_serialize(v.1, obuf))
}
```

This DPS-based theory rejects all formats that would be rejected by Vest1.0---one still won't be able to compose things like `Pair(Tail, U32Le)`, `Opt(Empty)`, `Choice(U8, U16Le)`.

But more importantly, we can now easily express formats not supported in Vest1.0---both `Pair(Opt(A), Opt(B))` and `(Repeat(A), B)` can be composed and are unambiguous if `parse_A` fails on `serialize_B` (no longer requires prefix-security of `Opt(A)` or `Repeat(A)`!).

And we will reject meaningless formats like `(Eof, U32Le)`, as the destination buffer won't be empty when serializing `Eof`.

**Downsides**

* Less ergonoimic top-level spec/theorem:

```diff
-    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type)
-        requires
-            self.requires(),
-        ensures
-            self.wf(v) ==> self.spec_parse(self.spec_serialize(v)) == Some(
-                (self.spec_serialize(v).len() as int, v),
-            ),
-    ;
+    proof fn theorem_serialize_parse_roundtrip(&self, v: Self::Type, obuf: Seq<u8>)
+        requires
+            self.unambiguous(v, obuf),
+        ensures
+            self.wf(v) ==> self.spec_parse(self.spec_serialize(v, obuf)) == Some(
+                (self.spec_serialize(v, obuf).len() - obuf.len(), v),
+            ),
+    ;
```

* Harder to prove pre-condition:

For `Repeat`:

```rust
    pub open spec fn elems_serializable(
        &self,
        vs: Seq<A::ST>,
        obuf: Seq<u8>,
    ) -> bool {
        forall|i: int|
            #![auto]
            0 <= i < vs.len() ==> self.inner.unambiguous(
                vs[i],
                self.rfold_serialize_dps(vs.skip(i + 1), obuf),
            )
    }
```

## The `Permutation` Combinator

### Approach 1: Explicit `Alt` Chain

`Permute2<P1, P2>` parses either `(P1, P2)` or `(P2, P1)` and produces `(P1::PVal, P2::PVal)`

```rust
Permute2 ::= Alt((P1, P2), Mapped((P2, P1), swap))
```

`Permute3<A, B, C>` parses any permutation of A, B, C and produces `(A::PVal, (B::PVal, C::PVal))`

```rust
Permute3(A, B, C) ::= 
    Alt((A, Permute2(B, C)), Alt(Mapped(
        (B, Permute2(A, C)), swap2), Mapped(
        (C, Permute2(A, B)), swap3),
    )
)
```

`Permute4<A, B, C, D>` parses any permutation of A, B, C, D and produces `(A::PVal, (B::PVal, (C::PVal, D::PVal)))`

```rust
Permute4(A, B, C, D) ::= 
    Alt((A, Permute3(B, C, D)), Alt(Mapped(
        (B, Permute3(A, C, D)), swap4_1), Alt(Mapped(
        (C, Permute3(A, B, D)), swap4_2), Mapped(
        (D, Permute3(A, B, C)), swap4_3),
        )
    )
)
```

Pros:
- Clean and no additional specs/proofs/impls needed
- No heap allocation is needed
- Encodes the "True" permutation semantics
  - Due to the full backtracking semantics of `Alt`, grammars like `Permute(any, 'a')` would succeed on both inputs `'ab'` and `'ba'`
  - Although Vest++ would reject ambiguous grammars like these for any combinators implementing (`SPRoundtrip`)

Cons:
- Rust's compile-time monomorphization means that the number of instances of `Permute2` grows **factorially** with the number of permutations.
- The worst-case runtime (a malicious input that triggers the entire tree traversal of a pathological, but unambiguous grammar) is also **factorial**
  - Although it's very uncommon in practice to have such grammars (branches that share considerably long prefixes)
  - For reasonable formats (ASN.1, Protobuf, etc.), where each field is associated with a unique preceeding tag, the worst-case runtime is only **quadratic**.

### Approach 2: Greedy "Bags" of `Alt`s

The high-level idea is to split the parsing into two phases:

1. Parse the malleable stream into a *homogenous* array of Enum variants.
2. Map that array into the target tuple/struct.

Concretely:

```rust
struct Msg<T, U, V> {
    a: T,
    b: U,
    c: V,
}

enum Field<T, U, V> {
    A(T),
    B(U),
    C(V),
}

let any_field = 
    Alt(
        Mapped(p1, Field::A),
    Alt(
        Mapped(p2, Field::B),
        Mapped(p3, Field::C)
        )
);

let bag = Repeat(any_field);

TryMap(bag, |fields| {
    let mut a = None; 
    let mut b = None; 
    let mut c = None;

    for f in fields {
        match f {
            Field::A(val) => { a = Some(val); }
            Field::B(val) => { b = Some(val); }
            Field::C(val) => { c = Some(val); }
        }
    }
    
    if let (Some(a), Some(b), Some(c)) = (a, b, c) {
        Ok(Msg { a, b, c })
    } else {
        Err::Other("Missing fields")
    }
})
```

Pros:
- No backtracking: the `RepeatN` parser tries each field in order at every iteration and greedily consumes the input if it matches.
  - The worst-case runtime is only **quadratic**.
- No factorial monomorphization: the "permutation logic" is encoded at runtime, rather than fully expanded at compile time

Cons:
- Need custom enums, mappers/partial-mappers for each struct format
  - In turn, much more obligations for impls/proofs/code-generation
  - Maybe we could encapsulate this pattern and have a `PermuteN` combinator?
- Unlike approach 1, *heap allocation* is unavoidable with the use of `Repeat` in the encoding
  - For a const `N`, Can we have a version of `Repeat::<N>` that parses to a fixed-size array?
- Because this encoding is non-backtracking, it does not actually encode the "True" permutation semantics.
  - Maybe we can prove that given unambiguous fields (Vest++ already enforces this for any combinator implementing `SPRoundtrip`), two versions of permutations are semantically equivalent


## The Serialization Dillemma

In Vest1.0, we claimed that users can simply invoke `.parse` and `.serialize` methods as one-liners:

```rust
let (consumed, msg) = parse_msg(&ibuf)?;

let len = serialize_msg(&mut obuf, &msg, 0)?; // <--- the same `msg` as above
```

Our eval/benchmark were indeed using this pattern.

However, in a more realistic scenario, the user would not directly feed the parsed message (guaranteed well-formed) into the serializer. If it is a tlv-encoded message, for example, the user would need to *manually* fill in the tag and length fields and establish the `v.wf()` proof obligation before serializing:

```vest
msg = {
  @tag: u8,
  @len: u16,
  v: [u8; @len] >>= choose(@tag) {
    0x00 => msg1,
    0x01 => msg2,
    0x02 => msg3,
  }
}
```

```rust
// For parsing, `v` depends on `tag` and `len`
// For serializing, `tag` and `len` depend on `v`
struct Msg {
  tag: u8,
  len: u16,
  v: MsgV,
}

enum MsgV {
  M1(Msg1),
  M2(Msg2),
  M3(Msg3),
}
```

The dillema: to serialize the whole `Msg`, `len` should be filled and well-formed against the `v` field; but one would need to serialize `v` first to fill `len`.

Given no prior knowledge of the message value, at best the user would need to invoke the serializer like follows:

```rust
fn write_msg(msg: &Msg, obuf: &mut Vec<u8>, pos: usize) -> Result<usize> {
    // manually get the tag
    let tag = match &msg.v {
    MsgV::M1(_) => 0x00,
    MsgV::M2(_) => 0x01,
    MsgV::M3(_) => 0x02,
    };
    
    // manually get the length
    let len = len_of_msg_v(&msg.v); // api provided by Vest1.0
    
    // "correct" the tag and length
    msg.tag = tag;
    msg.len = len;
    
    assert(msg@.wf());
    serialize_msg(&mut obuf, &msg, pos)
}
```

This is not ideal: it's ad-hoc and non-compositional.

Two possible solutions without significant changes to the spec are to split the serialization into two steps:

1. Add a `prepare` auxiliary function that removes the `wf()` pre-condition and instead take *mutable references* to the user-provided value and programmatically establish the `v.wf()` proof obligation similar to the above manual steps;
2. Call `serialize` as before.

OR

1. Remove the `wf()` pre-condition and call `serialize` as before, but only *reserve spaces* in the serialization buffer for any dependent fields (the dependent `Pair`'s responsibility);
2. Add a `finalize` auxiliary function (similar to Nail/EverParse unfortunately) that re-visits the serialization buffer and fills in the dependent fields.
