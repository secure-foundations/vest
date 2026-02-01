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
