
 # Exec Codegen Plan for vest2/src/codegen/execs.rs

## Summary

Implement generated Parser, Serializer, and Prepare for all named DSL definitions using imperative exec code for sequencing, dependencies,
nominal mapping, predicates, enums, and dependent choices, while still reusing existing vest_lib2 exec combinators for length-restricted
parsing, repetitions, options, and anonymous structural suffixes where they materially simplify correctness.

The generator should stay in a single execs.rs file with a small set of local helpers. Do not introduce new modules for this pass.

## Implementation Changes

### 1. Generated exec surface

- Emit, for every generated named format wrapper FooFmt{...}:
    - impl<'i> Parser<&'i [u8]> for FooFmt{...}
    - impl<'i> Serializer<&'i Foo<'i?>> for FooFmt{...} or Serializer<&'i Foo> when the exec type is not lifetime-parameterized
    - impl<'i> Prepare<&'i Foo<'i?>> for FooFmt{...} or Prepare<&'i Foo>
- Continue to generate full exec impls for lifted/internal named formats as well, because parent formats will call them.
- Public convenience APIs:
    - For nominal top-level user-defined formats (structs / enums / nominal choice enums):
        - non-parameterized: impl Foo<'i?> { parse(...), serialize(...), prepare(...) }
        - parameterized: impl Foo<'i?> { parse(params..., ibuf), serialize_with(params..., obuf), prepare_with(params...) }
    - For alias-valued user-defined formats (Rust type aliases, where inherent impls are illegal), emit module-level functions:
        - foo_parse(...), foo_serialize(...), foo_prepare(...)
        - parameterized aliases take params first
    - All public parse / prepare APIs must route through Named("dsl_name", FooFmt{...}) for error context.
    - Public serialize APIs call the bare wrapper FooFmt{...}.serialize(...) because serialization has no error context channel.

### 2. Internal generator shape in execs.rs

Keep execs.rs single-file, with these local helper families:

- gen_execs_section(...) orchestrates per-definition emission
- gen_parser_impl(...), gen_serializer_impl(...), gen_prepare_impl(...)
- gen_public_exec_api(...)
- recursive lowerers for:
    - parse bodies
    - serialize bodies
    - prepare bodies
    - raw exec combinator expressions for the cases we intentionally delegate
- One shared helper for checked_add chains in generated Prepare code

No new abstraction beyond these local helpers. Reuse CodeWriter / render_ts for readability.

### 3. Parser lowering rules

Always start generated parser impls with:

- broadcast use ...SafeParser::lemma_parse_safe;
- reveal(<FooFmt as SpecParser>::spec_parse);

Then lower by construct:

- Primitive ints / bytes / tail:
    - use existing combinator parsers directly:
        - U8/U16/U24/U32/U64/VarInt/ULeb128.parse(&rest)?
        - Fixed::<N>.parse(&rest)?
        - Varied(len).parse(&rest)?
        - Tail.parse(&rest)?
- Integer / enum constraints:
    - parse the base format imperatively, then if !pred { return Err(ParseError::predicate_failed()) }
    - enum-constraint mismatch also uses predicate failure
- Closed enums:
    - parse underlying integer
    - match on the integer to a nominal enum variant
    - unknown tag => Err(ParseError::invalid_tag())
- Open enums:
    - parse underlying integer
    - known tags => named variants
    - fallback => Unknown(x)
- Structs:
    - parse field-by-field with let (n_i, field_name) = ...?; let rest = rest.skip(n_i);
    - const fields: parse and discard with direct const/tag logic
    - dependent fields: later field parsers may reference earlier locals directly
    - build the nominal struct at the end
    - final proof shape: assert(self.spec_parse(ibuf@) == Some((total_n as int, value.deep_view())));
- Wrap:
    - parse prior const tags, then inner, then post const tags, all imperatively
    - no Preceded / Terminated / WithPrefixTag delegation in exec code
- Dependent choose(@x):
    - lower to one selector-driven match
    - each arm parses the chosen branch directly and constructs the nominal enum variant (or plain branch value if the surrounding format
      already carries the nominal type)
    - no Bind, no Mapped, no nested Sum on the exec side
- Non-dependent choose:
    - parser uses an imperative ordered try-chain
    - preserve Choice error precedence exactly
    - successful branch constructs the nominal enum variant directly
- bytes >>= fmt:
    - generate ExactLen(len_expr, inner_exec_fmt).parse(&rest)?
    - inner_exec_fmt is:
        - the generated wrapper FooFmt{...} when fmt is a named/lifted user-defined format
        - otherwise a raw exec combinator expression for anonymous structural formats
- General lhs >>= rhs where lhs is not bytes:
    - generate AndThen(lhs_exec_fmt, rhs_exec_fmt).parse(&rest)?
    - use this for cases like Tail >>= [item; count]
- Arrays / repetition / options:
    - [fmt; N] => Array::<N, _>(fmt).parse(...)
    - [fmt; @count] => RepeatN(count, fmt).parse(...)
    - Vec<fmt> at tail => RepeatTillEnd(fmt).parse(...)
    - Option<fmt> at tail => OptionalEnd(fmt).parse(...)
    - for non-tail Option / Vec inside structs => use Star/Opt (as unambiguity is already proved in the spec land)
- User-defined subformats:
    - internal parser calls use Named("dsl_name", FooFmt{...}).parse(&rest)? for error context
    - do not inline the subformat’s exec body into the parent

### 4. Serializer lowering rules

Always start with:

- reveal(<FooFmt as SpecSerializer>::spec_serialize);
- let ghost old_obuf = obuf@;

Then lower by construct:

- Primitive ints / bytes / tail:
    - use existing primitive serializers directly
- Closed/open enums:
    - match nominal enum to the encoded tag, then serialize the base integer
- Structs / wrap / consts:
    - serialize in wire order with plain statements
- Dependent choose(@x):
    - match on (selector, value) when both matter
    - mismatched selector/value combinations are impossible under the public serialize precondition, so the generated ex_serialize body may
      use a no-op fallback arm, as in the hand-written TLV example
- Non-dependent choose:
    - match on the nominal choice enum and serialize the corresponding branch
- bytes >>= fmt / general and_then:
    - for named/lifted inner formats, call the generated wrapper serializer
    - for anonymous raw inner formats, call the delegated combinator serializer
- Arrays / repetition / options:
    - reuse Array, RepeatN, RepeatTillEnd, OptionalEnd, Star, Opt serializers
- Nested user-defined subformats:
    - call the wrapper serializer directly, not Named
- End every serializer with:
    - assert(obuf@ == old_obuf + self.spec_serialize(v.deep_view()));

### 5. Prepare lowering rules

Always start with:

- reveal(<FooFmt as Consistency>::consistent);
- reveal(<FooFmt as SpecByteLen>::byte_len);

Then lower by construct:

- Primitive ints / bytes / tail:
    - call existing prepare(...)
- Constraints / consts / enums:
    - perform explicit checks first, returning:
        - PredicateFailed for refined/constraint rejection
        - InvalidTag for bad enum/const/tag mismatches
    - then call child prepare
- Structs / wrap:
    - compute each field length in wire order
    - combine with checked_add, returning LengthTooLarge on overflow
- Dependent choose(@x):
    - match on selector and/or nominal value, then prepare the selected branch
    - selector/value mismatch => Err(NotCompliant(InvalidTag))
- Non-dependent choose:
    - match on the nominal branch enum and prepare that branch
- bytes >>= fmt:
    - use ExactLen(len_expr, inner_exec_fmt).prepare(value)
    - this is the authoritative check for exact-length consistency
- General lhs >>= rhs:
    - use AndThen(lhs_exec_fmt, rhs_exec_fmt).prepare(value)
- Arrays / repetition / options:
    - reuse existing combinator prepare(...)
- Internal user-defined subformats:
    - call Named("dsl_name", FooFmt{...}).prepare(...) to attach nested NamedFormat(...) compliance errors
- Public parameterized prepare_with(...) passes the parameters into FooFmt{...}.prepare(...)

### 6. Raw exec-format expression renderer

execs.rs needs a small expression renderer for cases where the generated exec body delegates to combinators instead of lowering directly.
It
should emit runtime expressions for:

- primitives: U8, U16Le/Be, U24Le/Be, U32Le/Be, U64Le/Be, VarInt::<true>
- Fixed, Varied, Tail
- Array, RepeatN, RepeatTillEnd, OptionalEnd, Star, Opt
- ExactLen, AndThen
- const/tag helpers when used in delegated suffixes
- named/lifted user-defined subformats as FooFmt{...} or FooFmt

This renderer is only for delegated exec cases. It must not be used to reintroduce Mapped, Bind, Refined, or spec-side Sum-based mapping
into the exec path.

## Test Plan

Implement and verify in phases, using the existing generated corpus as milestones:

1. Parser-only smoke:

- codegen, enums, matches, tlv
- acceptance: generated parser impls compile and verify

2. Add serializer + prepare for simple nominal formats:

- codegen, enums, length_expr, nested_access

3. Add non-tail option/repeat suffix lowering:

- opt, repeat

4. Add nested/lifted and exact-length cases:

- anonymous_nested, elab, tlv

5. Add larger real-world modules:

- bitcoin, tls

Checks for each phase:

- regenerate the corresponding .rs files
- cargo test in vest2
- cargo verus verify -- --expand-errors --verify-only-module <module> in vest2/test
- final acceptance: full cargo verus verify -- --expand-errors in vest2/test

Targeted scenarios that must be covered by generated exec code:

- closed enum parse reject / open enum unknown capture
- dependent choose over enum/int/byte-array selectors
- ExactLen with parameterized named inner formats
- nested parameter capture like @hdr.payload_length - 4
- top-level and non-tail Option / Vec
- alias-valued user-defined formats (header_alias, header_bytes, hello_retry_request, responder_id, etc.)
- default branches in dependent chooses (msg_alt_content, TLS extension payloads)

## Assumptions

- Omitted fields are still out of scope; no Implicit exec generation in this pass.
- Public convenience APIs are emitted for user-defined DSL definitions only; lifted anonymous helper formats get wrapper exec impls but no
  public inherent/free API.
- Alias-valued definitions use free functions because Rust does not allow inherent impls on type aliases.
- The current selected Makefile corpus is the implementation target; ikev2 can be enabled after tls is green.

For this pass, temperarily mark all emitted exec fns `#[verifier::external_body]` and focus on making sure the emitted code *compiles and runs* correctly. Right now there's no executable impl for uleb128 so in this pass mark that as TODO as well.

```vest
btc_tx = {
const magic: u8 = 1,
  @txin_cnt: u8,
  txin: [u8; @txin_cnt],
  @txout_cnt: u8 | 1..,
  txout: [u8; @txout_cnt],
  witness: [u8; @txin_cnt],
  locktime: u8,
}
```

```rust
impl<'i> Parser<&'i [u8]> for TxSegwitFmt {
type PT = BtcTx<'i>;

fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
    let rest = *ibuf;

    let (n1, magic) = Const(U8, 1u8).parse(&rest)?;
    let rest = rest.skip(n1);
    let (n2, txin_cnt) = U8.parse(&rest)?;
    let rest = rest.skip(n2);
    let (n3, txin) = Varied(txin_cnt).parse(&rest)?;
    let rest = rest.skip(n3);
    let (n4, txout_cnt) = U8.parse(&rest)?;
    if txout_cnt < 1 {
        return Err(ParseError::predicate_failed());
    }
    let rest = rest.skip(n4);
    let (n5, txout) = Varied(txout_cnt).parse(&rest)?;
    let rest = rest.skip(n5);
    let (n6, witness) = Varied(txin_cnt).parse(&rest)?;
    let rest = rest.skip(n6);
    let (n7, locktime) = U8.parse(&rest)?;
    let total_n = n1 + n2 + n3 + n4 + n5 + n6 + n7;
    let final_v = BtcTx { magic, txin_cnt, txin, txout_cnt, txout, witness, locktime };
    Ok((total_n, final_v))
}
}

impl<'i> Serializer<&'i BtcTx<'i>> for TxSegwitFmt {
fn ex_serialize(&self, v: &'i BtcTx<'i>, obuf: &mut Vec<u8>) {
    let BtcTx { magic, txin_cnt, txin, txout_cnt, txout, witness, locktime } = *v;
    U8.ex_serialize(1u8, obuf);
    U8.ex_serialize(txin_cnt, obuf);
    Varied(txin_cnt).ex_serialize(txin, obuf);
    U8.ex_serialize(txout_cnt, obuf);
    Varied(txout_cnt).ex_serialize(txout, obuf);
    Varied(txin_cnt).ex_serialize(witness, obuf);
    U8.ex_serialize(locktime, obuf);
}
}

impl<'i> Prepare<&BtcTx<'i>> for TxSegwitFmt {
fn prepare(&self, v: &BtcTx<'i>) -> Result<usize, PreSerializeError> {
    let BtcTx { txin_cnt, txin, txout_cnt, txout, witness, locktime } = v;
    let l1 = U8.prepare(1u8)?;
    let l2 = U8.prepare(txin_cnt)?;
    let l3 = Varied(txin_cnt).prepare(txin)?;
    let l4 = U8.prepare(txout_cnt)?;
    if txout_cnt < 1 {
        return Err(PreSerializeError::NotCompliant(ComplianceErrorKind::PredicateFailed));
    }
    let l5 = Varied(txout_cnt).prepare(txout)?;
    let l6 = Varied(txin_cnt).prepare(witness)?;
    let l7 = U8.prepare(locktime)?;
    let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(
        l3,
    ).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(l4).ok_or(
        PreSerializeError::LengthTooLarge,
    )?.checked_add(l5).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(l6).ok_or(
        PreSerializeError::LengthTooLarge,
    )?.checked_add(l7).ok_or(PreSerializeError::LengthTooLarge)?;

    Ok(total_len)
}
}
```

```vest
tlv = {
  @tag: msg_ty,
  @len: u8,
  payload: [u8; @len] >>= choose(@tag) {
      TYPE1 => u8,
      TYPE2 => [u8; 10],
      TYPE3 => Tail,
      TYPE4 => Tail,
  },
}
```

```rs
impl<'i> Parser<&'i [u8]> for TLVFmt {
type PT = TLVMsgPayload<'i>;

fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
    let rest = *ibuf;

    let (n1, tag) = MsgTy::parse(&rest)?;
    let rest = rest.skip(n1);
    let (n2, len) = U8.parse(&rest)?;
    let rest = rest.skip(n2);
    let (n3, payload) = ExactLen(len, TLVPayloadFmt { tag }).parse(&rest)?;
    let total_n = n1 + n2 + n3;
    let final_v = TLVMsgPayload { tag, len, payload };
    Ok((total_n, final_v))
}
}

impl<'i> Serializer<&TLVMsg<'i>> for TLVFmt {
fn ex_serialize(&self, v: &TLVMsg<'i>, obuf: &mut Vec<u8>) {
    let TLVMsgPayload { tag, len, payload } = v;
    MsgTyFmt.ex_serialize(tag, obuf);
    U8.ex_serialize(len, obuf);
    TLVPayloadFmt { tag }.ex_serialize(payload, obuf);
}
}

impl<'i> Prepare<&TLVMsg<'i>> for TLVFmt {
fn prepare(&self, v: &TLVMsg<'i>) -> Result<usize, PreSerializeError> {
    let TLVMsgPayload { tag, len, payload } = v;
    let l1 = MsgTyFmt.prepare(tag)?;
    let l2 = U8.prepare(len)?;
    let l3 = TLVPayloadFmt { tag }.prepare(v)?;
    let total_len = l1.checked_add(l2).ok_or(PreSerializeError::LengthTooLarge)?.checked_add(
        l3,
    ).ok_or(PreSerializeError::LengthTooLarge)?;
    Ok(total_len)
}
}

impl<'i> Parser<&'i [u8]> for TLVPayloadFmt {
type PT = TLVMsg<'i>;

fn parse(&self, ibuf: &&'i [u8]) -> PResult<Self::PT> {
    let rest = *ibuf;

    let (n, payload) = match self.tag {
        MsgTy::TYPE1 => {
            let (n, v) = U8.parse(&rest)?;
            (n, TLVMsg::V1(v))
        },
        MsgTy::TYPE2 => {
            let (n, v) = Fixed::<10>.parse(&rest)?;
            (n, TLVMsg::V2(v))
        },
        MsgTy::TYPE3 => {
            let (n, v) = Tail.parse(&rest)?;
            (n, TLVMsg::V3(v)
        },
        MsgTy::TYPE4 => {
            let (n, v) = Tail.parse(&rest)?;
            (n, TLVMsg::V4(v)
        },
    };
    Ok((n, payload))
}
}

impl<'i> Serializer<&TLVMsg<'i>> for TLVPayloadFmt {
fn ex_serialize(&self, v: &TLVMsg<'i>, obuf: &mut Vec<u8>) {
    match (self.tag, v) {
        (MsgTy::TYPE1, TLVMsg::V1(v))=> U8.ex_serialize(*v, obuf),
        (MsgTy::TYPE2, TLVMsg::V2(v))=> Fixed::<10>.ex_serialize(*v, obuf),
        (MsgTy::TYPE3, TLVMsg::V3(v)) => Tail.ex_serialize((*v, obuf),
        (MsgTy::TYPE4, TLVMsg::V4(v)) => Tail.ex_serialize((*v, obuf),
        _ => {},
    }
}
}

impl<'i> Prepare<&TLVMsg<'i>> for TLVPayloadFmt {
fn prepare(&self, v: &TLVMsg<'i>) -> Result<usize, PreSerializeError> {
    match (self.tag, v) {
        (MsgTy::TYPE1, TLVMsg::V1(v)) => U8.prepare(*v),
        (MsgTy::TYPE2, TLVMsg::V2(v)) => Fixed::<10>.prepare(*v),
        (MsgTy::TYPE3, TLVMsg::V3(v)) => Tail.prepare(*v),
        (MsgTy::TYPE4, TLVMsg::V4(v)) => Tail.prepare(*v),
        _ => Err(PreSerializeError::NotCompliant(ComplianceErrorKind::InvalidTag)),
    }
}
}
```
