//! This module re-exports the most commonly used items from Vest.
//!
//! `use vest_lib::prelude::*;` would include the Verus prelude, Vest's executable,
//! specification and proof traits, as well as its format combinators.
//!
//! In addition, some basic length and bytes-view broadcast lemmas are enabled automatically when
//! `vest_lib` is imported.
pub use crate::combinators::*;
pub use crate::core::exec::{
    ByteLen, InputBuf, InputSlice, OutputBuf, OutputSlice, PResult, ParseError, ParseErrorKind,
    Parser, PreSerializeError, Prepare, Serializer, SerializerExt,
};
pub use crate::core::{proof::*, spec::*};
pub use vstd::prelude::*;

#[cfg(verus_keep_ghost)]
pub use crate::combinators::star::spec::lemma_star_static_byte_len;
#[cfg(feature = "alloc")]
use alloc::vec::Vec;

verus! {

/// Byte slices have the same shallow and deep views.
pub broadcast proof fn lemma_byte_slice_view(bytes: &[u8])
    ensures
        #[trigger] bytes.deep_view() == bytes@,
{
    assert(bytes.deep_view() =~= bytes@);
}

/// Fixed byte arrays have the same shallow and deep views.
pub broadcast proof fn lemma_byte_array_view<const N: usize>(bytes: &[u8; N])
    ensures
        #[trigger] bytes.deep_view() == bytes@,
{
    assert(bytes.deep_view() =~= bytes@);
}

/// Identity-view elements give a vector the same shallow and deep views.
#[cfg(feature = "alloc")]
pub broadcast proof fn lemma_identity_vec_view<T: DeepView<V = T>>(values: &Vec<T>)
    requires
        forall|item: T| #[trigger] item.deep_view() == item,
    ensures
        #[trigger] values.deep_view() == values@,
{
    assert(values.deep_view() =~= values@);
}

#[cfg_attr(verus_keep_ghost, verifier::broadcast_use_by_default_when_this_crate_is_imported)]
pub broadcast group basic_lemmas {
    StaticByteLen::lemma_static_len_matches_byte_len,
    GoodSerializer::lemma_serialize_len,
    lemma_star_static_byte_len,
    lemma_byte_slice_view,
    lemma_byte_array_view,
    #[cfg(feature = "alloc")]
    lemma_identity_vec_view,
}

/// Opt-in parser facts: consumed bounds, consistent values, and exact byte lengths.
pub broadcast group parser_lemmas {
    SafeParser::lemma_parse_safe,
    SoundParser::lemma_parse_sound_consumption,
    SoundParser::lemma_parse_sound_value,
}

} // verus!
