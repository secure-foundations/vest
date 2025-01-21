// Copyright 2020 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use crate::builtins::Blob;
use crate::io::{Decode, DecodeError, DecodeErrorKind, Encode, Wasmbin};
use crate::sections::{Section, StdPayload};
use crate::visit::Visit;
use arbitrary::Arbitrary;
use std::cmp::Ordering;

const MAGIC_AND_VERSION: [u8; 8] = [b'\0', b'a', b's', b'm', 0x01, 0x00, 0x00, 0x00];

#[derive(Debug, Default, Arbitrary, PartialEq, Eq, Hash, Clone, Visit)]
pub struct MagicAndVersion;

encode_decode_as!(MagicAndVersion, {
    MagicAndVersion <=> MAGIC_AND_VERSION,
}, |actual| {
    Err(DecodeErrorKind::InvalidMagic { actual }.into())
});

#[derive(Wasmbin, Debug, Default, Arbitrary, PartialEq, Eq, Hash, Clone, Visit)]
pub struct Module {
    #[doc(hidden)]
    pub magic_and_version: MagicAndVersion,
    pub sections: Vec<Section>,
}

impl Module {
    pub fn decode_from(mut r: impl std::io::Read) -> Result<Module, DecodeError> {
        Self::decode(&mut r)
    }

    pub fn encode_into<W: std::io::Write>(&self, mut w: W) -> std::io::Result<W> {
        self.encode(&mut w)?;
        Ok(w)
    }

    pub fn find_std_section<T: StdPayload>(&self) -> Option<&Blob<T>> {
        self.sections.iter().find_map(Section::try_as)
    }

    pub fn find_std_section_mut<T: StdPayload>(&mut self) -> Option<&mut Blob<T>> {
        self.sections.iter_mut().find_map(Section::try_as_mut)
    }

    pub fn find_or_insert_std_section<T: StdPayload>(
        &mut self,
        insert_callback: impl FnOnce() -> T,
    ) -> &mut Blob<T> {
        let mut index = self.sections.len();
        let mut insert = true;
        for (i, section) in self.sections.iter_mut().enumerate() {
            match section.kind().cmp(&T::KIND) {
                Ordering::Less => continue,
                Ordering::Equal => {
                    // We can't just `return` here due to a bug in rustc:
                    // https://github.com/rust-lang/rust/issues/70255
                    insert = false;
                }
                Ordering::Greater => {}
            }
            index = i;
            break;
        }
        if insert {
            self.sections.insert(index, insert_callback().into());
        }
        unsafe { self.sections.get_unchecked_mut(index) }
            .try_as_mut()
            .unwrap_or_else(|| unsafe { std::hint::unreachable_unchecked() })
    }
}
