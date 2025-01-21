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

use crate::builtins::{Lazy, WasmbinCountable};
use crate::io::{Decode, DecodeError, DecodeErrorKind, Encode};
use crate::visit::Visit;
use arbitrary::Arbitrary;

#[derive(Debug, Arbitrary, PartialEq, Eq, Hash, Clone, Visit)]
pub struct RawBlob<T = Vec<u8>> {
    pub contents: T,
}

impl<T: AsRef<[u8]>> Encode for RawBlob<T> {
    fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        let bytes = self.contents.as_ref();
        bytes.len().encode(w)?;
        bytes.encode(w)
    }
}

impl<T: Decode> Decode for RawBlob<T> {
    fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
        let size = u32::decode(r)?;
        let mut taken = std::io::Read::take(r, size.into());
        let contents = T::decode(&mut taken)?;
        if taken.limit() != 0 {
            return Err(DecodeErrorKind::UnrecognizedData.into());
        }
        Ok(RawBlob { contents })
    }
}

impl<T: AsRef<[u8]>> AsRef<[u8]> for RawBlob<T> {
    fn as_ref(&self) -> &[u8] {
        self.contents.as_ref()
    }
}

#[derive(Default, Arbitrary, PartialEq, Eq, Hash, Clone, Visit)]
pub struct Blob<T: Decode> {
    contents: Lazy<T>,
}

impl<T: Decode> Blob<T> {
    pub fn try_contents(&self) -> Result<&T, DecodeError> {
        self.contents.try_contents()
    }

    pub fn try_contents_mut(&mut self) -> Result<&mut T, DecodeError> {
        self.contents.try_contents_mut()
    }

    pub fn try_into_contents(self) -> Result<T, DecodeError> {
        self.contents.try_into_contents()
    }
}

impl<T: Decode + std::fmt::Debug> std::fmt::Debug for Blob<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.write_str("Blob(")?;
        self.contents.fmt(f)?;
        f.write_str(")")
    }
}

impl<T: Decode + Encode> Encode for Blob<T> {
    fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        let value = match self.contents.try_as_raw() {
            Ok(raw) => return RawBlob { contents: raw }.encode(w),
            Err(value) => value,
        };
        let mut buf;
        buf = Vec::new();
        value.encode(&mut buf)?;
        RawBlob { contents: buf }.encode(w)
    }
}

impl<T: Decode> Decode for Blob<T> {
    fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
        let contents: Lazy<T> = RawBlob::decode(r)?.contents;
        Ok(Self { contents })
    }
}

impl<T: Decode + WasmbinCountable> WasmbinCountable for Blob<T> {}

impl<T: Decode> From<T> for Blob<T> {
    fn from(value: T) -> Self {
        Blob {
            contents: value.into(),
        }
    }
}
