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

use crate::io::{Decode, DecodeError, Encode, Wasmbin};
use crate::visit::Visit;
use arbitrary::Arbitrary;

/// A wrapper around floats that treats `NaN`s as equal.
///
/// This is useful in instruction context, where we don't care
/// about general floating number rules.
#[derive(Wasmbin, Debug, Arbitrary, Clone, Visit)]
pub struct FloatConst<F> {
    pub value: F,
}

impl<F> Eq for FloatConst<F> where Self: PartialEq {}

macro_rules! def_float {
    ($ty:ident) => {
        impl Encode for $ty {
            fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
                self.to_le_bytes().encode(w)
            }
        }

        impl Decode for $ty {
            fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
                Decode::decode(r).map($ty::from_le_bytes)
            }
        }

        impl Visit for $ty {}

        impl PartialEq for FloatConst<$ty> {
            fn eq(&self, other: &Self) -> bool {
                self.value == other.value || self.value.is_nan() && other.value.is_nan()
            }
        }

        impl std::hash::Hash for FloatConst<$ty> {
            fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
                h.write(&self.value.to_ne_bytes())
            }
        }
    };
}

def_float!(f32);
def_float!(f64);
