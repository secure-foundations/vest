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

use crate::io::{Decode, DecodeError, DecodeErrorKind, Encode};
use crate::visit::Visit;
use std::convert::TryFrom;

macro_rules! def_byte_array {
    ($count:literal) => {
        impl Encode for [u8; $count] {
            fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
                w.write_all(self)
            }
        }

        impl Decode for [u8; $count] {
            fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
                let mut dest = [0_u8; $count];
                r.read_exact(&mut dest)?;
                Ok(dest)
            }
        }
    };
}

def_byte_array!(4);
def_byte_array!(8);
def_byte_array!(16);

impl Encode for u8 {
    fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        std::slice::from_ref(self).encode(w)
    }
}

impl Encode for [u8] {
    fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        w.write_all(self)
    }
}

impl Decode for u8 {
    fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
        let mut dest = 0;
        r.read_exact(std::slice::from_mut(&mut dest))?;
        Ok(dest)
    }
}

impl Decode for Option<u8> {
    fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
        let mut dest = 0;
        loop {
            return match r.read(std::slice::from_mut(&mut dest)) {
                Ok(0) => Ok(None),
                Ok(_) => Ok(Some(dest)),
                Err(err) if err.kind() == std::io::ErrorKind::Interrupted => continue,
                Err(err) => Err(DecodeErrorKind::Io(err).into()),
            };
        }
    }
}

impl Decode for Vec<u8> {
    fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
        let mut dest = Vec::new();
        r.read_to_end(&mut dest)?;
        Ok(dest)
    }
}

impl Visit for u8 {}

macro_rules! def_integer {
    ($ty:ident, $leb128_method:ident) => {
        impl Encode for $ty {
            fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
                leb128::write::$leb128_method(w, (*self).into()).map(|_| ())
            }
        }

        impl Decode for $ty {
            fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
                const LIMIT: u64 = (std::mem::size_of::<$ty>() * 8 / 7) as u64 + 1;

                let mut r = std::io::Read::take(r, LIMIT);
                let as_64 = leb128::read::$leb128_method(&mut r)?;
                let res = Self::try_from(as_64)?;

                Ok(res)
            }
        }

        impl Visit for $ty {}
    };
}

def_integer!(u32, unsigned);
def_integer!(i32, signed);
def_integer!(u64, unsigned);
def_integer!(i64, signed);

impl Encode for usize {
    fn encode(&self, w: &mut impl std::io::Write) -> std::io::Result<()> {
        match u32::try_from(*self) {
            Ok(v) => v.encode(w),
            Err(err) => Err(std::io::Error::new(std::io::ErrorKind::InvalidData, err)),
        }
    }
}

impl Decode for usize {
    fn decode(r: &mut impl std::io::Read) -> Result<Self, DecodeError> {
        Ok(usize::try_from(u32::decode(r)?)?)
    }
}

impl Visit for usize {}
