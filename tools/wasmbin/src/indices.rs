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

use crate::builtins::WasmbinCountable;
use crate::io::Wasmbin;
use crate::visit::Visit;
use arbitrary::Arbitrary;

macro_rules! newtype_id {
    ($name:ident) => {
        #[derive(PartialEq, Eq, Clone, Copy, Wasmbin, WasmbinCountable, Arbitrary, Hash, Visit)]
        #[repr(transparent)]
        pub struct $name {
            pub index: u32,
        }

        impl From<u32> for $name {
            fn from(index: u32) -> Self {
                Self { index }
            }
        }

        impl From<$name> for u32 {
            fn from(id: $name) -> u32 {
                id.index
            }
        }

        impl std::fmt::Debug for $name {
            fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
                write!(
                    f,
                    "{}#{}",
                    &stringify!($name)[..stringify!($name).len() - "Id".len()],
                    self.index
                )
            }
        }
    };
}

newtype_id!(DataId);
newtype_id!(ElemId);
newtype_id!(FuncId);
newtype_id!(GlobalId);
newtype_id!(LabelId);
newtype_id!(LocalId);
newtype_id!(MemId);
newtype_id!(TableId);
newtype_id!(TypeId);
