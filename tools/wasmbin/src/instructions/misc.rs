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

use crate::indices::{DataId, ElemId, MemId, TableId};
use crate::io::Wasmbin;
use crate::visit::Visit;
use arbitrary::Arbitrary;

#[crate::wasmbin_discriminants]
#[derive(Wasmbin, Debug, Arbitrary, PartialEq, Eq, Hash, Clone, Visit)]
#[repr(u32)]
pub enum Misc {
    I32TruncSatF32S = 0x00,
    I32TruncSatF32U = 0x01,
    I32TruncSatF64S = 0x02,
    I32TruncSatF64U = 0x03,
    I64TruncSatF32S = 0x04,
    I64TruncSatF32U = 0x05,
    I64TruncSatF64S = 0x06,
    I64TruncSatF64U = 0x07,
    MemoryInit { data: DataId, mem: MemId } = 0x08,
    DataDrop(DataId) = 0x09,
    MemoryCopy { dest: MemId, src: MemId } = 0x0A,
    MemoryFill(MemId) = 0x0B,
    TableInit { elem: ElemId, table: TableId } = 0x0C,
    ElemDrop(ElemId) = 0x0D,
    TableCopy { dest: TableId, src: TableId } = 0x0E,
    TableGrow(TableId) = 0x0F,
    TableSize(TableId) = 0x10,
    TableFill(TableId) = 0x11,
}
