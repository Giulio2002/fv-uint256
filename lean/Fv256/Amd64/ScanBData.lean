import Extracted

/-!
# `Scan` (amd64): the rodata facts the type switch reads (type hash words, disjointness from writable ranges)
-/
open Janus Janus.Amd64 Janus.Amd64.Tactic

namespace Fv256.Amd64.ScanBData

set_option maxRecDepth 100000 in
theorem hashS (m : Janus.Arm64.Memory) (hdl : Extracted.program.DataLoaded m) :
    m.readLE (Extracted.dataAddr.«type:string#f88732b8» + 16) 4 = 0xf88732b8 :=
  readLE_of_dataRead hdl (by decide)

set_option maxRecDepth 100000 in
theorem hashB (m : Janus.Arm64.Memory) (hdl : Extracted.program.DataLoaded m) :
    m.readLE (Extracted.dataAddr.«type:[]uint8#7efbbf65» + 16) 4 = 0x7efbbf65 :=
  readLE_of_dataRead hdl (by decide)

set_option maxRecDepth 100000 in
theorem aprtS (m : Janus.Arm64.Memory) (hdl : Extracted.program.DataLoaded m) {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ 5008128 ∨ 5008128 + 384 ≤ a :=
  disjoint_of_dataLoaded' hdl 1 (base := 5008128) (len := 384) (by decide) hw

set_option maxRecDepth 100000 in
theorem aprtB (m : Janus.Arm64.Memory) (hdl : Extracted.program.DataLoaded m) {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ 5002336 ∨ 5002336 + 256 ≤ a :=
  disjoint_of_dataLoaded' hdl 0 (base := 5002336) (len := 256) (by decide) hw

set_option maxRecDepth 100000 in
theorem accS (m : Janus.Arm64.Memory) (hdl : Extracted.program.DataLoaded m) :
    m.accessible (Extracted.dataAddr.«type:string#f88732b8» + 16) 4 false = true := by
  have h := accessible_of_dataLoaded hdl 1 (by decide)
  have e1 : (Extracted.program.data[1]'(by decide)).base = 5008128 := by decide
  have e2 : (Extracted.program.data[1]'(by decide)).bytes.length = 384 := by decide
  rw [e1, e2] at h
  exact Janus.Arm64.Memory.accessible_sub m h (Or.inl rfl) (by decide) (by decide)

set_option maxRecDepth 100000 in
theorem accB (m : Janus.Arm64.Memory) (hdl : Extracted.program.DataLoaded m) :
    m.accessible (Extracted.dataAddr.«type:[]uint8#7efbbf65» + 16) 4 false = true := by
  have h := accessible_of_dataLoaded hdl 0 (by decide)
  have e1 : (Extracted.program.data[0]'(by decide)).base = 5002336 := by decide
  have e2 : (Extracted.program.data[0]'(by decide)).bytes.length = 256 := by decide
  rw [e1, e2] at h
  exact Janus.Arm64.Memory.accessible_sub m h (Or.inl rfl) (by decide) (by decide)

end Fv256.Amd64.ScanBData
