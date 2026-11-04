import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.Amd64.UdivremA
import Fv256.Amd64.UdivremI
import Fv256.Amd64.UdivremK

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.UdivremA

namespace Fv256.Amd64.UdivremL

set_option maxHeartbeats 8000000 in
/-- `udivrem(quot, u, d, nil)`: only the quotient is produced. -/
theorem udivrem_nil {L : Nat} (hL : L ≤ 8) :
    Summary Extracted.program ku
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x150 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0xf8 ∧ StackWritable s 0x148 0x48 ∧ s.xmm 15 = 0 ∧
        (s.regs 6).toNat = L ∧ (s.regs 3).toNat = L ∧
        Buffer s (s.regs 0) (8 * L) true ∧ Buffer s (s.regs 7) (8 * L) false ∧ Buffer s (s.regs 9) 32 false ∧
        ((s.regs 0).toNat + 8 * L ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 8 * L ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 7).toNat) ∧
        ((s.regs 9).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 9).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 14).toNat + 16) ∧
        Fv256.B.wv s.mem (s.regs 9).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧ (s.regs 10).toNat = 0)
      (fun s s' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory) (kr : Nat → W64),
        s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8 else if i = 5 then s.regs 5 else if i = 14 then s.regs 14 else R' i,
                      rip := retAddrOf s, flags := fl', xmm := fun i => if i = 15 then s.xmm 15 else X' i, mem := M', kreg := kr } ∧
        Fv256.B.wv M' (s.regs 0).toNat L = Fv256.B.wv s.mem (s.regs 7).toNat L / Fv256.B.wv s.mem (s.regs 9).toNat 4 ∧
        MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)]) := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hr⟩
  refine Fv256.B.reachesRet_mono64 (Fv256.Amd64.UdivremK.udivrem_summary hL s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, fun h => absurd hr h⟩) ?_
  rintro S ⟨R', fl', X', M', kr, hS, hq, hrm, hf0, hf1⟩
  exact ⟨R', fl', X', M', kr, hS, hq, hf0 hr⟩

set_option maxHeartbeats 8000000 in
/-- `udivrem(quot, u, d, rem)` with a non-nil `rem`. -/
theorem udivrem_rem {L : Nat} (hL : L ≤ 8) :
    Summary Extracted.program ku
      (fun s => (s.mem.accessible (s.regs 4).toNat 8 false = true ∧ s.mem.readLE (s.regs 4).toNat 8 < 2 ^ 47) ∧
        0x150 ≤ (s.regs 4).toNat ∧ StackGuardOK s 0xf8 ∧ StackWritable s 0x148 0x48 ∧ s.xmm 15 = 0 ∧
        (s.regs 6).toNat = L ∧ (s.regs 3).toNat = L ∧
        Buffer s (s.regs 0) (8 * L) true ∧ Buffer s (s.regs 7) (8 * L) false ∧ Buffer s (s.regs 9) 32 false ∧
        ((s.regs 0).toNat + 8 * L ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 0).toNat) ∧
        ((s.regs 7).toNat + 8 * L ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 7).toNat) ∧
        ((s.regs 9).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 9).toNat) ∧
        ((s.regs 14).toNat + 24 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 14).toNat + 16) ∧
        Fv256.B.wv s.mem (s.regs 9).toNat 4 ≠ 0 ∧ Fv256.B.wv s.mem (s.regs 0).toNat L = 0 ∧
        (s.regs 10).toNat ≠ 0 ∧ Buffer s (s.regs 10) 32 true ∧ Fv256.B.wv s.mem (s.regs 10).toNat 4 = 0 ∧
          ((s.regs 0).toNat + 8 * L ≤ (s.regs 10).toNat ∨ (s.regs 10).toNat + 32 ≤ (s.regs 0).toNat) ∧
          ((s.regs 10).toNat + 32 ≤ (s.regs 7).toNat ∨ (s.regs 7).toNat + 8 * L ≤ (s.regs 10).toNat) ∧
          ((s.regs 10).toNat + 32 ≤ (s.regs 4).toNat - 0x148 ∨ (s.regs 4).toNat + 0x48 ≤ (s.regs 10).toNat))
      (fun s s' => ∃ (R' : Nat → W64) (fl' : Flags) (X' : Nat → BitVec 128) (M' : Memory) (kr : Nat → W64),
        s' = { s with regs := fun i => if i = 4 then s.regs 4 + 8 else if i = 5 then s.regs 5 else if i = 14 then s.regs 14 else R' i,
                      rip := retAddrOf s, flags := fl', xmm := fun i => if i = 15 then s.xmm 15 else X' i, mem := M', kreg := kr } ∧
        Fv256.B.wv M' (s.regs 0).toNat L = Fv256.B.wv s.mem (s.regs 7).toNat L / Fv256.B.wv s.mem (s.regs 9).toNat 4 ∧
        Fv256.B.wv M' (s.regs 10).toNat 4 = Fv256.B.wv s.mem (s.regs 7).toNat L % Fv256.B.wv s.mem (s.regs 9).toNat 4 ∧
        MemFrame s.mem M' [((s.regs 0).toNat, (s.regs 0).toNat + 8 * L), ((s.regs 10).toNat, (s.regs 10).toNat + 32),
          ((s.regs 4).toNat - 0x148, (s.regs 4).toNat), ((s.regs 4).toNat + 8, (s.regs 4).toNat + 0x48)]) := by
  intro s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, hr, hb, hz, d1, d2, d3⟩
  refine Fv256.B.reachesRet_mono64 (Fv256.Amd64.UdivremK.udivrem_summary hL s hpc ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, fun _ => ⟨hb, hz, d1, d2, d3⟩⟩) ?_
  rintro S ⟨R', fl', X', M', kr, hS, hq, hrm, hf0, hf1⟩
  exact ⟨R', fl', X', M', kr, hS, hq, hrm hr, hf1 hr⟩

end Fv256.Amd64.UdivremL
