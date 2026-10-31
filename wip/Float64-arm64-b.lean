import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

set_option Elab.async false in
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem correctness (x : BitVec 64) :
    Ensures Extracted.program Extracted.entry [x]
      (fun s => Ptr32 s.mem x false ∧ GuardOK s 0 ∧ StackOK s 88 0 ∧ Disjoint x.toNat 32 (s.sp.toNat - 88) 88 ∧ s.fpcr = 0)
      (fun s s' => s'.getV 0 64 = Fv256.B.float64Bits (val256 s.mem x.toNat) ∧
        OnlyWrites s.mem s'.mem (s.sp.toNat - 88) 88) := by
  intro ret hret s hs ⟨⟨hx, hx'⟩, ⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hdis, hf⟩
  janus_intro hs
  simp only [Disjoint] at hdis
  have c0 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem x.toNat)
  have c1 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem (x.toNat + 8))
  have c2 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem (x.toNat + 16))
  have c3 := Fv256.B.clz_cases _ (Fv256.Util.readLE8_lt s.mem (x.toNat + 24))
  have hor : (s.mem.readLE (x.toNat + 16) 8 ||| s.mem.readLE (x.toNat + 8) 8 ||| s.mem.readLE (x.toNat + 24) 8 = 0) ↔
      (s.mem.readLE (x.toNat + 16) 8 = 0 ∧ s.mem.readLE (x.toNat + 8) 8 = 0 ∧ s.mem.readLE (x.toNat + 24) 8 = 0) := by
    simp [Nat.or_eq_zero_iff, and_assoc]
  by_cases h3 : s.mem.readLE (x.toNat + 24) 8 = 0
  · sorry
  · obtain ⟨k3, hk3⟩ : ∃ k, Janus.Arm64.clzNat 64 (s.mem.readLE (x.toNat + 24) 8) = k := ⟨_, rfl⟩
    have hk3' : k3 < 64 := by
      rcases c3 with h | h
      · exact absurd h h3
      · rw [hk3] at h; exact h
    janus_run [hf, hor, h3, hk3] until [segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh"]
    generalize hN : (257#64 - (64#64 - BitVec.ofNat 64 k3 + 192#64)) = N at *
    have hNk : N.toNat = 1 + k3 := by
      have := congrArg BitVec.toNat hN
      simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat] at this
      omega
    janus_run [hNk] until [Extracted.entry + 0xa8]
    all_goals (first | (
      generalize hA3 : (s.mem.readLE (x.toNat + 24) 8 * 2 ^ ((1 + k3) % 64) % 18446744073709551616 |||
                      (BitVec.ofNat 64 (s.mem.readLE (x.toNat + 16) 8) >>>
                          ((18446744073709551616 - (1 + k3) - 18446744073709551552) % 64)).toNat) = A3
      generalize hA2 : (s.mem.readLE (x.toNat + 16) 8 * 2 ^ ((1 + k3) % 64) % 18446744073709551616 |||
                          (BitVec.ofNat 64 (s.mem.readLE (x.toNat + 8) 8) >>>
                              ((18446744073709551616 - (1 + k3) - 18446744073709551552) % 64)).toNat) = A2
      generalize hA1 : (s.mem.readLE (x.toNat + 8) 8 * 2 ^ ((1 + k3) % 64) % 18446744073709551616 |||
                  (BitVec.ofNat 64 (s.mem.readLE x.toNat 8) >>>
                      ((18446744073709551616 - (1 + k3) - 18446744073709551552) % 64)).toNat) = A1
      generalize hA0 : s.mem.readLE x.toNat 8 * 2 ^ ((1 + k3) % 64) = A0
      simp (disch := omega) only [Janus.Tactic.writeLE_comm, Fv256.B.writeLE_same]
      trace_state
      janus_run
      all_goals sorry) | sorry)

    all_goals sorry

end Fv256.Arm64.Float64
