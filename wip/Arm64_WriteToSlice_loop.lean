import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToSlice

abbrev head : Nat := Extracted.entry + 0x44

/-- memory after the prologue spills -/
def M₀ (s : State) (d : BitVec 64) (ret : Nat) : Memory :=
  ((s.mem.writeLE (s.sp.toNat - 16) 8 ret).writeLE (s.sp.toNat - 24) 8 (s.regs 29).toNat).writeLE (s.sp.toNat + 16) 8 d.toNat

theorem wtsA (s : State) (d z : BitVec 64) (ret n len : Nat) (i : Nat)
    (hz : s.mem.accessible z.toNat 32 false = true)
    (hw : s.mem.accessible (s.sp.toNat - 24) (24 + 24) true = true)
    (hd : s.mem.accessible d.toNat len true = true) :
    (Util.wts (M₀ s d ret) d.toNat (n - 1) (fun j => s.mem.readLE (z.toNat + 8 * j) 8) i).accessible z.toNat 32 false = true ∧ (Util.wts (M₀ s d ret) d.toNat (n - 1) (fun j => s.mem.readLE (z.toNat + 8 * j) 8) i).accessible (s.sp.toNat - 24) (24 + 24) true = true ∧
      (Util.wts (M₀ s d ret) d.toNat (n - 1) (fun j => s.mem.readLE (z.toNat + 8 * j) 8) i).accessible d.toNat len true = true := by
  simp only [Util.wts_acc, M₀, Janus.Arm64.Memory.accessible_writeLE]
  exact ⟨hz, hw, hd⟩

set_option maxHeartbeats 16000000 in
theorem loop (z d len : BitVec 64) (ret : Nat) (hret : RetAddr Extracted.program ret) (s : State)
    (n : Nat) (E : BitVec 64) (hE : E.toInt = (n : Int) - 1) (hn32 : n ≤ 32) (hnl : n ≤ len.toNat)
    (hz : s.mem.accessible z.toNat 32 false = true) (hz' : z.toNat + 32 ≤ 2 ^ 48)
    (hd : s.mem.accessible d.toNat len.toNat true = true) (hd' : d.toNat + len.toNat ≤ 2 ^ 48)
    (hzd : z.toNat + 32 ≤ d.toNat ∨ d.toNat + len.toNat ≤ z.toNat)
    (hzs : z.toNat + 32 ≤ s.sp.toNat - 24 ∨ s.sp.toNat - 24 + 48 ≤ z.toNat)
    (hds : d.toNat + len.toNat ≤ s.sp.toNat - 24 ∨ s.sp.toNat - 24 + 48 ≤ d.toNat)
    (hb : 24 ≤ s.sp.toNat) (hl : len.toNat < 2 ^ 48)
    (hw : s.mem.accessible (s.sp.toNat - 24) (24 + 24) true = true)
    (sp0 : BitVec 64) (hsp0 : sp0.toNat = s.sp.toNat - 16) :
    ∀ k (S : State) (i : BitVec 64), i.toNat + k = n →
      S.pc = BitVec.ofNat 64 head → S.regs 0 = z → S.regs 1 = d → S.regs 2 = len → S.regs 3 = E → S.regs 4 = i →
      S.regs 30 = BitVec.ofNat 64 ret → S.sp = sp0 → S.regs 28 = s.regs 28 →
      S.regs 29 = s.sp - 24#64 → S.regs 18 = s.regs 18 →
      S.mem = Util.wts (M₀ s d ret) d.toNat (n - 1) (fun j => s.mem.readLE (z.toNat + 8 * j) 8) i.toNat →
      Reaches (Extracted.program.withExit ret) S (IsReturn fun s' => ABIReturn s s' ∧
        s'.mem = Util.wts (M₀ s d ret) d.toNat (n - 1) (fun j => s.mem.readLE (z.toNat + 8 * j) 8) n) := by
  intro k
  induction k with
  | zero =>
    intro S i hk hpc h0 h1 h2 h3 h4 h30 hsp h28 h29 h18 hm
    obtain ⟨a1, a2, a3⟩ := wtsA s d z ret n len.toNat i.toNat hz hw hd
    have e16 : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; have := s.sp.isLt; omega
    have e24 : (s.sp - 24#64).toNat = s.sp.toNat - 24 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; have := s.sp.isLt; omega
    have eS : S.sp.toNat = s.sp.toNat - 16 := by rw [hsp, hsp0]
    have q1 : 8 ≤ S.sp.toNat := by omega
    have a4 : (Util.wts (M₀ s d ret) d.toNat (n - 1) (fun j => s.mem.readLE (z.toNat + 8 * j) 8) i.toNat).accessible (S.sp.toNat - 8) 8 true = true := by
      rw [Util.wts_acc]; simp only [M₀, Janus.Arm64.Memory.accessible_writeLE]; exact Janus.Arm64.Memory.accessible_mono _ hw (by omega) (by omega)
    janus_run [Util.wts_acc]
    trace_state
    all_goals sorry
  | succ k ih =>
    intro S i hk hpc h0 h1 h2 h3 h4 h30 hsp h28 h29 h18 hm
    obtain ⟨a1, a2, a3⟩ := wtsA s d z ret n len.toNat i.toNat hz hw hd
    have e16 : (s.sp - 16#64).toNat = s.sp.toNat - 16 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; have := s.sp.isLt; omega
    have e24 : (s.sp - 24#64).toNat = s.sp.toNat - 24 := by
      rw [BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; have := s.sp.isLt; omega
    janus_run [Util.wts_acc] until [head]
    all_goals (try (rw [Util.sdiv8 i (by omega)] at hbr; omega))
    trace_state
    all_goals sorry

end Fv256.Arm64.WriteToSlice
