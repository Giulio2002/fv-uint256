import Janus
import Fv256.IbsProg64
import Fv256.IndexByteSpec
import Fv256.IbsMath
import Fv256.IbsAlign
import Fv256.IbsVec64
import Fv256.IbsSynd
/-!
# `internal/bytealg.IndexByteString` (arm64): library summary over `Fv256.IbsProg64.program`

Extracted-free.  `ibs_summary_64` proves `IbsSummary64 IbsProg64.program 0x11f10 p n c` for every `p n c`: `X0` holds `indexOfNat`, memory, `SP`,
`X18`, `X28`, `X29`, `X30` unchanged.  The code scans 32-byte aligned blocks with two bits of syndrome per byte: an unaligned head block masked by
`LSR`/`LSL`, the loop `loop64` (invariant `FT s.mem p c d = d`: no match in the `d` bytes scanned so far, `x3 = p + d` aligned) and a tail block masked by
`LSL`/`LSR`.  Syndrome / mask calculus in `IbsSynd`, window results in `win_ft`.
-/
open Janus Janus.Arm64 Janus.Tactic
namespace Fv256.IndexByte
open Fv256.IndexByte64
open Fv256.IndexByte

/-- invariant at the loop head `0x11f74` of `IndexByteString`: `d` bytes consumed, `x3 = p + d` -/
def LoopInv (s t : State) (p n : BitVec 64) (c d : Nat) : Prop :=
  t.mem = s.mem ∧ t.sp = s.sp ∧ t.regs 3 = p + BitVec.ofNat 64 d ∧ t.regs 1 = n - BitVec.ofNat 64 d ∧
  t.regs 5 = 1074791425#64 ∧ t.regs 9 = BitVec.ofNat 64 (p.toNat % 32) ∧ t.regs 10 = BitVec.ofNat 64 (n.toNat % 32) ∧
  t.regs 11 = p ∧ t.regs 18 = s.regs 18 ∧ t.regs 28 = s.regs 28 ∧ t.regs 29 = s.regs 29 ∧ t.regs 30 = s.regs 30 ∧
  t.vregs 0 = BitVec.ofNat 128 ((ofElems 8 16 fun _ => BitVec.toNat (s.regs 2)) % 340282366920938463463374607431768211456) ∧
  t.vregs 5 = BitVec.ofNat 128 ((ofElems 32 4 fun _ => 1074791425) % 340282366920938463463374607431768211456) ∧
  FT s.mem p.toNat c d = d ∧ (p.toNat + d) % 32 = 0 ∧ d < n.toNat ∧ (0 < d ∨ p.toNat % 32 = 0)

set_option maxRecDepth 100000 in
theorem loop64 (p n : BitVec 64) (c : Nat) (s : State) (hpre : IbsPre64 p n c s) (hc : (s.regs 2).toNat % 256 = c % 256) (hn : 0 < n.toNat) :
    ∀ k, ∀ (t : State) d, n.toNat - d = k → t.pc = BitVec.ofNat 64 0x11f74 → LoopInv s t p n c d →
      ReachesRet Fv256.IbsProg64.program (s.regs GoABI.regLR) t (IbsPost64 p n c s) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro t d hk hpc hinv
  obtain ⟨h0, h1, h2, h30a, h30b, hpr⟩ := hpre
  obtain ⟨hm, hsp, h3, h1t, h5, h9, h10, h11, h18, h28, h29, h30, hv0, hv5, hft, hal, hdn, hd0⟩ := hinv
  obtain ⟨hend, hacc2⟩ := hpr.resolve_left (by omega)
  have hn48 : n.toNat ≤ 2 ^ 48 := by omega
  have hp48 : p.toNat < 2 ^ 48 := by omega
  janus_run [hv0, hv5, BitVec.toNat_ofNat, Nat.mod_mod] until [0x11f74]
  all_goals simp only [loopTest, syndrome] at *
  all_goals
    have hSb : synd (blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2))) 32
        = synd (bp s.mem (p.toNat + d) c) 32 := synd_blk_bp s.mem _ _ _ _ (by omega) h2
  · -- r = 32, no match
    have hF := none_full s.mem p.toNat d n.toNat c _ hft (by omega) rfl (by rw [← hSb]; exact hbr)
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      rw [BitVec.toNat_ofNat, idx_FT, hF, if_neg (Nat.lt_irrefl _)]
    all_goals simp [setReg, h18, h28, h29, h30]
  · -- r = 32, a match
    have hbr' : ¬ synd (bp s.mem (p.toNat + d) c) 32 = 0 := by rw [← hSb]; exact hbr
    obtain ⟨hct, hlt, hF⟩ := found_full s.mem p.toNat d n.toNat c _ hft (by omega) rfl hbr'
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      rw [← hSb] at hct
      rw [x0_found p d _ _ hct hlt (by omega), idx_FT, hF, if_pos (by omega)]
    all_goals simp [setReg, h18, h28, h29, h30]
  · -- r < 32, masked syndrome zero
    have hk : (n.toNat + p.toNat) % 32 = n.toNat - d := by omega
    have hS0 := synd_lt (blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2))) 32
    have he := tail_eval (synd (blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2))) 32)
      ((n.toNat + p.toNat) % 32) (by simpa using hS0) (by omega) (by omega)
    rw [he, hSb, hk] at hbr
    have hF := none_tail s.mem p.toNat d n.toNat c (n.toNat - d) _ hft (by omega) (by omega) rfl
      (by rw [← synd_tail_wf _ _ (by omega)]; exact hbr)
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      rw [BitVec.toNat_ofNat, idx_FT, hF, if_neg (Nat.lt_irrefl _)]
    all_goals simp [setReg, h18, h28, h29, h30]
  · -- r < 32, a match in the masked syndrome
    have hk : (n.toNat + p.toNat) % 32 = n.toNat - d := by omega
    have hS0 := synd_lt (blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2))) 32
    have he := tail_eval (synd (blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2))) 32)
      ((n.toNat + p.toNat) % 32) (by simpa using hS0) (by omega) (by omega)
    have hbr' : ¬ synd (wf 0 (n.toNat - d) (bp s.mem (p.toNat + d) c)) 32 = 0 := by
      rw [← synd_tail_wf _ _ (by omega), ← hk, ← hSb, ← he]; exact hbr
    obtain ⟨hct, hlt, hF⟩ := found_tail s.mem p.toNat d n.toNat c (n.toNat - d) _ hft (by omega) (by omega) rfl hbr'
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      rw [he, hSb, hk, synd_tail_wf _ _ (by omega)]
      rw [x0_found p d _ _ hct (by omega) (by omega), idx_FT, hF, if_pos (by omega)]
    all_goals simp [setReg, h18, h28, h29, h30]
  · -- r > 32, no match in the block: next round
    have hnone := (blk_none_iff s.mem _ _ _ c (by omega) h2).1 hbr
    have hft' : FT s.mem p.toNat c (d + 32) = d + 32 := by
      apply FT_clean s.mem p.toNat c d 32 hft
      show firstTrue (bp s.mem (p.toNat + d) c) 32 = 32
      rw [ft_eq_iff]; exact hnone
    refine ih (n.toNat - (d + 32)) (by omega) _ (d + 32) rfl rfl ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hft', by omega, by omega, by omega⟩
    · simp [hm]
    · simp [hsp]
    all_goals first | rfl | simp [setReg, setVReg, h5, h9, h10, h11, h18, h28, h29, h30, hv0, hv5]
  · -- r > 32, quick test hit but zero syndrome: impossible
    exfalso
    have hq : ¬ ∀ i < 32, blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2)) i = false := by janus_assumption
    apply hq
    intro i hi
    cases hf : blk (s.mem.readLE (p.toNat + d) 16) (s.mem.readLE (p.toNat + (d + 16)) 16) (BitVec.toNat (s.regs 2)) i
    · rfl
    · exact absurd hbr (synd_ne_zero _ _ ⟨i, hi, hf⟩)
  · -- r > 32, a match
    have hbr' : ¬ synd (bp s.mem (p.toNat + d) c) 32 = 0 := by rw [← hSb]; exact hbr
    obtain ⟨hct, hlt, hF⟩ := found_full s.mem p.toNat d n.toNat c _ hft (by omega) rfl hbr'
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
      rw [← hSb] at hct
      rw [x0_found p d _ _ hct hlt (by omega), idx_FT, hF, if_pos (by omega)]
    all_goals simp [setReg, h18, h28, h29, h30]

abbrev entry64 : Nat := 0x11f10

set_option maxRecDepth 100000 in
/-- the library summary of `internal/bytealg.IndexByteString` on arm64 -/
theorem ibs_summary_64 (p n : BitVec 64) (c : Nat) : IbsSummary64 Fv256.IbsProg64.program entry64 p n c := by
  intro s hpc hpre
  have hpre0 := hpre
  obtain ⟨h0, h1, h2, h30a, h30b, hpr⟩ := hpre
  by_cases hn0 : n.toNat = 0
  · have : n = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hn0)
    subst this
    janus_run
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
    · simp [setReg, indexOfNat]
    all_goals simp [setReg]
  · obtain ⟨hend, hacc2⟩ := hpr.resolve_left hn0
    have hn48 : n.toNat ≤ 2 ^ 48 := by omega
    have hp48 : p.toNat < 2 ^ 48 := by omega
    janus_run [bv_and31, bv_and_hi, nat_and31, nat_and_hi _ p.isLt] until [0x11f74]
    all_goals (try simp only [loopTest, syndrome] at *)
    all_goals
      have hSb : synd (blk (s.mem.readLE (p.toNat / 32 * 32) 16) (s.mem.readLE (p.toNat / 32 * 32 + 16) 16) (BitVec.toNat (s.regs 2))) 32
          = synd (bp s.mem (p.toNat / 32 * 32) c) 32 := synd_blk_bp s.mem _ _ _ _ rfl h2
      have hSlt := synd_lt (blk (s.mem.readLE (p.toNat / 32 * 32) 16) (s.mem.readLE (p.toNat / 32 * 32 + 16) 16) (BitVec.toNat (s.regs 2))) 32
      have hSlt' : synd (blk (s.mem.readLE (p.toNat / 32 * 32) 16) (s.mem.readLE (p.toNat / 32 * 32 + 16) 16) (BitVec.toNat (s.regs 2))) 32 < 2 ^ 64 := by simpa using hSlt
    · -- aligned: straight into the loop
      have ho0 : p.toNat % 32 = 0 := by janus_assumption
      refine loop64 p n c s hpre0 h2 (by omega) _ _ 0 rfl rfl ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, FT_zero _ _ _, by omega, by omega, Or.inr ho0⟩
      · apply BitVec.eq_of_toNat_eq
        simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
        rw [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_ofNat]
        have := p.isLt
        simp only [Nat.reducePow]
        omega
      all_goals simp [setReg, setVReg, h1]
    · -- the string ends in the first block: no match
      have ho1 : ¬ p.toNat % 32 = 0 := by janus_assumption
      have hls : (((addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.c && !(addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.z) = false) := by janus_assumption
      rw [ls_iff n _ (by omega) (Nat.mod_lt _ (by decide)) hn48] at hls
      have hP : p.toNat = p.toNat / 32 * 32 + p.toNat % 32 := by omega
      have he : (if (n.toNat + p.toNat) % 32 = 0 then 32 else (n.toNat + p.toNat) % 32) = p.toNat % 32 + n.toNat := by
        split <;> omega
      rw [rotA, shB, ht_eval1 _ _ _ hSlt' (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)), hSb, he] at hbr
      have hF := win_none (bp s.mem (p.toNat / 32 * 32) c) (p.toNat % 32) (p.toNat % 32 + n.toNat) ((synd (bp s.mem (p.toNat / 32 * 32) c) 32 / 4 ^ (p.toNat % 32) * 4 ^ (p.toNat % 32)) % 4 ^ (p.toNat % 32 + n.toNat)) (by omega) (by omega)
        (synd_head_tail _ _ _ (by omega) (by omega)) hbr
      rw [show p.toNat % 32 + n.toNat - p.toNat % 32 = n.toNat by omega, ← FT_bp s.mem p.toNat _ _ c _ hP] at hF
      refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
        rw [BitVec.toNat_ofNat, idx_FT, hF, if_neg (Nat.lt_irrefl _)]
      all_goals simp [setReg]
    · -- the string ends in the first block: a match
      have ho1 : ¬ p.toNat % 32 = 0 := by janus_assumption
      have hls : (((addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.c && !(addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.z) = false) := by janus_assumption
      rw [ls_iff n _ (by omega) (Nat.mod_lt _ (by decide)) hn48] at hls
      have hP : p.toNat = p.toNat / 32 * 32 + p.toNat % 32 := by omega
      have he : (if (n.toNat + p.toNat) % 32 = 0 then 32 else (n.toNat + p.toNat) % 32) = p.toNat % 32 + n.toNat := by
        split <;> omega
      have hbr' : ¬ synd (wf (p.toNat % 32) (p.toNat % 32 + n.toNat) (bp s.mem (p.toNat / 32 * 32) c)) 32 = 0 := by
        rw [← synd_head_tail _ _ _ (by omega) (by omega), ← hSb, ← he, ← ht_eval1 _ (p.toNat % 32) ((n.toNat + p.toNat) % 32) hSlt' (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)), ← shB, ← rotA]
        exact hbr
      obtain ⟨hct, hlt⟩ := win_found (bp s.mem (p.toNat / 32 * 32) c) (p.toNat % 32) (p.toNat % 32 + n.toNat) ((synd (bp s.mem (p.toNat / 32 * 32) c) 32 / 4 ^ (p.toNat % 32) * 4 ^ (p.toNat % 32)) % 4 ^ (p.toNat % 32 + n.toNat)) (by omega) (by omega)
        (synd_head_tail _ _ _ (by omega) (by omega)) (by rw [synd_head_tail _ _ _ (by omega) (by omega)]; exact hbr')
      rw [show p.toNat % 32 + n.toNat - p.toNat % 32 = n.toNat by omega, ← FT_bp s.mem p.toNat _ _ c _ hP] at hct hlt
      refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
        rw [rotA, shB, ht_eval1 _ _ _ hSlt' (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)), hSb, he]
        rw [x0_head p _ _ _ _ hP hct (by omega) (by omega), idx_FT, if_pos hlt]
      all_goals simp [setReg]
    · -- not in the first block: no match there, into the loop
      have ho1 : ¬ p.toNat % 32 = 0 := by janus_assumption
      have hls : ¬ (((addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.c && !(addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.z) = false) := by janus_assumption
      rw [ls_iff n _ (by omega) (Nat.mod_lt _ (by decide)) hn48] at hls
      have hP : p.toNat = p.toNat / 32 * 32 + p.toNat % 32 := by omega
      rw [rotA, ht_eval2 _ _ hSlt' (Nat.mod_lt _ (by decide)), hSb] at hbr
      have hF := win_none (bp s.mem (p.toNat / 32 * 32) c) (p.toNat % 32) 32 (synd (bp s.mem (p.toNat / 32 * 32) c) 32 / 4 ^ (p.toNat % 32) * 4 ^ (p.toNat % 32)) (by omega) (by omega)
        (synd_head _ _ (by omega)) hbr
      rw [← FT_bp s.mem p.toNat _ _ c _ hP] at hF
      refine loop64 p n c s hpre0 h2 (by omega) _ _ (32 - p.toNat % 32) rfl rfl ⟨rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hF, by omega, by omega, Or.inl (by omega)⟩
      · apply BitVec.eq_of_toNat_eq
        simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
        have := p.isLt
        simp only [Nat.reducePow]
        omega
      · apply BitVec.eq_of_toNat_eq
        simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
        simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
        have := p.isLt
        have := n.isLt
        have h32 : (32#64 : BitVec 64).toNat = 32 := rfl
        simp only [h32, Nat.reducePow]
        omega
      all_goals simp [setReg, setVReg]
    · -- not in the first block: a match
      have ho1 : ¬ p.toNat % 32 = 0 := by janus_assumption
      have hls : ¬ (((addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.c && !(addWithCarry n (BitVec.ofNat 64 (p.toNat % 32) - 32#64) false).snd.z) = false) := by janus_assumption
      rw [ls_iff n _ (by omega) (Nat.mod_lt _ (by decide)) hn48] at hls
      have hP : p.toNat = p.toNat / 32 * 32 + p.toNat % 32 := by omega
      have hbr' : ¬ synd (wf (p.toNat % 32) 32 (bp s.mem (p.toNat / 32 * 32) c)) 32 = 0 := by
        rw [← synd_head _ _ (by omega), ← hSb, ← ht_eval2 _ _ hSlt' (Nat.mod_lt _ (by decide)), ← rotA]
        exact hbr
      obtain ⟨hct, hlt⟩ := win_found (bp s.mem (p.toNat / 32 * 32) c) (p.toNat % 32) 32 (synd (bp s.mem (p.toNat / 32 * 32) c) 32 / 4 ^ (p.toNat % 32) * 4 ^ (p.toNat % 32)) (by omega) (by omega)
        (synd_head _ _ (by omega)) (by rw [synd_head _ _ (by omega)]; exact hbr')
      rw [← FT_bp s.mem p.toNat _ _ c _ hP] at hct hlt
      have hF := FT_found s.mem p.toNat c 0 n.toNat (32 - p.toNat % 32) (FT_zero _ _ _) (by omega) (by simpa using hlt)
      simp only [Nat.zero_add, Nat.add_zero] at hF
      refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
      · simp only [setReg, Nat.reduceEqDiff, ↓reduceIte]
        rw [rotA, ht_eval2 _ _ hSlt' (Nat.mod_lt _ (by decide)), hSb]
        rw [x0_head p _ _ _ _ hP hct (by omega) (by omega), idx_FT, hF, if_pos (by omega)]
      all_goals simp [setReg]

/-- the library hypothesis `hibs` of a consumer, for the library program -/
theorem ibs_lib_64 : IbsLib64 Fv256.IbsProg64.program entry64 := fun p n c => ibs_summary_64 p n c

end Fv256.IndexByte
