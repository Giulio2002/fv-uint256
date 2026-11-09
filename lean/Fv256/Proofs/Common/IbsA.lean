import Janus
import Fv256.Proofs.Common.IbsProgA
import Fv256.Proofs.Common.IndexByteSpec
import Fv256.Proofs.Common.IbsMath

/-!
# `internal/bytealg.IndexByteString.abi0` (amd64): library summary over `Fv256.IbsProgA.program`

Extracted-free.  `ibs_summary_A` proves `IbsSummaryA IbsProgA.program 0x402bc0 0x5df444 p n c` for every `p n c`, i.e. the result slot holds
`indexOfNat`, for BOTH values of `internal/cpu.X86.HasAVX2` (only the readability of that byte, `avxA = 0x5df444`, is assumed).

Paths of `indexbytebody`: `n = 0`; `n < 16` (16-byte load at `p` when the 16 bytes do not cross a page, else the load at `p+n-16` shifted
by `n`); `16 <= n <= 32` and `n > 32` without AVX2 (SSE loop `sse_loop`, 16-byte blocks, last block at `p+n-16`); `n > 32` with AVX2
(`avx_loop`, 32-byte blocks, last block at `p+n-32`).  The block invariant is `FT s.mem p c j = j` (no match in the first `j` bytes).
-/
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
namespace Fv256.IndexByte

abbrev avxA : Nat := 0x5df444


/-- loop invariant at the SSE loop head `0x402aa5` -/
def SseInv (s t : State) (p n : BitVec 64) (c j : Nat) : Prop :=
  t.fsBase = s.fsBase ∧ t.df = s.df ∧ t.mem = s.mem ∧ t.regs 4 = s.regs 4 ∧ t.regs 5 = s.regs 5 ∧ t.regs 8 = s.regs 4 + 32#64 ∧
  t.regs 7 = p + BitVec.ofNat 64 j ∧ t.regs 0 = p + n - 16#64 ∧ t.regs 6 = p ∧
  t.xmm 0 = BitVec.ofNat 128 (replBytes 16 (c % 256)) ∧ FT s.mem p.toNat c j = j ∧ j < n.toNat

set_option maxRecDepth 100000 in
theorem sse_loop (p n : BitVec 64) (c : Nat) (s : State) (hpre : IbsPreA avxA p n c s) (hn16 : 16 ≤ n.toNat) :
    ∀ k, ∀ (t : State) j, n.toNat - j = k → t.rip = BitVec.ofNat 64 0x402aa5 → SseInv s t p n c j →
      ReachesRet Fv256.IbsProgA.program (retAddrOf s) t (IbsPostA p n c s) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro t j hk hpc hinv
  obtain ⟨hav, hstk, hra1, hra2, hra3, hp, hn, hc, hacc, hpr, hdis⟩ := hpre
  obtain ⟨hfs, hdf, hm, h4, h5, h8, h7, h0, h6, hx, hft, hjn⟩ := hinv
  obtain ⟨hend, hacc2⟩ := hpr.resolve_left (by omega)
  have hn48 : n.toNat < 2 ^ 48 := by omega
  have hp48 : p.toNat < 2 ^ 48 := by omega
  janus64_run until [0x402aa5]
  · -- the chunk had no match: next round
    have hz : msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem (p.toNat + j) 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0 := by janus_assumption
    rw [mk16_mod32, mk16_zero_iff] at hz
    have hlt : p.toNat + j < p.toNat + n.toNat - 16 := by janus_assumption
    have hft' : FT s.mem p.toNat c (j + 16) = j + 16 := by
      rw [FT_add, hft, if_neg (by omega), hz]
    refine ih (n.toNat - (j + 16)) (by omega) _ (j + 16) rfl rfl ⟨by simp [hfs], by simp [hdf], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hft', by omega⟩
    · simp [setRegF, h4]
    · simp [setRegF, h5]
    · simp [setRegF, h8]
    · simp [setRegF]
    · simp [setRegF, h0]
    · simp [setRegF, h6]
    · simp [setXmmF, hx]
  · -- found in the chunk at p + j
    have hz : ¬ (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem (p.toNat + j) 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0) := by janus_assumption
    have hlt : p.toNat + j < p.toNat + n.toNat - 16 := by janus_assumption
    rw [mk16_mod32] at hz
    have hne := hz
    rw [mk16_zero_iff] at hz
    have hct : FT s.mem (p.toNat + j) c 16 < 16 := by have := FT_le s.mem (p.toNat + j) c 16; omega
    have hF := FT_found s.mem p.toNat c j n.toNat 16 hft (by omega) hct
    refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF, h5]) (by simp [hfs]) (by simp [hdf]) ?_
    simp only [mk16_mod32]
    rw [ctz32_mk16 _ _ _ hne, idx_FT, hF, if_pos (by omega)]
    omega
  · -- the tail chunk: no match
    have hz : (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 16) 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0) := by janus_assumption
    have hge : ¬ (p.toNat + j < p.toNat + n.toNat - 16) := by janus_assumption
    rw [mk16_mod32, mk16_zero_iff] at hz
    have hF := FT_tail s.mem p.toNat c j n.toNat 16 hft hn16 (by omega)
    rw [hz, if_neg (by omega)] at hF
    refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF, h5]) (by simp [hfs]) (by simp [hdf]) ?_
    rw [idx_FT, hF, if_neg (Nat.lt_irrefl _)]
  · -- the tail chunk: a match
    have hz : ¬ (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 16) 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0) := by janus_assumption
    have hge : ¬ (p.toNat + j < p.toNat + n.toNat - 16) := by janus_assumption
    rw [mk16_mod32] at hz
    have hne := hz
    rw [mk16_zero_iff] at hz
    have hct : FT s.mem (p.toNat + n.toNat - 16) c 16 < 16 := by have := FT_le s.mem (p.toNat + n.toNat - 16) c 16; omega
    have hF := FT_tail s.mem p.toNat c j n.toNat 16 hft hn16 (by omega)
    rw [if_pos hct] at hF
    refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF, h5]) (by simp [hfs]) (by simp [hdf]) ?_
    simp only [mk16_mod32]
    rw [ctz32_mk16 _ _ _ hne, idx_FT, hF, if_pos (by omega)]
    omega

/-- loop invariant at the AVX2 loop head `0x402b40` -/
def AvxInv (s t : State) (p n : BitVec 64) (c j : Nat) : Prop :=
  t.fsBase = s.fsBase ∧ t.df = s.df ∧ t.mem = s.mem ∧ t.regs 4 = s.regs 4 ∧ t.regs 5 = s.regs 5 ∧ t.regs 8 = s.regs 4 + 32#64 ∧
  t.regs 7 = p + BitVec.ofNat 64 j ∧ t.regs 11 = p + n - 32#64 ∧ t.regs 6 = p ∧
  t.xmm 1 = BitVec.ofNat 128 (replBytes 32 (c % 256)) ∧
  t.ymmHi 1 = BitVec.ofNat 128 (replBytes 32 (c % 256) / 340282366920938463463374607431768211456) ∧
  FT s.mem p.toNat c j = j ∧ j + 32 < n.toNat

set_option maxRecDepth 100000 in
theorem avx_loop (p n : BitVec 64) (c : Nat) (s : State) (hpre : IbsPreA avxA p n c s) (hn32 : 32 < n.toNat) :
    ∀ k, ∀ (t : State) j, n.toNat - j = k → t.rip = BitVec.ofNat 64 0x402b40 → AvxInv s t p n c j →
      ReachesRet Fv256.IbsProgA.program (retAddrOf s) t (IbsPostA p n c s) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro t j hk hpc hinv
  obtain ⟨hav, hstk, hra1, hra2, hra3, hp, hn, hc, hacc, hpr, hdis⟩ := hpre
  obtain ⟨hfs, hdf, hm, h4, h5, h8, h7, h11, h6, hx1, hy1, hft, hjn⟩ := hinv
  obtain ⟨hend, hacc2⟩ := hpr.resolve_left (by omega)
  have hn48 : n.toNat < 2 ^ 48 := by omega
  have hp48 : p.toNat < 2 ^ 48 := by omega
  janus64_run [hy1, ymmJoin_rep] until [0x402b40]
  · -- no match in the chunk, more to scan
    have hz : cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) &&& cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) = 0 := by janus_assumption
    have hbr : (p + BitVec.ofNat 64 (j + 32)).toInt < (p + n - 32#64).toInt := by janus_assumption
    have hjl : ((p + BitVec.ofNat 64 (j + 32)).toInt < (p + n - 32#64).toInt) ↔ j + 32 < n.toNat - 32 := by
      rw [toInt_lt_iff _ _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega) (by rw [toNat_add_sub _ _ _ (by omega) (by omega)]; omega),
        toNat_add_ofNat _ _ (by omega), toNat_add_sub _ _ _ (by omega) (by omega)]
      omega
    rw [Nat.and_self, cmpeq32_zero_iff] at hz
    have hft' := FT_clean s.mem p.toNat c j 32 hft hz
    refine ih (n.toNat - (j + 32)) (by omega) _ (j + 32) rfl rfl ⟨by simp [hfs], by simp [hdf], rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hft', by have := hjl.1 hbr; omega⟩
    · simp [setRegF, h4]
    · simp [setRegF, h5]
    · simp [setRegF, h8]
    · simp [setRegF]
    · simp [setRegF, h11]
    · simp [setRegF, h6]
    · simp [setXmmF, hx1]
    · simp [setXmmF, hy1]
  · -- the tail chunk: no match
    have hz0 : cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) &&& cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) = 0 := by janus_assumption
    have hz : cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 32) 32) (replBytes 32 (c % 256)) &&& cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 32) 32) (replBytes 32 (c % 256)) = 0 := by janus_assumption
    have hnj : ¬ ((p + BitVec.ofNat 64 (j + 32)).toInt < (p + n - 32#64).toInt) := by janus_assumption
    have hjl : ((p + BitVec.ofNat 64 (j + 32)).toInt < (p + n - 32#64).toInt) ↔ j + 32 < n.toNat - 32 := by
      rw [toInt_lt_iff _ _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega) (by rw [toNat_add_sub _ _ _ (by omega) (by omega)]; omega),
        toNat_add_ofNat _ _ (by omega), toNat_add_sub _ _ _ (by omega) (by omega)]
      omega
    rw [Nat.and_self, cmpeq32_zero_iff] at hz0 hz
    have hF := FT_tail s.mem p.toNat c (j + 32) n.toNat 32 (FT_clean s.mem p.toNat c j 32 hft hz0) (by omega) (by have := mt hjl.2 hnj; omega)
    rw [hz, if_neg (Nat.lt_irrefl _)] at hF
    refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF, h5]) (by simp [hfs]) (by simp [hdf]) ?_
    rw [idx_FT, hF, if_neg (Nat.lt_irrefl _)]
  · -- the tail chunk: a match
    have hz0 : cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) &&& cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) = 0 := by janus_assumption
    have hz : ¬ (cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 32) 32) (replBytes 32 (c % 256)) &&& cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 32) 32) (replBytes 32 (c % 256)) = 0) := by janus_assumption
    have hnj : ¬ ((p + BitVec.ofNat 64 (j + 32)).toInt < (p + n - 32#64).toInt) := by janus_assumption
    have hjl : ((p + BitVec.ofNat 64 (j + 32)).toInt < (p + n - 32#64).toInt) ↔ j + 32 < n.toNat - 32 := by
      rw [toInt_lt_iff _ _ (by rw [toNat_add_ofNat _ _ (by omega)]; omega) (by rw [toNat_add_sub _ _ _ (by omega) (by omega)]; omega),
        toNat_add_ofNat _ _ (by omega), toNat_add_sub _ _ _ (by omega) (by omega)]
      omega
    rw [Nat.and_self, cmpeq32_zero_iff] at hz0 hz
    have hct : FT s.mem (p.toNat + n.toNat - 32) c 32 < 32 := by have := FT_le s.mem (p.toNat + n.toNat - 32) c 32; omega
    have hF := FT_tail s.mem p.toNat c (j + 32) n.toNat 32 (FT_clean s.mem p.toNat c j 32 hft hz0) (by omega) (by have := mt hjl.2 hnj; omega)
    rw [if_pos hct] at hF
    have hm : ¬ (msbBytes 32 (cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 32) 32) (replBytes 32 (c % 256))) % 4294967296 = 0) := by
      show ¬ (mk32 s.mem (p.toNat + n.toNat - 32) c % 4294967296 = 0)
      rw [mk32_mod32, mk32_zero_iff]; omega
    refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF, h5]) (by simp [hfs]) (by simp [hdf]) ?_
    rw [if_neg hm]
    rw [show msbBytes 32 (cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + n.toNat - 32) 32) (replBytes 32 (c % 256))) % 4294967296 = mk32 s.mem (p.toNat + n.toNat - 32) c from mk32_mod32 _ _ _, ctz_mk32]
    rw [idx_FT, hF, if_pos (by omega)]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  · -- found in the chunk at p + j
    have hz : ¬ (cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) &&& cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256)) = 0) := by janus_assumption
    rw [Nat.and_self, cmpeq32_zero_iff] at hz
    have hct : FT s.mem (p.toNat + j) c 32 < 32 := by have := FT_le s.mem (p.toNat + j) c 32; omega
    have hF := FT_found s.mem p.toNat c j n.toNat 32 hft (by omega) hct
    have hm : ¬ (msbBytes 32 (cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256))) % 4294967296 = 0) := by
      show ¬ (mk32 s.mem (p.toNat + j) c % 4294967296 = 0)
      rw [mk32_mod32, mk32_zero_iff]; omega
    refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF, h5]) (by simp [hfs]) (by simp [hdf]) ?_
    rw [if_neg hm]
    rw [show msbBytes 32 (cmpeqBytes 32 (Arm64.Memory.readLE s.mem (p.toNat + j) 32) (replBytes 32 (c % 256))) % 4294967296 = mk32 s.mem (p.toNat + j) c from mk32_mod32 _ _ _, ctz_mk32]
    rw [idx_FT, hF, if_pos (by omega)]
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega

abbrev entryA : Nat := 0x402bc0

set_option maxRecDepth 100000 in
/-- the library summary of `internal/bytealg.IndexByteString.abi0` on amd64 -/
theorem ibs_summary_A (p n : BitVec 64) (c : Nat) : IbsSummaryA Fv256.IbsProgA.program entryA avxA p n c := by
  intro s hpc hpre
  have hpre0 := hpre
  obtain ⟨hav, hstk, hra1, hra2, hra3, hp, hn, hc, hacc, hpr, hdis⟩ := hpre
  janus64_run until [0x402ad0, 0x402a85, 0x402b16]
  rotate_left 0
  · -- small
    by_cases hn0 : n.toNat = 0
    · have : n = 0#64 := BitVec.eq_of_toNat_eq (by simpa using hn0)
      subst this
      janus64_run
      refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) ?_
      simp [indexOfNat]
    · obtain ⟨hend, hacc2⟩ := hpr.resolve_left hn0
      have hn48 : n.toNat < 2 ^ 48 := by omega
      have hp48 : p.toNat < 2 ^ 48 := by omega
      have e := BitVec.toInt_eq_toNat_of_lt (x := n) (by omega)
      janus64_run until [0x402adf, 0x402af8]
      · -- tail path
        have hbr' := (pg_iff p hp48).1 hbr
        have hn16 : n.toNat < 16 := by
          have e := BitVec.toInt_eq_toNat_of_lt (x := n) (by omega)
          omega
        have hn32 : ¬ n.toNat % 32 = 0 := by omega
        janus64_run [bcast_state, hn32]
        · rename_i hz
          have hz' : tailX (mk16 s.mem (p.toNat + n.toNat - 16) c) n.toNat = 0 := by
            unfold tailX mk16; first | (rw [repl16_mod _ (Nat.mod_lt _ (by decide))] at hz; exact hz) | exact hz
          have hq16 : 16 ≤ p.toNat + n.toNat := by omega
          have hF := (tail_facts s.mem p.toNat n.toNat c (by omega) hn16 hq16).1.1 hz'
          refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) ?_
          rw [indexOfNat_ft]
          have : Janus.Tactic.firstTrue (fun i => decide (bytesOf s.mem p.toNat i = c % 256)) n.toNat = n.toNat := hF
          rw [this]; simp
        · rename_i hz
          have hz' : ¬ tailX (mk16 s.mem (p.toNat + n.toNat - 16) c) n.toNat = 0 := by
            unfold tailX mk16; first | (rw [repl16_mod _ (Nat.mod_lt _ (by decide))] at hz; exact hz) | exact hz
          have hq16 : 16 ≤ p.toNat + n.toNat := by omega
          have hF := (tail_facts s.mem p.toNat n.toNat c (by omega) hn16 hq16)
          have hF1 : FT s.mem p.toNat c n.toNat < n.toNat := by
            have := FT_le s.mem p.toNat c n.toNat
            have h2 : ¬ FT s.mem p.toNat c n.toNat = n.toNat := fun h => hz' (hF.1.2 h)
            omega
          have hct : ctzNat 32 (tailX (mk16 s.mem (p.toNat + n.toNat - 16) c) n.toNat) = FT s.mem p.toNat c n.toNat := hF.2 hF1
          unfold tailX mk16 at hct
          (try rw [repl16_mod _ (Nat.mod_lt _ (by decide))] at hct)
          (try rw [repl16_mod _ (Nat.mod_lt _ (by decide))])
          refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) ?_
          rw [hct, indexOfNat_ft]
          have : Janus.Tactic.firstTrue (fun i => decide (bytesOf s.mem p.toNat i = c % 256)) n.toNat = FT s.mem p.toNat c n.toNat := rfl
          rw [this]
          have := FT_le s.mem p.toNat c n.toNat
          simp only [hF1, ite_true]
          omega
      · have hbr' : ¬ 4080 ≤ p.toNat % 4096 := fun h => hbr ((pg_iff p hp48).2 h)
        have hn16 : n.toNat < 16 := by
          have e := BitVec.toInt_eq_toNat_of_lt (x := n) (by omega)
          omega
        janus64_run [bcast_state]
        · have hz : msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem p.toNat 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0 := by janus_assumption
          rw [mk16_mod32] at hz
          refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) ?_
          rw [(head_res s.mem p.toNat n.toNat c hn16).1 hz]
        · have hz : ¬ (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem p.toNat 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0) := by janus_assumption
          have hlt : ctzNat 32 (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem p.toNat 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296) % 4294967296 < n.toNat % 4294967296 := by janus_assumption
          rw [mk16_mod32] at hz hlt
          have hlt' : ctzNat 32 (mk16 s.mem p.toNat c) < n.toNat := by
            have := ctz_le 32 (mk16 s.mem p.toNat c)
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
            exact hlt
          refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) ?_
          rw [(head_res s.mem p.toNat n.toNat c hn16).2.1 hz hlt']
          have := ctz_le 32 (mk16 s.mem p.toNat c)
          simp only [mk16_mod32]
          rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
        · have hz : ¬ (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem p.toNat 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296 = 0) := by janus_assumption
          have hlt : ¬ (ctzNat 32 (msbBytes 16 (cmpeqBytes 16 (Arm64.Memory.readLE s.mem p.toNat 16) (replBytes 16 (c % 256) % 340282366920938463463374607431768211456)) % 4294967296) % 4294967296 < n.toNat % 4294967296) := by janus_assumption
          rw [mk16_mod32] at hz hlt
          have hlt' : ¬ ctzNat 32 (mk16 s.mem p.toNat c) < n.toNat := by
            have := ctz_le 32 (mk16 s.mem p.toNat c)
            rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hlt
            exact hlt
          refine post_mk p _ c s _ _ rfl (by simp [setRegF]) (by simp [setRegF]) (by simp) (by simp) ?_
          rw [(head_res s.mem p.toNat n.toNat c hn16).2.2 hz hlt']
  · -- 32 < n: the AVX2 test
    have hlt : ¬ n.toInt < 16 := by janus_assumption
    have hn0 : ¬ n.toNat = 0 := by
      intro h
      have : n = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h)
      subst this; simp at hlt
    obtain ⟨hend, hacc2⟩ := hpr.resolve_left hn0
    have hn48 : n.toNat < 2 ^ 48 := by omega
    have hp48 : p.toNat < 2 ^ 48 := by omega
    have e := BitVec.toInt_eq_toNat_of_lt (x := n) (by omega)
    have h32 : ¬ n.toNat < 32 ∧ ¬ (18446744073709551584 + n.toNat) % 18446744073709551616 = 0 := by janus_assumption
    have hnn : 32 < n.toNat := by omega
    janus64_run [bcast_state] until [0x402aa5, 0x402b40]
    · exact avx_loop p n c s hpre0 hnn _ _ 0 rfl rfl ⟨rfl, rfl, rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], by simp [setRegF],
        by simp [setRegF], by simp [setRegF], by simp [setXmmF], by simp [setXmmF], FT_zero _ _ _, by omega⟩
    · exact sse_loop p n c s hpre0 (by omega) _ _ 0 rfl rfl ⟨rfl, rfl, rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], by simp [setRegF],
        by simp [setRegF], by simp [setRegF], by simp [setXmmF], FT_zero _ _ _, by omega⟩
  · -- 16 <= n <= 32: the SSE loop
    have hlt : ¬ n.toInt < 16 := by janus_assumption
    have hn0 : ¬ n.toNat = 0 := by
      intro h
      have : n = 0#64 := BitVec.eq_of_toNat_eq (by simpa using h)
      subst this; simp at hlt
    obtain ⟨hend, hacc2⟩ := hpr.resolve_left hn0
    have hn48 : n.toNat < 2 ^ 48 := by omega
    have hp48 : p.toNat < 2 ^ 48 := by omega
    have e := BitVec.toInt_eq_toNat_of_lt (x := n) (by omega)
    janus64_run [bcast_state] until [0x402aa5]
    exact sse_loop p n c s hpre0 (by omega) _ _ 0 rfl rfl ⟨rfl, rfl, rfl, by simp [setRegF], by simp [setRegF], by simp [setRegF], by simp [setRegF],
        by simp [setRegF], by simp [setRegF], by simp [setXmmF], FT_zero _ _ _, by omega⟩

/-- the library hypothesis `hibs` of a consumer, for the library program -/
theorem ibs_lib_A : IbsLibA Fv256.IbsProgA.program entryA avxA := fun p n c => ibs_summary_A p n c

end Fv256.IndexByte
