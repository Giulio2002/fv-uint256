import Fv256.Proofs.Common.IndexByteSpec
import Fv256.Proofs.Common.Util

/-!
# `scanScientificFromString` -> `IndexByteString.abi0`: the call-site facts (Extracted-free)

At the call, the memory is `s.mem` after the prologue stores and the call's argument stores (`sp` = the `SP` at `scanSci`'s entry):
`rbp` at `sp - 8`, the three spills at `sp + 8 .. sp + 24`, the arguments `(p, n, 'e')` at `sp - 112 .. sp - 96`, the return address at `sp - 120`.
-/

open Janus Janus.Amd64 Fv256.IndexByte

namespace Fv256.Amd64.ScanIbsCall

set_option maxRecDepth 100000

/-- the memory at the call -/
def callMem (m : Janus.Arm64.Memory) (sp v5 dst p n ra : Nat) : Janus.Arm64.Memory :=
  (((((((m.writeLE (sp - 8) 8 v5).writeLE (sp + 16) 8 p).writeLE (sp + 8) 8 dst).writeLE (sp + 24) 8 n).writeLE (sp + 16) 8 p).writeLE
    (sp - 112) 8 p).writeLE (sp - 104) 8 n |>.writeLE (sp - 96) 1 101).writeLE (sp - 120) 8 ra

theorem pre_of (m : Janus.Arm64.Memory) {sp v5 dst p n ra lo hi : Nat} (S3 : Janus.Amd64.State) {avx : Nat}
    (hm : S3.mem = callMem m sp v5 dst p n ra) (h4 : S3.regs 4 = BitVec.ofNat 64 (sp - 120))
    (hra : ra < 2 ^ 47) (hlo : lo + 4920 ≤ sp) (hsp : sp % 8 = 0) (hhi : sp + 32 ≤ hi) (hhi48 : hi ≤ 2 ^ 48)
    (hwin : m.accessible lo (hi - lo) true = true) (hav : m.accessible avx 1 false = true)
    (hpg : PageReadable m p n) (hp64 : p < 2 ^ 64) (hn64 : n < 2 ^ 64) (hpn : p + n ≤ 2 ^ 48)
    (hpW : n = 0 ∨ p + n ≤ lo ∨ hi ≤ p) :
    IbsPreA avx (BitVec.ofNat 64 p) (BitVec.ofNat 64 n) 101 S3 := by
  have hs4 : (S3.regs 4).toNat = sp - 120 := by rw [h4, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
  have hpt : (BitVec.ofNat 64 p).toNat = p := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hp64
  have hnt : (BitVec.ofNat 64 n).toNat = n := by rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn64
  unfold IbsPreA
  rw [hs4, hpt, hnt, hm]
  unfold callMem
  have hw : m.accessible (sp - 120) 32 false = true := by
    exact Janus.Arm64.Memory.accessible_sub m hwin (Or.inl rfl) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hav]
  · simp [hw]
  · rw [Janus.Arm64.Memory.readLE_writeLE_self]; exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) (by omega)
  · omega
  · omega
  · rw [show sp - 120 + 8 = sp - 112 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using hp64)
  · rw [show sp - 120 + 16 = sp - 104 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using hn64)
  · rw [show sp - 120 + 24 = sp - 96 by omega]
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  · simp
    exact Janus.Arm64.Memory.accessible_sub m hwin (Or.inr rfl) (by omega) (by omega)
  · unfold PageReadable at hpg ⊢
    simpa using hpg
  · omega

theorem pre_of_bv (m : Janus.Arm64.Memory) {sp v5 dst ra lo hi : Nat} (p n : BitVec 64) (S3 : Janus.Amd64.State) {avx : Nat}
    (hm : S3.mem = callMem m sp v5 dst p.toNat n.toNat ra) (h4 : S3.regs 4 = BitVec.ofNat 64 (sp - 120))
    (hra : ra < 2 ^ 47) (hlo : lo + 4920 ≤ sp) (hsp : sp % 8 = 0) (hhi : sp + 32 ≤ hi) (hhi48 : hi ≤ 2 ^ 48)
    (hwin : m.accessible lo (hi - lo) true = true) (hav : m.accessible avx 1 false = true)
    (hpg : PageReadable m p.toNat n.toNat) (hpn : p.toNat + n.toNat ≤ 2 ^ 48)
    (hpW : n.toNat = 0 ∨ p.toNat + n.toNat ≤ lo ∨ hi ≤ p.toNat) :
    IbsPreA avx p n 101 S3 := by
  have := pre_of m S3 (p := p.toNat) (n := n.toNat) hm h4 hra hlo hsp hhi hhi48 hwin hav hpg p.isLt n.isLt hpn hpW
  simpa [BitVec.ofNat_toNat] using this

theorem find_congr (l : List Nat) (f g : Nat → Bool) (h : ∀ i ∈ l, f i = g i) : l.find? f = l.find? g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.find?_cons, h a (by simp)]
    rw [ih (fun i hi => h i (by simp [hi]))]

theorem indexOf_congr (b b' : Nat → Nat) (n c : Nat) (h : ∀ i, i < n → b i = b' i) : indexOfNat b n c = indexOfNat b' n c := by
  unfold indexOfNat
  rw [find_congr (List.range n) (fun i => b i == c % 256) (fun i => b' i == c % 256)
    (fun i hi => by simp only [h i (List.mem_range.1 hi)])]

/-- the facts that hold after the call (state `S'`, at the instruction after the `CALL`) -/
def PostK (s S : Janus.Amd64.State) (lo hi : Nat) (dst p n : BitVec 64) : Prop :=
  S.regs 4 = s.regs 4 - 112#64 ∧ S.regs 5 = s.regs 4 - 8#64 ∧ S.fsBase = s.fsBase ∧ S.df = s.df ∧
  Janus.MemFrame s.mem S.mem [(lo, hi)] ∧
  S.mem.readLE ((s.regs 4).toNat - 88) 8 = indexOfNat (bytesOf s.mem p.toNat) n.toNat 101 ∧
  S.mem.readLE ((s.regs 4).toNat + 8) 8 = dst.toNat ∧ S.mem.readLE ((s.regs 4).toNat + 16) 8 = p.toNat ∧
  S.mem.readLE ((s.regs 4).toNat + 24) 8 = n.toNat ∧ S.mem.readLE (s.regs 4).toNat 8 = s.mem.readLE (s.regs 4).toNat 8 ∧
  S.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat ∧ S.mem.regions = s.mem.regions

theorem cont {s S3 S' : Janus.Amd64.State} {lo hi : Nat} {dst p n : BitVec 64}
    (h4 : S3.regs 4 = s.regs 4 - 120#64) (h5 : S3.regs 5 = s.regs 4 - 8#64) (hfs3 : S3.fsBase = s.fsBase) (hdf3 : S3.df = s.df)
    (hm : S3.mem = callMem s.mem (s.regs 4).toNat (s.regs 5).toNat dst.toNat p.toNat n.toNat 4930611)
    (hpost : IbsPostA p n 101 S3 S') (hreg : S'.mem.regions = S3.mem.regions) (hfs : S'.fsBase = S3.fsBase) (hdf : S'.df = S3.df)
    (e1 : lo ≤ (s.regs 4).toNat) (hhi : (s.regs 4).toNat + 32 ≤ hi) (hlo : lo + 4920 ≤ (s.regs 4).toNat)
    (hpW : n.toNat = 0 ∨ p.toNat + n.toNat ≤ lo ∨ hi ≤ p.toNat) : PostK s S' lo hi dst p n := by
  obtain ⟨hv1, hv2, hv3, hv4, -, -⟩ := hpost
  have hs := (s.regs 4).isLt
  have hs4 : (S3.regs 4).toNat = (s.regs 4).toNat - 120 := by
    rw [h4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hmf3 : Janus.MemFrame s.mem S3.mem [(lo, hi)] := by
    rw [hm]; unfold callMem
    have p64 := p.isLt
    have n64 := n.isLt
    repeat' first
      | exact Janus.MemFrame.refl _ _
      | refine Janus.MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
  have hv4' : Janus.MemFrame S3.mem S'.mem [(lo, hi)] :=
    hv4.mono (fun a n h => by
      simp only [outside_cons, outside_nil, and_true] at h ⊢
      rw [hs4]
      omega)
  have hmf : Janus.MemFrame s.mem S'.mem [(lo, hi)] := hmf3.trans hv4' (rs'' := [(lo, hi)]) (fun a n h => ⟨h, h⟩)
  have o4 : ∀ a, (a + 8 ≤ (s.regs 4).toNat - 88 ∨ (s.regs 4).toNat - 80 ≤ a) → S'.mem.readLE a 8 = S3.mem.readLE a 8 := by
    intro a ha
    exact hv4.readLE a 8 (by
      simp only [outside_cons, outside_nil, and_true]
      rw [hs4]; omega)
  have p64 := p.isLt
  have n64 := n.isLt
  have hb : ∀ i, i < n.toNat → bytesOf S3.mem p.toNat i = bytesOf s.mem p.toNat i := by
    intro i hi'
    unfold bytesOf
    rw [hm]; unfold callMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  refine ⟨?_, ?_, hfs.trans hfs3, hdf.trans hdf3, hmf, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv2, h4]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]; omega
  · rw [hv3, h5]
  · have := hv1; rw [hs4] at this
    rw [show (s.regs 4).toNat - 120 + 32 = (s.regs 4).toNat - 88 by omega, indexOf_congr _ _ _ _ hb] at this
    exact this
  · rw [o4 _ (by omega), hm]; unfold callMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt dst.isLt
  · rw [o4 _ (by omega), hm]; unfold callMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt p.isLt
  · rw [o4 _ (by omega), hm]; unfold callMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt n.isLt
  · rw [o4 _ (by omega), hm]; unfold callMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
  · rw [o4 _ (by omega), hm]; unfold callMem
    simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (s.regs 5).isLt
  · rw [hreg, hm]; unfold callMem
    simp only [Janus.Arm64.Memory.regions_writeLE]

end Fv256.Amd64.ScanIbsCall