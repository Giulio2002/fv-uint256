import Extracted
import Fv256.SpecE
import Fv256.UtilE
import Fv256.Amd64.DecA
import Fv256.UtilB2
import Fv256.Util

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

/-- Entry of `(*Int).Dec` (the extraction's entry point). -/
abbrev decE : Nat := segAddr Extracted.program "github.com/holiman/uint256.(*Int).Dec"
/-- The loop head of `Dec` (`MOVQ CX, 0x100(SP)`), `0x16c` bytes into the function. -/
abbrev decH : Nat := decE + 0x16c

theorem zeros_tab : ∀ i, i < 98 → Extracted.data[3]!.bytes[i]! = 48 := by
  decide +kernel

/-- The memory of `Dec` at the loop head, from the entry memory `m` (`r` = entry `RSP`, `zp` = the receiver,
`x` = `X15`, `bp` = the saved `BP`). -/
def initMem (m : Janus.Arm64.Memory) (r zp x bp : Nat) : Janus.Arm64.Memory :=
  ((((((((((((((((((m.writeLE (r - 8) 8 bp).writeLE (r - 290) 16 64053151420411946063694043751862251568).writeLE
    (r - 274) 16 64053151420411946063694043751862251568).writeLE (r - 258) 16 64053151420411946063694043751862251568).writeLE
    (r - 242) 16 64053151420411946063694043751862251568).writeLE (r - 226) 16 64053151420411946063694043751862251568).writeLE
    (r - 210) 16 64053151420411946063694043751862251568).writeLE (r - 208) 16 64053151420411946063694043751862251568).writeLE
    (r - 64) 16 x).writeLE (r - 48) 16 x).writeLE (r - 64) 8 10000000000000000000).writeLE (r - 96) 16 x).writeLE
    (r - 80) 16 x).writeLE (r - 96) 8 (m.readLE zp 8)).writeLE (r - 88) 8 (m.readLE (zp + 8) 8)).writeLE
    (r - 80) 8 (m.readLE (zp + 16) 8)).writeLE (r - 72) 8 (m.readLE (zp + 24) 8)).writeLE (r - 309) 16 x).writeLE
    (r - 306) 16 x

set_option maxRecDepth 200000 in
theorem initMem_frame (m : Janus.Arm64.Memory) (r zp x bp : Nat) (h : 0x178 ≤ r) :
    MemFrame m (initMem m r zp x bp) [(r - 0x178 - 0x1a0, r)] := by
  unfold initMem
  repeat' first
    | exact MemFrame.refl _ _
    | refine MemFrame.writeLE ?_ _ (List.mem_singleton_self _) (by omega) (by omega)

set_option maxRecDepth 200000 in
theorem initMem_bp (m : Janus.Arm64.Memory) (r zp x bp : Nat) (h : 0x178 ≤ r) (hbp : bp < 2 ^ 64) :
    (initMem m r zp x bp).readLE (r - 8) 8 = bp := by
  unfold initMem
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  simp only [Nat.reducePow]
  omega

set_option maxRecDepth 200000 in
theorem initMem_y (m : Janus.Arm64.Memory) (r zp bp : Nat) (h : 0x178 ≤ r) :
    (initMem m r zp 0 bp).readLE (r - 96) 32 = m.readLE zp 32 := by
  rw [Util.readLE_32, Util.readLE_32, show r - 96 + 8 = r - 88 by omega, show r - 96 + 16 = r - 80 by omega, show r - 96 + 24 = r - 72 by omega]
  unfold initMem
  have l0 := Janus.Arm64.Memory.readLE_lt m zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt m (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt m (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt m (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
  simp only [Nat.reducePow, Nat.add_assoc, Nat.reduceAdd]
  omega


theorem zbyte_all : ∀ e, e < 16 → 64053151420411946063694043751862251568 / 256 ^ e % 256 ^ 1 = 48 := by
  decide +kernel

theorem zbyte (e : Nat) (he : e < 16) : 64053151420411946063694043751862251568 / 256 ^ e % 256 ^ 1 = 48 := zbyte_all e he

set_option maxRecDepth 200000 in
theorem initMem_d (m : Janus.Arm64.Memory) (r zp bp : Nat) (h : 0x178 ≤ r) :
    (initMem m r zp 0 bp).readLE (r - 64) 32 = 10 ^ 19 := by
  rw [Util.readLE_32, show r - 64 + 8 = r - 56 by omega, show r - 64 + 16 = r - 48 by omega, show r - 64 + 24 = r - 40 by omega]
  unfold initMem
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self,
    Janus.Arm64.Memory.readLE_writeLE_inside, Nat.zero_div, Nat.zero_mod]

set_option maxRecDepth 200000 in
theorem initMem_zeros (m : Janus.Arm64.Memory) (r zp bp : Nat) (h : 0x178 ≤ r) :
    ∀ i, i < 98 → (initMem m r zp 0 bp).readLE (r - 290 + i) 1 = 48 := by
  intro i hi
  unfold initMem
  by_cases c1 : 82 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)
  by_cases c2 : 80 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)
  by_cases c3 : 64 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)
  by_cases c4 : 48 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)
  by_cases c5 : 32 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)
  by_cases c6 : 16 ≤ i
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)
  · simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_inside]
    exact zbyte _ (by omega)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem dec_init (s : State) (hpc : s.rip = BitVec.ofNat 64 decE) (zp : Nat) (e0 : s.regs 0 = BitVec.ofNat 64 zp)
    (hg : StackGuardOK s 0xf8) (hw : StackWritable s 0x318 0x8) (hal : (s.regs 4).toNat % 8 = 0)
    (hd : Extracted.program.DataLoaded s.mem)
    (hz : zp + 32 ≤ 2 ^ 48 ∧ s.mem.accessible zp 32 false = true)
    (hzd : zp + 32 ≤ (s.regs 4).toNat - 0x318 ∨ (s.regs 4).toNat + 8 ≤ zp)
    (hbig : s.mem.readLE (zp + 8) 8 ≠ 0 ∨ s.mem.readLE (zp + 16) 8 ≠ 0 ∨ s.mem.readLE (zp + 24) 8 ≠ 0)
    (hx15 : s.xmm 15 = 0) :
    ReachesRet Extracted.program (BitVec.ofNat 64 decH) s
      (fun S' => S'.regs 0 = BitVec.ofNat 64 98 ∧ S'.regs 1 = 19#64 ∧
        S'.regs 2 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x178 + 67) ∧
        S'.regs 4 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x178) ∧
        S'.regs 5 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x178 + 368) ∧
        S'.regs 7 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x178 + 280) ∧
        S'.regs 9 = BitVec.ofNat 64 ((s.regs 4).toNat - 0x178 + 312) ∧
        S'.regs 14 = s.regs 14 ∧ S'.xmm 15 = 0 ∧ S'.df = s.df ∧
        MemFrame s.mem S'.mem [((s.regs 4).toNat - 0x178 - 0x1a0, (s.regs 4).toNat)] ∧
        Fv256.B.wv S'.mem ((s.regs 4).toNat - 0x178 + 280) 4 = Fv256.B.wv s.mem zp 4 ∧
        Fv256.B.wv S'.mem ((s.regs 4).toNat - 0x178 + 312) 4 = 10 ^ 19 ∧
        (∀ k, k < 98 → S'.mem.readLE ((s.regs 4).toNat - 0x178 + 86 + 97 - k) 1 = 48) ∧ TabsOK S'.mem ∧
        S'.mem.readLE ((s.regs 4).toNat - 8) 8 = (s.regs 5).toNat) := by
  have hc : decE + 0x400 < 2 ^ 47 := by decide
  obtain ⟨hwb, hwn, hwa⟩ := hw
  have hgl := hg.load
  have hg3 := hg.below
  have hg1 := hg.noWrap
  have hg2 := hg.readable
  obtain ⟨hzn, hza⟩ := hz
  simp only [regSP, Janus.Amd64.GoABI.regG, Janus.Amd64.GoABI.stackguard0Offset,
    Janus.Amd64.GoABI.stackguard0] at hgl hg3 hg1 hg2 hwb hwn hwa hal
  janus64_data hd [hwa]
  have l0 := Janus.Arm64.Memory.readLE_lt s.mem zp 8
  have l1 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 8) 8
  have l2 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 16) 8
  have l3 := Janus.Arm64.Memory.readLE_lt s.mem (zp + 24) 8
  simp only [Nat.reducePow] at l0 l1 l2 l3
  have hnz : ((BitVec.ofNat 64 (s.mem.readLE zp 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE zp 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  have hnz2 : ((BitVec.ofNat 64 (s.mem.readLE (zp + 8) 8) ||| BitVec.ofNat 64 (s.mem.readLE (zp + 16) 8) |||
      BitVec.ofNat 64 (s.mem.readLE (zp + 24) 8)).toNat = 0) = False := by
    apply eq_false
    intro h
    rw [BitVec.toNat_or, BitVec.toNat_or, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 8) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 16) 8 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : s.mem.readLE (zp + 24) 8 < 2 ^ 64)] at h
    simp only [Nat.or_eq_zero_iff] at h
    omega
  janus64_run [e0, hnz, hnz2] until [decH]
  have hx0 : (s.xmm 15).toNat = 0 := by rw [hx15]; rfl
  have hr := (s.regs 4).isLt
  have hr0 : 0x178 ≤ (s.regs 4).toNat := by omega
  refine ReachesRet.done (by rfl) ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [setRegF]
  · simp [setRegF]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 309 (by omega)]; congr 1; omega
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 376 (by omega)]
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 8 (by omega)]; congr 1; omega
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 96 (by omega)]; congr 1; omega
  · simp [setRegF]; rw [Fv256.E.bv_sub_lit _ 64 (by omega)]; congr 1; omega
  · simp [setRegF]
  · simp [setRegF, setXmmF]; exact hx15
  · simp [setRegF]
  · dsimp only
    try simp only [hx0]
    exact initMem_frame _ _ _ _ _ hr0
  · dsimp only
    rw [Fv256.B.wv4_eq, Fv256.B.wv4_eq, show (s.regs 4).toNat - 0x178 + 280 = (s.regs 4).toNat - 96 by omega]
    try simp only [hx0]
    exact initMem_y _ _ _ _ hr0
  · dsimp only
    rw [Fv256.B.wv4_eq, show (s.regs 4).toNat - 0x178 + 312 = (s.regs 4).toNat - 64 by omega]
    try simp only [hx0]
    exact initMem_d _ _ _ _ hr0
  · intro k hk
    dsimp only
    rw [show (s.regs 4).toNat - 0x178 + 86 + 97 - k = (s.regs 4).toNat - 290 + (97 - k) by omega]
    try simp only [hx0]
    exact initMem_zeros _ _ _ _ hr0 _ (by omega)
  · dsimp only
    refine TabsOK.frame (TabsOK.of_loaded hd) (rs := [((s.regs 4).toNat - 0x178 - 0x1a0, (s.regs 4).toNat)]) ?_ ?_
    · try simp only [hx0]
      exact initMem_frame _ _ _ _ _ hr0
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact accessible_sub hwa (Or.inr rfl) (by omega) (by omega)
  · dsimp only
    try simp only [hx0]
    exact initMem_bp _ _ _ _ _ hr0 (by have := (s.regs 5).isLt; omega)
end Fv256.Amd64.Dec
