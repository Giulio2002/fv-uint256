import Extracted
import Fv256.Arm64.CallSites.Base
import Fv256.Arm64.SfdCfgE
import Fv256.Arm64.SfdWitB

/-!
# Witness for `SetFromDecimal` (arm64), part C: a concrete call state

`SetFromDecimal(z, "7")` with the toy runtime `R`, the interface model `R0`, a stack window `[lo, hi)`, and a memory laid out
by hand (`mem0`): the model's metadata, the heap, the binary's static objects the proof reads (at the extraction's own
addresses, with synthetic contents), the four multiplier objects `10^(19 k)`, `z`, the string.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I
  Fv256.Arm64.SfdTopSpec

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.SetFromDecimal.Witness

set_option maxRecDepth 100000

open Janus.Contracts.Toy Janus.Contracts.IfaceModel

def spW : Nat := 0x100000
def loW : Nat := 0xFEE00
def hiW : Nat := 0x100100
def gW : Nat := 0x200000
def zW : Nat := 0x300000
def multW : Nat := 0x501000

/-- byte `a - base` of the little-endian number `v` -/
def nb (v base a : Nat) : Nat := v / 256 ^ (a - base) % 256

/-- the synthetic contents of `mem0` -/
def val (a : Nat) : Nat :=
  if 0x10000 ≤ a ∧ a < 0x11000 then (IfaceModel.wmem.bytes a).toNat
  else if a = 0x400003 then 0x10
  else if a = 0x301000 then 0x37
  else if a = 0xdc840 then 48
  else if a = 0xdc848 then 1
  else if a = 0xf692a then 1
  else if 0xf490b ≤ a ∧ a < 0xf490b + 78 then Fv256.I.maxDigit (a - 0xf490b)
  else if 0x1b6548 ≤ a ∧ a < 0x1b6568 then nb (multW + 32 * ((a - 0x1b6540) / 8 - 1)) 0 ((a - 0x1b6540) % 8)
  else if multW ≤ a ∧ a < multW + 128 then nb (10 ^ (19 * ((a - multW) / 32 + 1))) 0 ((a - multW) % 32)
  else 0

def mem0 : Memory :=
  ⟨fun a => BitVec.ofNat 8 (val a),
   [⟨0x10000, 0x300, false⟩, ⟨0x10300, 0xd00, true⟩, ⟨loW, hiW - loW, true⟩, ⟨gW, 0x100, false⟩, ⟨zW, 32, true⟩,
    ⟨0x301000, 1, false⟩, ⟨BUMP, 0x200, true⟩, ⟨HEAP, HSIZE, true⟩,
    ⟨0xdc840, 16, false⟩, ⟨0xf490b, 78, false⟩, ⟨0xf5940, 8, false⟩, ⟨0xf6920, 16, false⟩, ⟨0x1b5b60, 16, false⟩,
    ⟨0x1b5c10, 16, false⟩, ⟨0x1b5eb0, 16, false⟩, ⟨0x1b6540, 40, false⟩, ⟨0x1e34c0, 4, false⟩, ⟨multW, 128, false⟩]⟩

def zV : BitVec 64 := BitVec.ofNat 64 zW
def pSV : BitVec 64 := BitVec.ofNat 64 0x301000
def retW : Nat := 0x1000

def s0 : State :=
  { regs := fun i => if i = 0 then zV else if i = 1 then pSV else if i = 2 then 1#64
      else if i = 28 then BitVec.ofNat 64 gW else if i = 30 then BitVec.ofNat 64 retW else 0,
    sp := BitVec.ofNat 64 spW, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := mem0 }

theorem cfgE_lit : cfgE = (SfdCfg.mk 0x1b5c10 0x1b5b60 0x1b6540 0xdc840 0xf6940 0xf6920 0xf5940 0x1b5eb0 0x1e34c0 0xeb483
    0xf490b mgA mvA newA w1A w2A) := by
  rfl

theorem rt_eq : R.rt = [(HEAP, HEND), (BUMP, BUMP + 8), (WBUF, WBUF + 64)] := rfl


theorem hT_R0 (m : Memory) (g : BitVec 64) (h : R0.Env m g) :
    isRegularMemory m TD = true ∧ isDirectIface m TD = false ∧ tySize m TD = 8 := by
  obtain ⟨-, -, d1, -, d3, -, -, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [isRegularMemory, tyTFlag, d3]; decide
  · simp only [isDirectIface, tyTFlag, d3]; decide
  · simp only [tySize, d1]

theorem outside_of_decide {a n : Nat} {L : List (Nat × Nat)} (h : ∀ r ∈ L, a + n ≤ r.1 ∨ r.2 ≤ a) : Outside a n L :=
  Janus.Contracts.outside_of_forall h

theorem mod0 : Mod cfgE R R0 TD [] := by
  rw [cfgE_lit]
  refine ⟨R0_laws, by decide, by decide, Or.inl rfl, ?_, fun r hr => absurd hr (by simp), ?_, ?_, ?_, ?_, ?_, ?_, hT_R0⟩
  · intro r hr
    rw [rt_eq]
    simp only [R0_priv, List.mem_singleton] at hr
    subst hr
    simp only [outside_cons, outside_nil, and_true]; decide
  · rw [rt_eq]; decide
  · intro r hr
    rw [rt_eq]
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro r hr hne
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    simp only [R0_priv]
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact absurd rfl hne | decide
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))


theorem val_big (a : Nat) (h : 0x600000 ≤ a) : val a = 0 := by
  simp only [val, multW]
  repeat rw [if_neg (by omega)]
  exact if_neg (by omega)

theorem bytes_big (i : Nat) (h : HEAP ≤ i) : mem0.bytes i = 0 := by
  show BitVec.ofNat 8 (val i) = 0
  rw [val_big i (by simp only [HEAP] at h; omega)]; rfl

theorem inv0 : R.inv 0x400 [] (s0.regs 28).toNat (view R.rt [] s0.mem) := by
  refine toyInv_init (m := mem0) (g := (s0.regs 28).toNat) (by decide) (by decide) (fun i hi _ => bytes_big i hi)
    (by decide) (by decide) (by decide)

theorem static0 : StaticOK cfgE R0 TD s0.mem := by
  rw [cfgE_lit]
  exact ⟨by decide, Or.inl rfl, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide⟩

theorem env0 : Env cfgE R R0 TD 0x400 [] loW hiW s0 := by
  rw [cfgE_lit]
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_, ?_, ?_, ?_,
    by decide, ?_, static0, ?_, inv0, fun r hr => absurd hr (by simp)⟩
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · exact ⟨by decide, by decide, by unfold Desc; decide⟩

theorem mult0 : MultOK cfgE zV.toNat loW hiW s0.mem := by
  rw [cfgE_lit]
  refine ⟨by decide, ?_, ?_⟩
  · apply outside_of_decide; decide
  · intro k h1 h2
    have hk : k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
    rcases hk with rfl | rfl | rfl | rfl
    all_goals refine ⟨by decide, by decide, by decide, ?_⟩
    all_goals (apply outside_of_decide; decide)

theorem maxdig0 : ∀ k, k < 78 → s0.mem.readLE (cfgE.maxStr + k) 1 = Fv256.I.maxDigit k := by
  rw [cfgE_lit]
  intro k hk
  show (BitVec.ofNat 8 (val (0xf490b + k))).toNat = _
  have h1 : val (0xf490b + k) = Fv256.I.maxDigit k := by
    simp only [val, multW]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_pos (by omega)]
    rw [Nat.add_sub_cancel_left]
  have h2 : Fv256.I.maxDigit k < 256 := by
    unfold Fv256.I.maxDigit
    have := Nat.mod_lt ((2 ^ 256 - 1) / 10 ^ (77 - k)) (by decide : 0 < 10)
    omega
  rw [h1, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h2

theorem chunk0 : ChunkAll cfgE R R0 [] 0x400 pSV.toNat (1#64).toNat loW hiW s0.mem := by
  rw [cfgE_lit]
  intro sp sl h1 h2 h3 h4
  have e1 : pSV.toNat = 0x301000 := by decide
  have e2 : (1#64).toNat = 1 := by decide
  rw [e1] at h1 h2; rw [e2] at h2
  have hsp : sp = 0x301000 := by omega
  have hsl : sl = 1 := by omega
  subst hsp hsl
  refine ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))), fun q => Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, q, rfl⟩))),
    by decide, by decide, by decide, by decide, ?_, ?_⟩
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide

theorem pre0 : TopPre cfgE R R0 TD 0x400 [] loW hiW zV pSV 1#64 s0 := by
  have e : cfgE = _ := cfgE_lit
  refine ⟨by decide, by decide, rfl, rfl, rfl, mod0, env0, by decide, by decide, mult0, ?_⟩
  have hm := maxdig0
  have hc := chunk0
  rw [e] at hm hc ⊢
  refine ⟨by decide, ?_, by decide, ?_, ?_, hm, by decide, ?_, ⟨by decide, by decide⟩, by decide, ?_, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, hc⟩
  · apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · rw [rt_eq]; apply outside_of_decide; decide
  · apply outside_of_decide; decide
  · left; rw [rt_eq]; apply outside_of_decide; decide
  · simp only [R0_priv]; apply outside_of_decide; decide
  · intro r hr
    simp only [staticRanges, List.mem_cons, List.not_mem_nil, or_false] at hr
    apply outside_of_decide
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

theorem hret : RetAddr (Extracted.program.link implA) retW := RetAddr.of_check (by decide)

theorem setup : CallSetup ((Extracted.program.link implA).withExit retW) Extracted.entry [zV, pSV, 1#64] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

-- CALLSITE-LIVE-BLOCK
/-- Call states of the runtime stubs (U-WITNESS-CALLSITE): `s0` with `PC` at the stub's entry and the argument registers of a request `ok` serves. -/
def csNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else s0.regs i }
def csNew : State := { csNew0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }
def csMg0 : State := { s0 with regs := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 0 else s0.regs i }
def csMg : State := { csMg0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") }
def csMv0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 zW else if i = 1 then BitVec.ofNat 64 0x301000 else if i = 2 then 1 else s0.regs i }
def csMv : State := { csMv0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") }
def csW1 : State := { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }
def csW2 : State := { s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }
def csCm0 : State := { s0 with regs := fun i => if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 0 else s0.regs i }
def csCm : State := { csCm0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") }
def csIf0 : State := { s0 with regs := fun i => if i = 0 then 0 else s0.regs i }
def csIf : State := { csIf0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") }
set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 csNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), typeOK_of (by decide) (by decide), by decide⟩, ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · rw [addr_new]; exact Or.inl (⟨rfl, by decide⟩)
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 csMg := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by decide, Or.inl (by decide)⟩, ⟨guardOK_of (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ?_, inv0, by decide, liveSep_nil _, ?_⟩
  · rw [addr_mg]; exact Or.inr (Or.inr (Or.inr (Or.inl (⟨rfl, by decide⟩))))
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 csMv := by
  refine ⟨⟨(guardOK_iff _ _).1 (guardOK_of (by decide) (by decide) (by decide)), callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    ⟨?_, inv0, liveSep_nil _, ?_⟩, ⟨by decide, by decide, by simp only [calleeStack, outside_cons, outside_nil]; decide⟩,
    by decide, by decide, by simp only [calleeStack, outside_cons, outside_nil]; decide, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩
  · rw [addr_mv]; exact Or.inr (Or.inr (Or.inr (Or.inr (⟨rfl, zW, by decide⟩))))
  · intro r hr
    rw [rt_eq]
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide)

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 csW1 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w1]; exact Or.inr (Or.inl (⟨rfl, rfl⟩)), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 csW2 := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), by rw [addr_w2]; exact Or.inr (Or.inr (Or.inl (⟨rfl, rfl⟩))), inv0, liveSep_nil _, ?_⟩
  intro r hr
  rw [rt_eq]
  simp only [List.mem_singleton] at hr
  subst hr
  simp only [outside_cons, outside_nil]; decide

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 csCm :=
  ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), Or.inl (by decide), Or.inl (by decide)⟩

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite R0 csIf := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hE, -⟩ := env0
  refine ⟨⟨hE, (guardOK_iff _ _).1 (guardOK_of (by decide) (by decide) (by decide)), callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_⟩, fun h => absurd (by decide) h⟩
  simp only [R0_priv]; apply outside_of_decide; decide

/-- The statement of the witness theorem `nonvacuous` (spelled out there). -/
theorem nonvacuous_core : ∃ (impl : List Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
      (lo hi : Nat) (z pS nS : BitVec 64) (ret : Nat) (s : State),
    ImplApart Extracted.program impl ∧
    Contracts.Iface.Ifaceeq (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.ifaceeq") R2 ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R ∧
    MallocgcLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.mallocgc") 4096 R ∧
    MemmoveLive (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.memmove") 4096 R ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2 ∧
    Contracts.Cmpstring.CmpstringContract (Extracted.program.ofImpl impl)
      (Extracted.program.contractAddr "runtime.cmpstring") 16 ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, pS, nS] s ∧
    TopPre cfgE R R2 T b L lo hi z pS nS s ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectLiveSite R (Extracted.program.contractAddr "runtime.newobject") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc") ∧ MallocgcLiveSite R (Extracted.program.contractAddr "runtime.mallocgc") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove") ∧ MemmoveLiveSite R (Extracted.program.contractAddr "runtime.memmove") 4096 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 1 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") ∧ WbLiveSite R (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 2 [] 0x400 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring") ∧ Janus.Contracts.Cmpstring.CmpstringPre 16 s_c) ∧
    (∃ (s_c : State), s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq") ∧ IfaceeqSite R2 s_c) :=
  ⟨implA, R, R0, TD, 0x400, [], loW, hiW, zV, pSV, 1#64, retW, s0, implOK,
    by rw [addr_if]; exact model_if, by rw [addr_new]; exact model_new, by rw [addr_mg]; exact model_mg,
    by rw [addr_mv]; exact model_mv, by rw [addr_w1]; exact model_wb1, by rw [addr_w2]; exact model_wb2,
    by rw [addr_cm]; exact hcmp, hret, setup, pre0,
    ⟨csNew, rfl, csNew_pre⟩, ⟨csMg, rfl, csMg_pre⟩, ⟨csMv, rfl, csMv_pre⟩, ⟨csW1, rfl, csW1_pre⟩, ⟨csW2, rfl, csW2_pre⟩, ⟨csCm, rfl, csCm_pre⟩, ⟨csIf, rfl, csIf_pre⟩⟩

end Fv256.Arm64.SetFromDecimal.Witness
