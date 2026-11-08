import Extracted
import Fv256.Arm64.FM.IntoBigDefs
import Fv256.GrabTac

/-!
# Format witness, part A: the toy string runtime (lengths 2 and 4), the trivial callees and the toy allocator (arm64)
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Arm64.FormatWitA

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

def hA : Nat := 0x600000
def hB : Nat := 0x610000
def rtT : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 8)]

/-- `slicebytetostring(0, ptr, n)` for `n = 2` or `n = 4`: the bytes copied to the block `hA`, returns `(hA, n)` -/
def ss24Words : List Nat :=
  [0xf100085f, 0x54000121, 0x39400023, 0x39400424, 0xd2a00c05, 0x390000a3, 0x390004a4, 0xaa0503e0, 0xd2800041, 0xd65f03c0,
   0xb9400023, 0xd2a00c05, 0xb90000a3, 0xaa0503e0, 0xd2800081, 0xd65f03c0]

/-- `stringtoslicebyte(0, ptr, n)` for `n = 2` or `n = 4`: the bytes zero-extended into the word at `hB`, returns `(hB, n, 8)` -/
def st24Words : List Nat :=
  [0xf100085f, 0x54000141, 0x39400023, 0x39400424, 0xaa042063, 0xd2a00c25, 0xf90000a3, 0xaa0503e0, 0xd2800041, 0xd2800102, 0xd65f03c0,
   0xb9400023, 0xd2a00c25, 0xf90000a3, 0xaa0503e0, 0xd2800081, 0xd2800102, 0xd65f03c0]

/-- readiness of the toy runtime: a two- or four-byte string and both heap blocks writable -/
def Hw : RtReady := fun a _ _ view =>
  (((∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, p, 4])) ∨ (∃ x y, a = [x, y])) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true

section Rest
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

abbrev taAddr : Nat := 157040
abbrev fpAddr : Nat := 666928
abbrev bfAddr : Nat := 706368
def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
abbrev amA : Nat := 0x700000

/-- `mov x0, xzr ; mov x1, xzr ; ret` -/
def zeroWords : List Nat := [0xaa1f03e0, 0xaa1f03e1, 0xd65f03c0]

/-- the answer of the trivial callees: `X0 = X1 = 0` -/
def R0z : Res := fun _ _ _ _ j0 j1 _ => j0 = 0 ∧ j1 = 0

def implAll : List Segment :=
  [{ name := "model-sbts", base := ssAddr, words := ss24Words }, { name := "model-stb", base := stAddr, words := st24Words },
   { name := "model-ta", base := taAddr, words := Janus.Contracts.IfaceSat.assertE2I2Code },
   newobjectSeg newA, wbSeg w1A, wbSeg w2A,
   { name := "model-am", base := amA, words := zeroWords }, { name := "model-fp", base := fpAddr, words := zeroWords },
   { name := "model-bf", base := bfAddr, words := zeroWords }]

theorem implOK : ImplApart Extracted.program implAll := by
  unfold ImplApart; constructor <;> decide

theorem addr_fp : Extracted.program.contractAddr "fmt.Fprint" = fpAddr := by decide
theorem addr_bf : Extracted.program.contractAddr "math/big.(*Int).Format" = bfAddr := by decide
theorem addr_ta : Extracted.program.contractAddr "runtime.typeAssert" = taAddr := by decide

end Rest

def linked : Program := { Extracted.program with segments := Extracted.program.segments ++ implAll }
theorem linked_eq : Extracted.program.link implAll = linked := rfl
def linkedO : Program := { Extracted.program with segments := implAll }
theorem ofImpl_eq : Extracted.program.ofImpl implAll = linkedO := rfl


theorem rtView_acc (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem byte_lt (b : BitVec 8) : b.toNat < 256 := by have := b.isLt; simpa using this

theorem byte_mod (b : BitVec 8) : b.toNat % 18446744073709551616 = b.toNat :=
  Nat.mod_eq_of_lt (by have := b.isLt; simp at this; omega)

theorem strBytes4 (m : Janus.Arm64.Memory) (a p : Nat) :
    Spec.strBytes (m.writeLE a 4 (m.readLE p 4)) a 4 = Spec.strBytes m p 4 := by
  have h0 := byte_lt (m.bytes p)
  have h1 := byte_lt (m.bytes (p + 1))
  have h2 := byte_lt (m.bytes (p + 2))
  have h3 := byte_lt (m.bytes (p + 3))
  simp [Spec.strBytes, List.range_succ, Janus.Arm64.Memory.writeLE, Janus.Arm64.Memory.readLE_succ]
  simp only [show p + 1 + 1 = p + 2 from rfl, show p + 1 + 1 + 1 = p + 3 from rfl]
  omega

theorem model1 : RtContract (Extracted.program.ofImpl implAll) ssAddr rtT 4096 Hw
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [ofImpl_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw, rtView_acc] at ha
  obtain ⟨hpp, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
  replace hpp := hpp.resolve_right (fun ⟨x, y, hp⟩ => absurd (congrArg List.length hp) (by simp [argWords, wordsFrom, slicebytetostringSpec, stringtoslicebyteSpec]))
  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hargs : argWords s 3 = [0, p, 2] := hp
    simp [slicebytetostringSpec, argWords, wordsFrom, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h1, h2⟩ := hp
    have e2 : s.regs 2 = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 1).toNat 2 false = true := by
      have h := hs2 (by omega); rw [h2] at h; exact h
    janus_run [e2]
    apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true]
      simp only [byte_mod]
      refine MemFrame.trans (rs := rtIf true rtT ++ (calleeStack s 4096 3 ++ []))
        (MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := rtIf true rtT ++ (calleeStack s 4096 3 ++ [])) (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      simp only [byte_mod]
      refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
      · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
      · rw [← h1]
        simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
      · right; right; right
        exact ⟨Nat.le_refl _, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩
  · have hargs : argWords s 3 = [0, p, 4] := hp
    simp [slicebytetostringSpec, argWords, wordsFrom, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h1, h2⟩ := hp
    have e2 : s.regs 2 = 4#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 1).toNat 4 false = true := by
      have h := hs2 (by omega); rw [h2] at h; exact h
    janus_run [e2]
    apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true]
      exact MemFrame.trans (rs := rtIf true rtT ++ (calleeStack s 4096 3 ++ []))
        (MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega))
        (MemFrame.refl _ _) (fun a n h => ⟨h, h⟩)
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      have hv : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 4 % 18446744073709551616 =
          Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 4 :=
        Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 1)) 4; simp at this; omega)
      rw [hv]
      refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
      · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
      · rw [← h1]; exact strBytes4 _ _ _
      · right; right; right
        exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩


theorem or_mul256 : ∀ a, a < 256 → ∀ b, b < 256 → (a % 18446744073709551616 ||| b * 256 % 18446744073709551616) = a + 256 * b := by
  decide +kernel

theorem strBytes4w (m : Janus.Arm64.Memory) (a p : Nat) :
    Spec.strBytes (m.writeLE a 8 (m.readLE p 4)) a 4 = Spec.strBytes m p 4 := by
  have h0 := byte_lt (m.bytes p)
  have h1 := byte_lt (m.bytes (p + 1))
  have h2 := byte_lt (m.bytes (p + 2))
  have h3 := byte_lt (m.bytes (p + 3))
  simp [Spec.strBytes, List.range_succ, Janus.Arm64.Memory.writeLE, Janus.Arm64.Memory.readLE_succ]
  simp only [show p + 1 + 1 = p + 2 from rfl, show p + 1 + 1 + 1 = p + 3 from rfl]
  omega

theorem model2 : RtContract (Extracted.program.ofImpl implAll) stAddr rtT 4096 Hw stringtoslicebyteSpec := by
  rw [ofImpl_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw, rtView_acc] at ha
  obtain ⟨hpp, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
  replace hpp := hpp.resolve_right (fun ⟨x, y, hp⟩ => absurd (congrArg List.length hp) (by simp [argWords, wordsFrom, slicebytetostringSpec, stringtoslicebyteSpec]))
  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hargs : argWords s 3 = [0, p, 2] := hp
    simp [stringtoslicebyteSpec, argWords, wordsFrom, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h1, h2⟩ := hp
    have e2 : s.regs 2 = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 1).toNat 2 false = true := by
      have h := hs2 (by omega); rw [h2] at h; exact h
    janus_run [e2]
    apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true]
      rw [or_mul256 _ (byte_lt _) _ (byte_lt _)]
      exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [← h1, or_mul256 _ (byte_lt _) _ (byte_lt _)]
      have hl : (Spec.strBytes s.mem (BitVec.toNat (s.regs 1)) 2).length = 2 := by simp [Spec.strBytes]
      have hr : roundupsize 2 true = 8 := by decide
      refine ⟨by simp [Spec.strBytes], fun h => absurd rfl h, fun _ => ⟨by rw [hl, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
      refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
      · simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
        refine ⟨byte_lt _, ?_⟩
        have := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 1) + 1))
        omega
      · intro i hi
        simp [Arm64.Memory.writeLE]
        rw [if_pos (by omega)]
        have h0b := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 1)))
        have h1b := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 1) + 1))
        have e : 6356994 + i - 6356992 = i + 2 := by omega
        rw [e]
        have hp2 : 256 ^ 2 ≤ 256 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.div_eq_of_lt (by omega)]
  · have hargs : argWords s 3 = [0, p, 4] := hp
    simp [stringtoslicebyteSpec, argWords, wordsFrom, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h1, h2⟩ := hp
    have e2 : s.regs 2 = 4#64 := BitVec.eq_of_toNat_eq (by simpa using h2)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 1).toNat 4 false = true := by
      have h := hs2 (by omega); rw [h2] at h; exact h
    janus_run [e2]
    have hv : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 4 % 18446744073709551616 =
        Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 4 :=
      Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 1)) 4; simp at this; omega)
    apply RtPost.intro <;> (try rfl) <;> (try simp [setReg])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true, hv]
      exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, hv]
      rw [← h1]
      have hl : (Spec.strBytes s.mem (BitVec.toNat (s.regs 1)) 4).length = 4 := by simp [Spec.strBytes]
      have hr : roundupsize 4 true = 8 := by decide
      refine ⟨by simp [Spec.strBytes], fun h => absurd rfl h, fun _ => ⟨by rw [hl, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
      refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
      · exact strBytes4w _ _ _
      · intro i hi
        simp only [Arm64.Memory.writeLE]
        rw [if_pos (by omega)]
        have e : 6356992 + 4 + i - 6356992 = i + 4 := by omega
        rw [e]
        have hp2 : 256 ^ 4 ≤ 256 ^ (i + 4) := Nat.pow_le_pow_right (by omega) (by omega)
        have h256 : (256:Nat) ^ 4 = 4294967296 := by decide
        have hlt32 : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 1)) 4 < 4294967296 := by
          have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 1)) 4; simp at this; omega
        rw [Nat.div_eq_of_lt (by omega)]
        rfl


/-! ### the trivial callees -/

theorem ret_gen {nargs stack : Nat} {rt : List (Nat × Nat)} {Pr : State → Janus.Arm64.Memory → Prop} (s : State)
    (hP : Pr s s.mem) (RG : Nat → W64) (F : Flags)
    (hrel : R0z (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (RG 0) (RG 1) (RG 2))
    (h18 : RG 18 = s.regs 18) (h28 : RG 28 = s.regs 28) (h29 : RG 29 = s.regs 29) (hF : F = s.flags) :
    ICallRetP nargs stack rt (fun _ => []) R0z Pr s { s with regs := RG, flags := F, pc := s.regs 30 } := by
  refine ⟨RG, F, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, by simp, hrel, hP⟩
  simp only [retStateX]
  congr 1
  funext i
  simp only [callRegs]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rcases h with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · simp only [h, ite_false, List.getD_nil]

theorem stub_gen (A : Nat) (hA : A = amA ∨ A = fpAddr ∨ A = bfAddr) (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop)
    (Pr : State → Janus.Arm64.Memory → Prop) (hPr : ∀ s, Pr s s.mem) :
    ICallContract (Extracted.program.link implAll) A nargs stack above rt (fun _ => []) R0z P Pr := by
  rw [linked_eq]
  intro s hpc ⟨⟨hr1, hr2, _⟩, _⟩
  rcases hA with rfl | rfl | rfl
  · have hpc' : s.pc = 0x700000#64 := hpc
    janus_run [hpc']
    all_goals
      apply ret_gen _ (hPr _)
      all_goals simp [setReg, R0z]
  · have hpc' : s.pc = 666928#64 := hpc
    janus_run [hpc']
    all_goals
      apply ret_gen _ (hPr _)
      all_goals simp [setReg, R0z]
  · have hpc' : s.pc = 706368#64 := hpc
    janus_run [hpc']
    all_goals
      apply ret_gen _ (hPr _)
      all_goals simp [setReg, R0z]


/-! ### the allocator `R2` and the type-assertion runtime -/

section Live
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

/-- the requests the witness allocator serves: `IntoBig`'s (the big path's allocations) -/
def okR : Nat → List Nat → Prop := fun a args =>
  (a = newA ∧ (args = [Fv256.Arm64.IntoBig.bigType] ∨ args = [Fv256.Arm64.IntoBig.arrType])) ∨ (a = w1A ∧ args = [1]) ∨ (a = w2A ∧ args = [2])

theorem addr_new : Extracted.program.contractAddr "runtime.newobject" = newA := by decide
theorem addr_w1 : Extracted.program.contractAddr "runtime.gcWriteBarrier1" = w1A := by decide
theorem addr_w2 : Extracted.program.contractAddr "runtime.gcWriteBarrier2" = w2A := by decide

def R2 : RtInv := toyR [] okR

theorem model_new : NewobjectLiveContract (Extracted.program.ofImpl implAll) newA 4096 R2 := by janus_live_newobject
theorem model_wb1 : WbLiveContract (Extracted.program.ofImpl implAll) w1A 4096 R2 1 := by janus_live_wb 1
theorem model_wb2 : WbLiveContract (Extracted.program.ofImpl implAll) w2A 4096 R2 2 := by janus_live_wb 2
end Live

section TA
open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat Janus.Contracts.Iface Janus.Spec.Type

theorem model_ta : TypeAssert (Extracted.program.link implAll) taAddr R0 Hw := by
  rw [linked_eq]
  intro s hpc hpre
  obtain ⟨⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, ⟨hl1, hl2, hal, hd1, hd2, hd3, hst⟩, hout⟩, hdesc, -, -, -⟩ := hpre
  have hi : taInter s.mem (s.regs 0).toNat = ID := hdesc.2.2.2.1
  janus_run
  refine rtReturn_of R0 2 _ s _ _ rfl rfl (by simp [setReg]) (by simp [setReg]) (by simp [setReg])
    rfl rfl rfl rfl rfl rfl (MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
  have := itabResult_R0 (g := s.regs 28) ⟨he1, he2, hd⟩ (s.regs 1).toNat
  refine ⟨?_, hdesc, rfl, rfl⟩
  simp only [setReg_apply, reduceIte, Nat.reduceEqDiff]
  rw [hi]
  have heq : (if (s.regs 1).toNat = 65536 then 66048#64 else 0#64).toNat =
      (if (s.regs 1).toNat = TD then TAB else 0) := by
    simp only [TD, TAB]; split <;> simp_all
  rw [heq]; exact this
end TA

end Fv256.Arm64.FormatWitA
