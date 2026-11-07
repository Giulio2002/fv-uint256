import Extracted
import Fv256.Arm64.FormatWitB

/-!
# Format witness, part G: the big-path witness (arm64)

The same environment as the fast witness, but the callees answer "has width" (`X1 = 1`): the first query sends the machine to the big path.
The runtime pieces (`implAllG`, the string runtime, the type-assertion model, the toy allocator's contracts) are re-proved over the changed
segment list.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.Arm64.FormatWitA Fv256.Arm64.FormatWitB Fv256.Arm64.FormatTransfer Fv256.FormatFastA64

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace Fv256.Arm64.FormatWitG

section Rest
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

/-- `mov x0, xzr ; mov x1, #1 ; ret` -/
def oneWords : List Nat := [0xaa1f03e0, 0xd2800021, 0xd65f03c0]

/-- the answer of the "has width" callees: `X0 = 0`, `X1 = 1` -/
def R0w : Res := fun _ _ _ _ j0 j1 _ => j0 = 0 ∧ j1 = 1

def implAllG : List Segment :=
  [{ name := "model-sbts", base := ssAddr, words := ss24Words }, { name := "model-stb", base := stAddr, words := st24Words },
   { name := "model-ta", base := taAddr, words := Janus.Contracts.IfaceSat.assertE2I2Code },
   newobjectSeg newA, wbSeg w1A, wbSeg w2A,
   { name := "model-am", base := amA, words := oneWords }, { name := "model-fp", base := fpAddr, words := zeroWords },
   { name := "model-bf", base := bfAddr, words := zeroWords }]

theorem implOKG : ImplApart Extracted.program implAllG := by
  unfold ImplApart; constructor <;> decide

end Rest

def linkedG : Program := { Extracted.program with segments := Extracted.program.segments ++ implAllG }
theorem linkedG_eq : Extracted.program.link implAllG = linkedG := rfl
def linkedOG : Program := { Extracted.program with segments := implAllG }
theorem ofImplG_eq : Extracted.program.ofImpl implAllG = linkedOG := rfl

theorem model1G : RtContract (Extracted.program.ofImpl implAllG) ssAddr rtT 4096 Hw
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [ofImplG_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw, rtView_acc] at ha
  obtain ⟨hpp, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
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


theorem model2G : RtContract (Extracted.program.ofImpl implAllG) stAddr rtT 4096 Hw stringtoslicebyteSpec := by
  rw [ofImplG_eq]
  rintro s hpc ⟨⟨h30a, h30b, -⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready, Hw, rtView_acc] at ha
  obtain ⟨hpp, hA8, hB8⟩ := ha
  simp only [hA, hB] at hA8 hB8
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



theorem ret_genG {nargs stack : Nat} {rt : List (Nat × Nat)} {Pr : State → Janus.Arm64.Memory → Prop} (RR : Res) (s : State)
    (hP : Pr s s.mem) (RG : Nat → W64) (F : Flags)
    (hrel : RR (s.regs 0) (s.regs 1) (s.regs 2) (s.regs 3) (RG 0) (RG 1) (RG 2))
    (h18 : RG 18 = s.regs 18) (h28 : RG 28 = s.regs 28) (h29 : RG 29 = s.regs 29) (hF : F = s.flags) :
    ICallRetP nargs stack rt (fun _ => []) RR Pr s { s with regs := RG, flags := F, pc := s.regs 30 } := by
  refine ⟨RG, F, s.vregs, s.mem, s.excl, s.exclPass, ?_, MemFrame.refl _ _, by simp, hrel, hP⟩
  simp only [retStateX]
  congr 1
  funext i
  simp only [callRegs]
  by_cases h : i = 18 ∨ i = 28 ∨ i = 29
  · rcases h with rfl | rfl | rfl <;> simp [h18, h28, h29]
  · simp only [h, ite_false, List.getD_nil]

theorem stub_am1 (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop)
    (Pr : State → Janus.Arm64.Memory → Prop) (hPr : ∀ s, Pr s s.mem) :
    ICallContract (Extracted.program.link implAllG) amA nargs stack above rt (fun _ => []) R0w P Pr := by
  rw [linkedG_eq]
  intro s hpc ⟨⟨hr1, hr2, _⟩, _⟩
  have hpc' : s.pc = 0x700000#64 := hpc
  janus_run [hpc']
  all_goals
    apply ret_genG _ _ (hPr _)
    all_goals simp [setReg, R0w]

theorem stub_fpbf (A : Nat) (hA : A = fpAddr ∨ A = bfAddr) (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop)
    (Pr : State → Janus.Arm64.Memory → Prop) (hPr : ∀ s, Pr s s.mem) :
    ICallContract (Extracted.program.link implAllG) A nargs stack above rt (fun _ => []) R0z P Pr := by
  rw [linkedG_eq]
  intro s hpc ⟨⟨hr1, hr2, _⟩, _⟩
  rcases hA with rfl | rfl
  · have hpc' : s.pc = 666928#64 := hpc
    janus_run [hpc']
    all_goals
      apply ret_genG _ _ (hPr _)
      all_goals simp [setReg, R0z]
  · have hpc' : s.pc = 706368#64 := hpc
    janus_run [hpc']
    all_goals
      apply ret_genG _ _ (hPr _)
      all_goals simp [setReg, R0z]

section Live
open Janus.Contracts.Toy Janus.Contracts.LiveSat Janus.Contracts.LiveStub

theorem model_newG : NewobjectLiveContract (Extracted.program.ofImpl implAllG) newA 4096 R2 := by janus_live_newobject
theorem model_wb1G : WbLiveContract (Extracted.program.ofImpl implAllG) w1A 4096 R2 1 := by janus_live_wb 1
theorem model_wb2G : WbLiveContract (Extracted.program.ofImpl implAllG) w2A 4096 R2 2 := by janus_live_wb 2
end Live

section TA
open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSat Janus.Contracts.Iface Janus.Spec.Type

theorem model_taG : TypeAssert (Extracted.program.link implAllG) taAddr R0 Hw := by
  rw [linkedG_eq]
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


theorem hretG : RetAddr linkedG ret := RetAddr.of_check (by decide)

theorem setupG : CallSetup (linkedG.withExit ret) Extracted.entry [zV, tabV, dataV, chV] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | _ | _ | _ | r <;> simp [s0] at h ⊢ <;> omega⟩

open Janus.Contracts.IfaceModel Janus.Spec.Type in
theorem big_core : ∃ (impl : List Segment) (R : IfaceModel) (H : RtReady) (R2 : RtInv) (rt : List (Nat × Nat))
    (fa : Nat) (Rc Rd : Res) (z tab data ch : BitVec 64) (ret : Nat) (s : State),
    (ImplApart Extracted.program impl ∧ R.Laws ∧
    Janus.Contracts.Iface.TypeAssert (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.typeAssert") R H ∧
    NewobjectLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.newobject") 4096 R2 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R2 1 ∧
    WbLiveContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R2 2 ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.slicebytetostring") rt 4096 H
      (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») ∧
    RtContract (Extracted.program.ofImpl impl) (Extracted.program.contractAddr "runtime.stringtoslicebyte") rt 4096 H
      stringtoslicebyteSpec ∧
    4608 ≤ 4608 ∧
    ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)) ∧
    (ICallContract (Extracted.program.link impl) fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2) ∧
    ICallContract (Extracted.program.link impl) fa 4 4608 120 rt (fun _ => []) Rc
      (FastWP data (Fv256.FormatSpec.fastBytes 16 (ch.toNat % 2 ^ 32))) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "fmt.Fprint") 5 4608 80 rt (fun _ => [])
      Rd (Fv256.Arm64.FormatNil.FpArg data) ∧
    ICallContract (Extracted.program.link impl) (Extracted.program.contractAddr "math/big.(*Int).Format") 4 4608 120 rt (fun _ => [])
      Rd (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P 16 ∧ sc.regs 1 = tab ∧ sc.regs 2 = data ∧
        (sc.regs 3).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z, tab, data, ch] s ∧
    PreF R H R2 rt 4608 0x400 fa fa fa fa 16 z tab data s ∧
    NotPlain Rc Rc Rc data fa fa fa ch (ch.toNat % 2 ^ 32) ∧
    (∃ (P : Nat) (j0 j1 j2 : BitVec 64), Rd (BitVec.ofNat 64 P) tab data
      (BitVec.ofNat 64 (if ch.toNat % 2 ^ 32 < 2 ^ 31 then ch.toNat % 2 ^ 32 else ch.toNat % 2 ^ 32 + 18446744069414584320)) j0 j1 j2) ) := by
  refine ⟨implAllG, R0, Hw, R2, rtT, amA, R0w, R0z, zV, tabV, dataV, chV, ret, s0,
    ⟨implOKG, Janus.Contracts.IfaceModel.R0_laws, by rw [addr_ta]; exact model_taG, by rw [addr_new]; exact model_newG, by rw [addr_w1]; exact model_wb1G, by rw [addr_w2]; exact model_wb2G, model1G, model2G, by decide, stub_am1 _ _ _ _ _ _ (fun s b L h => h)⟩,
    ⟨stub_am1 _ _ _ _ _ _ (fun s b L h => h), stub_am1 _ _ _ _ _ _ (fun s b L h => h), stub_am1 _ _ _ _ _ _ (fun _ => trivial), by rw [addr_fp]; exact stub_fpbf fpAddr (Or.inl rfl) _ _ _ _ _ _ (fun _ => trivial), by rw [addr_bf]; exact stub_fpbf bfAddr (Or.inr rfl) _ _ _ _ _ _ (fun _ => trivial), by rw [linkedG_eq]; exact hretG, by rw [linkedG_eq]; exact setupG, pre, Or.inl ⟨1, ⟨0, 0, ⟨rfl, rfl⟩⟩, by decide⟩, ⟨0, 0, 0, 0, ⟨rfl, rfl⟩⟩⟩⟩

end Fv256.Arm64.FormatWitG
