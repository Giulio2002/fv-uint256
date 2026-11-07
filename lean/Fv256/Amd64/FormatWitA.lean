import Extracted
import Fv256.Amd64.FormatTransfer
import Fv256.ToyRuntime64

/-!
# Format witness, part A: the toy string runtime (lengths 2 and 4) and the trivial callees (amd64)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Contracts Janus.Contracts.ICall
open Fv256.ToyRuntime64

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Fv256.Amd64.FormatWitA

abbrev ssAddr : Nat := Extracted.program.contractAddr "runtime.slicebytetostring"
abbrev stAddr : Nat := Extracted.program.contractAddr "runtime.stringtoslicebyte"

def hA : Nat := 0x600000
def hB : Nat := 0x610000
def rtT : List (Nat × Nat) := [(hA, hA + 8), (hB, hB + 8)]

/-- `slicebytetostring(0, ptr, n)` for `n = 2` or `n = 4`: bytes copied to the block `h`, returns `(h, n)` -/
def ss24Code (h : Nat) : List Nat :=
  [0x48, 0x83, 0xf9, 0x02, 0x75, 0x1c] ++ sbts2Code h ++
  [0x8b, 0x03, 0xbf] ++ le32 h ++ [0x89, 0x07, 0xb8] ++ le32 h ++ [0xbb, 4, 0, 0, 0, 0xc3]

/-- `stringtoslicebyte(0, ptr, n)` for `n = 2` or `n = 4`: the bytes zero-extended into the word at `h`, returns `(h, n, 8)` -/
def st24Code (h : Nat) : List Nat :=
  [0x48, 0x83, 0xf9, 0x02, 0x75, 0x24] ++ stb2Code h ++
  [0x8b, 0x03, 0xbf] ++ le32 h ++ [0x48, 0x89, 0x07, 0xb8] ++ le32 h ++ [0xbb, 4, 0, 0, 0, 0xb9, 8, 0, 0, 0, 0xc3]

theorem sbts2_len (h : Nat) : (sbts2Code h).length = 28 := by simp [sbts2Code, le32]
theorem stb2_len (h : Nat) : (stb2Code h).length = 36 := by simp [stb2Code, le32]


def Hw : RtReady := fun a _ sp view =>
  ((∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, p, 4])) ∧ view.accessible hA 8 true = true ∧ view.accessible hB 8 true = true ∧
    (sp + 8 ≤ hA ∨ hA + 8 ≤ sp) ∧ (sp + 8 ≤ hB ∨ hB + 8 ≤ sp)

/-! ### the rest of the runtime and the trivial callees -/

section Rest
open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64

abbrev taAddr : Nat := Extracted.program.contractAddr "runtime.typeAssert"
abbrev fpAddr : Nat := Extracted.program.contractAddr "fmt.Fprint"
abbrev bfAddr : Nat := Extracted.program.contractAddr "math/big.(*Int).Format"
def newA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def w1A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier1")
def w2A : Nat := janus_eval% (Extracted.program.contractAddr "runtime.gcWriteBarrier2")
def amA : Nat := 0x700000

/-- `xor eax,eax ; xor ebx,ebx ; ret` -/
def zeroCode : List Nat := [0x31, 0xc0, 0x31, 0xdb, 0xc3]

/-- the answer of the trivial callees: `RAX = RBX = 0` -/
def R0z : Res := fun _ _ _ _ j0 j3 _ => j0 = 0 ∧ j3 = 0

def implAll : List Amd64.Segment :=
  [{ name := "model-sbts", base := ssAddr, bytes := ss24Code hA }, { name := "model-stb", base := stAddr, bytes := st24Code hB },
   { name := "model-ta", base := taAddr, bytes := Janus.Contracts.IfaceSatAmd64.assertE2I2Code },
   newobjectSeg newA, wbSeg w1A, wbSeg w2A,
   { name := "model-am", base := amA, bytes := zeroCode }, { name := "model-fp", base := fpAddr, bytes := zeroCode },
   { name := "model-bf", base := bfAddr, bytes := zeroCode }]

set_option maxRecDepth 100000 in
theorem implOK : Amd64.ImplApart Extracted.program implAll := by
  unfold Amd64.ImplApart; constructor <;> decide

end Rest

def linked : Amd64.Program := { Extracted.program with segments := Extracted.program.segments ++ implAll }
theorem linked_eq : Extracted.program.link implAll = linked := rfl
def linkedO : Amd64.Program := { Extracted.program with segments := implAll }
theorem ofImpl_eq : Extracted.program.ofImpl implAll = linkedO := rfl

theorem rtView_acc (m : Janus.Arm64.Memory) (a n : Nat) (w : Bool) : (rtView rtT m).accessible a n w = m.accessible a n w :=
  Janus.Arm64.Memory.accessible_congr rfl a n w

theorem byte_lt (b : BitVec 8) : b.toNat < 256 := by have := b.isLt; simpa using this

theorem strBytes4 (m : Janus.Arm64.Memory) (a p : Nat) :
    Spec.strBytes (m.writeLE a 4 (m.readLE p 4)) a 4 = Spec.strBytes m p 4 := by
  have h0 := byte_lt (m.bytes p)
  have h1 := byte_lt (m.bytes (p + 1))
  have h2 := byte_lt (m.bytes (p + 2))
  have h3 := byte_lt (m.bytes (p + 3))
  simp [Spec.strBytes, List.range_succ, Janus.Arm64.Memory.writeLE, Janus.Arm64.Memory.readLE_succ]
  simp only [show p + 1 + 1 = p + 2 from rfl, show p + 1 + 1 + 1 = p + 3 from rfl]
  omega

theorem model1 : RtContract64 (Extracted.program.ofImpl implAll) ssAddr rtT 4096 Hw
    (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») := by
  rw [ofImpl_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw, rtView_acc] at ha
  obtain ⟨hpp, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hargs : argWords64 s 3 = [0, p, 2] := hp
    simp [slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h3, h1⟩ := hp
    have e1 : s.regs 1 = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 3).toNat 2 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
    janus64_run [e1]
    apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, if_true]
      refine MemFrame.trans (rs := rtIf true rtT ++ (calleeStack64 s 4096 3 ++ []))
        (MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega))
        (MemFrame.of_writeLE _ _ (rs := rtIf true rtT ++ (calleeStack64 s 4096 3 ++ [])) (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega)) ?_
      intro a n h; exact ⟨h, h⟩
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
      · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
      · rw [← h3]
        simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
      · right; right; right
        exact ⟨Nat.le_refl _, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩
  · have hargs : argWords64 s 3 = [0, p, 4] := hp
    simp [slicebytetostringSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h3, h1⟩ := hp
    have e1 : s.regs 1 = 4#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 3).toNat 4 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
    janus64_run [e1]
    apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true]
      exact MemFrame.trans (rs := rtIf true rtT ++ (calleeStack64 s 4096 3 ++ []))
        (MemFrame.of_writeLE s.mem _ (r := (6291456, 6291464)) (by simp [rtIf, rtT, hA]) (by omega) (by omega))
        (MemFrame.refl _ _) (fun a n h => ⟨h, h⟩)
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      refine ⟨⟨trivial, ?_, ?_⟩, ?_⟩
      · exact accessible_sub hA8 (Or.inl rfl) (by omega) (by omega)
      · rw [← h3]; exact strBytes4 _ _ _
      · right; right; right
        exact ⟨by omega, Or.inl rfl, (6291456, 6291464), by simp [rtT, hA], by omega, by omega⟩


theorem or_shift8 : ∀ a, a < 256 → ∀ b, b < 256 → (a % 4294967296 ||| (b % 4294967296) <<< 8 % 4294967296) = a + 256 * b := by
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

theorem model2 : RtContract64 (Extracted.program.ofImpl implAll) stAddr rtT 4096 Hw stringtoslicebyteSpec := by
  rw [ofImpl_eq]
  rintro s hpc ⟨⟨hra, hal, hsb, hsa, hacc⟩, ⟨hbuf, hstr, hdis⟩, -, -, hH⟩
  have ha := ready_of rfl hH
  simp only [Ready64, Hw, rtView_acc] at ha
  obtain ⟨hpp, hA8, hB8, hdA, hdB⟩ := ha
  simp only [hA, hB] at hA8 hB8 hdA hdB
  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩
  · have hargs : argWords64 s 3 = [0, p, 2] := hp
    simp [stringtoslicebyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h3, h1⟩ := hp
    have e1 : s.regs 1 = 2#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 3).toNat 2 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
    janus64_run [e1]
    apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true]
      rw [or_shift8 _ (byte_lt _) _ (byte_lt _)]
      exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
      rw [← h3, or_shift8 _ (byte_lt _) _ (byte_lt _)]
      have hl : (Spec.strBytes s.mem (BitVec.toNat (s.regs 3)) 2).length = 2 := by simp [Spec.strBytes]
      have hr : roundupsize 2 true = 8 := by decide
      refine ⟨by simp [Spec.strBytes], fun h => absurd rfl h, fun _ => ⟨by rw [hl, hr], fun _ => ⟨⟨(6356992, 6357000), by simp [rtT, hB], by omega, by omega⟩, ?_⟩⟩⟩
      refine ⟨by omega, by omega, by simpa using accessible_sub hB8 (Or.inr rfl) (by omega) (by omega), ?_, ?_⟩
      · simp [Spec.strBytes, List.range_succ, Arm64.Memory.writeLE]
        refine ⟨byte_lt _, ?_⟩
        have := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3) + 1))
        omega
      · intro i hi
        simp [Arm64.Memory.writeLE]
        rw [if_pos (by omega)]
        have h0b := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3)))
        have h1b := byte_lt (s.mem.bytes (BitVec.toNat (s.regs 3) + 1))
        have e : 6356994 + i - 6356992 = i + 2 := by omega
        rw [e]
        have hp2 : 256 ^ 2 ≤ 256 ^ (i + 2) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.div_eq_of_lt (by omega)]
  · have hargs : argWords64 s 3 = [0, p, 4] := hp
    simp [stringtoslicebyteSpec, argWords64, wordsFrom, GoABI.argReg, GoABI.intArgRegs, arg] at hp hstr hbuf hdis
    obtain ⟨h0, h3, h1⟩ := hp
    have e1 : s.regs 1 = 4#64 := BitVec.eq_of_toNat_eq (by simpa using h1)
    obtain ⟨hs1, hs2⟩ := hstr
    have hacc2 : s.mem.accessible (s.regs 3).toNat 4 false = true := hs2 (by omega) |> fun h => by rw [h1] at h; exact h
    janus64_run [e1]
    have hv : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 4 % 4294967296 =
        Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 4 :=
      Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 4; simpa using this)
    have hlt : Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 4 < 4294967296 := by
      have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 4; simpa using this
    apply RtPost64.intro <;> (try rfl) <;> (try simp [retAddrOf]) <;> (try simp [setRegF])
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, ite_true, hv]
      exact MemFrame.of_writeLE s.mem _ (r := (6356992, 6357000)) (by simp [rtIf, rtT, hB]) (by omega) (by omega)
    · rw [hargs]
      simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, hv]
      rw [← h3]
      have hl : (Spec.strBytes s.mem (BitVec.toNat (s.regs 3)) 4).length = 4 := by simp [Spec.strBytes]
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
        rw [Nat.div_eq_of_lt (by omega)]
        rfl




/-! ### the trivial callees -/

theorem ret_gen {nargs stack : Nat} {rt : List (Nat × Nat)} {Pr : State → Janus.Arm64.Memory → Prop} (s : State)
    (hP : Pr s s.mem) (RG : Nat → W64) (F : Flags)
    (hrel : R0z (s.regs 0) (s.regs 3) (s.regs 1) (s.regs 7) (RG 0) (RG 3) (RG 1))
    (h4 : RG 4 = s.regs 4 + 8#64) (h5 : RG 5 = s.regs 5) (h14 : RG 14 = s.regs 14) :
    ICallRetP64 nargs stack rt (fun _ => []) R0z Pr s { s with regs := RG, flags := F, rip := retAddrOf s } := by
  refine ⟨RG, F, s.xmm, s.ymmHi, s.mem, s.zmmHi, s.kreg, ?_, MemFrame.refl _ _, by simp, hrel, hP⟩
  simp only [retState64]
  congr 1
  · funext i
    simp only [callRegs64]
    by_cases e4 : i = 4
    · subst e4; simp [h4]
    by_cases e5 : i = 5 ∨ i = 14
    · rcases e5 with rfl | rfl <;> simp [h5, h14]
    simp only [e4, e5, ite_false]
    by_cases e0 : i = 0
    · subst e0; simp
    by_cases e3 : i = 3
    · subst e3; simp
    by_cases e1 : i = 1
    · subst e1; simp
    simp [e0, e3, e1]
  · funext i; split <;> simp_all

theorem stub_am (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop)
    (Pr : State → Janus.Arm64.Memory → Prop) (hPr : ∀ s, Pr s s.mem) :
    ICallContract64 (Extracted.program.link implAll) amA nargs stack above rt (fun _ => []) R0z P Pr := by
  rw [linked_eq]
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, _⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hpc' : s.rip = BitVec.ofNat 64 amA := hpc
  janus64_run [hpc']
  all_goals
    apply ret_gen
    all_goals first | exact hPr _ | simp [setRegF, R0z]

theorem stub_fp (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop)
    (Pr : State → Janus.Arm64.Memory → Prop) (hPr : ∀ s, Pr s s.mem) :
    ICallContract64 (Extracted.program.link implAll) fpAddr nargs stack above rt (fun _ => []) R0z P Pr := by
  rw [linked_eq]
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, _⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hpc' : s.rip = BitVec.ofNat 64 fpAddr := hpc
  janus64_run [hpc']
  all_goals
    apply ret_gen
    all_goals first | exact hPr _ | simp [setRegF, R0z]

theorem stub_bf (nargs stack above : Nat) (rt : List (Nat × Nat)) (P : State → Prop)
    (Pr : State → Janus.Arm64.Memory → Prop) (hPr : ∀ s, Pr s s.mem) :
    ICallContract64 (Extracted.program.link implAll) bfAddr nargs stack above rt (fun _ => []) R0z P Pr := by
  rw [linked_eq]
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, _⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hpc' : s.rip = BitVec.ofNat 64 bfAddr := hpc
  janus64_run [hpc']
  all_goals
    apply ret_gen
    all_goals first | exact hPr _ | simp [setRegF, R0z]


open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64 in
/-- the requests the witness runtime serves: none (the fast path allocates nothing) -/
def okR : Nat → List Nat → Prop := fun _ _ => False

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64 in
def R2 : RtInv := toyR [] okR

open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64 in
theorem model_new : NewobjectLiveContract64 (Extracted.program.ofImpl implAll) newA 4096 R2 := by janus64_live_newobject
open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64 in
theorem model_wb1 : WbLiveContract64 (Extracted.program.ofImpl implAll) w1A 4096 R2 1 := by janus64_live_wb 1
open Janus.Contracts.Toy Janus.Contracts.LiveSatAmd64 Janus.Contracts.LiveStubAmd64 in
theorem model_wb2 : WbLiveContract64 (Extracted.program.ofImpl implAll) w2A 4096 R2 2 := by janus64_live_wb 2


section TA
open Janus.Contracts.IfaceModel Janus.Contracts.IfaceSatAmd64 Janus.Contracts.IfaceAmd64 Janus.Spec.Type
open Janus.Contracts (IfaceSat.itabAt_TAB IfaceSat.itabResult_R0 IfaceSat.efaceEqual_R0)

theorem model_ta : TypeAssert (Extracted.program.link implAll) taAddr R0 Hw := by
  rw [linked_eq]
  intro s hpc ⟨hpre, hdesc, _, _, _⟩
  obtain ⟨⟨he1, he2, hd⟩, ⟨hg1, hg2, hg3⟩, hal, hd1, hd2, hst, hx15, hdf, hra, hout⟩ := hpre
  simp only [R0_depth, R0_priv, outside_cons, outside_nil, and_true] at hout hd1 hd2 hst
  have hi : taInter s.mem (s.regs 0).toNat = ID := hdesc.2.2.2.1
  have := IfaceSat.itabResult_R0 (g := s.regs 14) ⟨he1, he2, hd⟩ (s.regs 3).toNat
  janus64_run
  all_goals
    refine rtReturn_of R0 2 _ s _ _ (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF])
      (by simp [setRegF]) rfl rfl (by simp [hdf]) rfl rfl (Janus.MemFrame.refl _ _) ⟨he1, he2, hd⟩ ?_
    refine ⟨?_, hdesc, rfl, rfl⟩
    rw [hi]
    simp only [setRegF, reduceIte, Nat.reduceEqDiff, BitVec.toNat_ofNat]
    simp only [TD, TAB] at this
    have hlt := (s.regs 3).isLt
    first
      | (have h3 : (s.regs 3).toNat = 65536 := by omega
         simpa [h3] using this)
      | (have h3 : (s.regs 3).toNat ≠ 65536 := by omega
         simpa [h3] using this)
end TA

end Fv256.Amd64.FormatWitA
