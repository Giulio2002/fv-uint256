import Extracted
import Fv256.Amd64.ErlpDefs

/-!
# `EncodeRLP` non-vacuity witness material (amd64): a toy `runtime.newobject` and a toy `io.Writer.Write`

The theorem `Witness.nonvacuous` (in `EncodeRLP.lean`) uses these: a concrete call state, a toy allocator linked at the
`runtime.newobject` address, and a toy writer at a code address (`MOV RAX,RCX ; XOR EBX,EBX ; XOR ECX,ECX ; RET`) reached through
the itab word `tab+24`.  The value at `z` is `0x011234`, a 17-bit number: the multi-byte path.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP.Witness

open Janus.Contracts.AllocSatAmd64 (ret_of)
open Janus.Contracts.AllocSat (le_blockSize)

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% tyBig
def tyB : Nat := janus_eval% tyOne
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def A0 : Nat := 0x700000
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16), (tyB, tyB + 16)]
def stack : Nat := 4104

def writerCode : List Nat := [0x48, 0x89, 0xc8, 0x31, 0xdb, 0x31, 0xc9, 0xc3]

/-- toy allocator `mov $0x10000, %eax; ret` and toy writer -/
def impl : List Amd64.Segment :=
  [{ name := "witness.newobject", base := cA, bytes := [0xb8, 0x00, 0x00, 0x01, 0x00, 0xc3] },
   { name := "witness.writer", base := A0, bytes := writerCode }]

def H : RtReady := fun args _ _ v =>
  (v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000) ∧
    ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768

/-- the writer's relation: it returns `(len, nil)` -/
def R0 : Res := fun _ _ a2 _ n e1 e2 => n = a2 ∧ e1 = 0 ∧ e2 = 0

def linked : Amd64.Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem hnew : NewobjectContract64 (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨hra, hal, _, _, _⟩, _, _⟩, hr, typ, hargs, hin, hsz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus64_run
  refine ⟨BitVec.ofNat 64 heap, _, _, _, _, _, _, _, ret_of s _ [BitVec.ofNat 64 heap]
    (by simp [retAddrOf]) (by simp [setRegF]) (by simp [setRegF]) (by simp [setRegF])
    (by simp [setRegF, heap]) (by simp) (by simp) rfl rfl rfl rfl rfl,
    ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, fun _ => ?_⟩
  unfold typSize at hsz
  rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
  change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
  have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
    (typNoscan s.mem (s.regs 0).toNat) hsz
  simp only [maxSmallSize] at hb
  have hle := le_blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat)
  have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
  rw [hheap]
  obtain ⟨hacc, hz⟩ := hr
  rw [rtView_accessible] at hacc
  have hz' := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
  refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
    by simp only [heap]; omega, Janus.Arm64.Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega),
    fun _ => by decide, fun _ _ => by decide, fun _ => fun i hi => hz' i (by omega), hle⟩

/-- the abstract writer's return state -/
theorem wret_of {st : Nat} (s : State) (R : Nat → W64) (F : Flags) (h0 : R 0 = s.regs 1) (h3 : R 3 = 0) (h1 : R 1 = 0)
    (h4 : R 4 = s.regs 4 + 8#64) (h5 : R 5 = s.regs 5) (h14 : R 14 = s.regs 14) :
    ICallRet64 4 st rt (fun _ => []) R0 s { s with regs := R, flags := F, rip := retAddrOf s } := by
  refine ⟨R, F, s.xmm, s.ymmHi, s.mem, s.zmmHi, s.kreg, ?_, MemFrame.refl _ _, by simp, ?_⟩
  · simp only [retState64]
    congr 1
    · funext i
      simp only [callRegs64]
      by_cases e4 : i = 4
      · subst e4; simp [h4]
      by_cases e5 : i = 5 ∨ i = 14
      · rcases e5 with rfl | rfl <;> simp [h5, h14]
      simp only [e4, e5, ite_false]
      by_cases e0 : i = 0
      · subst e0; simp [h0]
      by_cases e3 : i = 3
      · subst e3; simp [h3]
      by_cases e1 : i = 1
      · subst e1; simp [h1]
      simp [e0, e3, e1]
    · funext i; split <;> simp_all
  · exact ⟨h0, h3, h1⟩

theorem hw (z w : BitVec 64) : ICallContract64 (Extracted.program.link impl) A0 4 stack 56 rt (fun _ => []) R0 (WP z w) := by
  intro s hpc ⟨⟨hr, _, hst, _, hw⟩, _⟩
  have hacc : s.mem.accessible (s.regs 4).toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ (Janus.Arm64.Memory.accessible_read_of_write _ hw) (by omega) (by omega)
  have hpc' : s.rip = BitVec.ofNat 64 A0 := hpc
  change ReachesRet linked _ s _
  janus64_run [hpc']
  all_goals
    apply wret_of
    all_goals simp [setRegF]

def retA : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def tabp : Nat := 0x31000
def dsegs : List DataSegment := Extracted.data

/-- the memory: the zeroed heap, the return address, `*z = 0x011234` (a 17-bit number), the itab word `tab+24 = A0`, the data objects -/
def bytes (a : Nat) : Byte :=
  if heap ≤ a ∧ a < heap + 0x10000 then 0 else
  if a = sp0 + 2 then 0x20 else
  if a = zp then 0x34 else if a = zp + 1 then 0x12 else if a = zp + 2 then 0x01 else
  if a = tabp + 26 then 0x70 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def zA : BitVec 64 := BitVec.ofNat 64 zp
def tabA : BitVec 64 := BitVec.ofNat 64 tabp
def wA : BitVec 64 := 0x777

def s0 : Amd64.State :=
  { regs := fun i => if i = 0 then zA else if i = 3 then tabA else if i = 1 then wA else if i = 4 then BitVec.ofNat 64 sp0
      else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 4160, 4192, true⟩, ⟨g0, 0x100, false⟩, ⟨heap, 0x10000, true⟩, ⟨zp, 0x100, false⟩,
      ⟨tabp, 0x100, false⟩] ++ dregs⟩ }

theorem hret : RetAddr linked retA := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit retA) Extracted.entry [zA, tabA, wA] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h
    match i, h with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Amd64.Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH (ty : Nat) (hty : ty = tyA ∨ ty = tyB) :
    H [ty] (s0.regs 14).toNat ((s0.regs 4).toNat - 56) (rtView rt s0.mem) := by
  have hbase : ∀ d ∈ dsegs, 0x20000 ≤ d.base := by simp only [dsegs]; decide
  refine ⟨⟨by rw [rtView_accessible]; decide, fun i hi => ?_⟩, ty, rfl, ?_, ?_⟩
  · show (if _ then bytes (heap + i) else 0) = 0
    split
    · have hh : heap = 65536 := rfl
      simp only [bytes]
      rw [if_pos (show heap ≤ heap + i ∧ heap + i < heap + 0x10000 from ⟨by omega, by omega⟩)]
    · rfl
  · rcases hty with rfl | rfl
    · exact ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨(tyB, tyB + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
  · rcases hty with rfl | rfl <;> decide

set_option maxRecDepth 100000 in
theorem pre : 4104 ≤ stack ∧ A0 < 2 ^ 47 ∧
    StackGuardOK s0 0 ∧ StackWritable s0 (56 + stack) 32 ∧ SPAligned s0 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside ((s0.regs 4).toNat - 56 - stack) (stack + 88) rt ∧
    (zA = 0 ∨ (Buffer s0 zA 32 false ∧ Outside zA.toNat 32 rt ∧
      (zA.toNat + 32 ≤ (s0.regs 4).toNat - 56 - stack ∨ (s0.regs 4).toNat + 32 ≤ zA.toNat))) ∧
    (tabA.toNat + 32 ≤ (s0.regs 4).toNat - 56 - stack ∨ (s0.regs 4).toNat + 32 ≤ tabA.toNat + 24) ∧
    tabA.toNat + 32 ≤ 2 ^ 48 ∧ s0.mem.accessible (tabA.toNat + 24) 8 false = true ∧ Outside (tabA.toNat + 24) 8 rt ∧
    s0.mem.readLE (tabA.toNat + 24) 8 = A0 ∧
    H [tyBig] (s0.regs 14).toNat ((s0.regs 4).toNat - 56) (rtView rt s0.mem) ∧
    H [tyOne] (s0.regs 14).toNat ((s0.regs 4).toNat - 56) (rtView rt s0.mem) :=
  ⟨by decide, by decide, ⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩,
    ⟨by decide, by decide, by decide⟩, by simp only [SPAligned]; decide, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide,
    Or.inr ⟨⟨by decide, by decide⟩, by simp only [rt, outside_cons, outside_nil]; decide, Or.inl (by decide)⟩,
    Or.inl (by decide), by decide, by decide, by simp only [rt, outside_cons, outside_nil]; decide, by decide,
    hH tyBig (Or.inl rfl), hH tyOne (Or.inr rfl)⟩

end Fv256.Amd64.EncodeRLP.Witness
