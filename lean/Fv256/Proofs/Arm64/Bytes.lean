import Extracted
import Fv256.Proofs.Arm64.CallSites.Base
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Spec.Arm64.Bytes

/-!
# `(*uint256.Int).Bytes() []byte` (arm64)

**Guarantee.** For every receiver `z` (`X0`), every list `rt` of runtime-owned ranges and **every** implementation of
`runtime.newobject` satisfying the allocation contract (`NewobjectContract`; hypothesis `hnew`), and every Go call whose
stack-growth check falls through (`GuardOK s 0`, stack window `[SP-4176, SP+24)` writable and aligned, outside `rt`), with the 32 bytes at `z`
readable, outside `rt` and outside the stack window: the call returns (no fault, no panic), obeys the ABI, and the result slice
`(X0, X1, X2)` is `(ptr', n, n)` where `n = Fv256.Spec.byteLen v` (`v` the number at `z`, read before the call), `ptr = obj + (32 - n)`
(`obj` when `n = 0`, the Go compiler's pointer mask for empty slices), `obj` a fresh 16-byte aligned 32-byte object inside `rt`, and the
`n` bytes at the result pointer read big-endian as `v`; memory is unchanged outside `rt` and the stack window.

**What is assumed.** Only the contract hypothesis `hnew` for the code linked at `runtime.newobject` (not extracted).

**Non-vacuity.** `Witness.nonvacuous` / `Witness.returns`: a toy allocator is linked at the `runtime.newobject` address; for the number
`0x1234` the call returns a slice of length and capacity 2.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

open Fv256.Arm64.CallSites

namespace Fv256.Arm64.Bytes

set_option hygiene false in
local macro "bltac" : tactic => `(tactic| (
    simp only [Spec.byteLen, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod];
    (try rw [Util.bl_4 _ _ _ _ b0 b1 b2]);
    (try rw [Util.bl_3 _ _ _ b0 b1 b2]);
    (try rw [Util.bl_2 _ _ b0 b1]);
    (try simp only [ne_eq]);
    (repeat' split) <;> omega))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 64000000 in
theorem correctness_proof (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (z : BitVec 64)
    (hnew : NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H) :
    Ensures (Extracted.program.link impl) Extracted.entry [z]
      (fun s => GuardOK s 0 ∧ StackOK s 4176 24 ∧ Extracted.program.DataLoaded s.mem ∧
        Outside (s.sp.toNat - 4176) 4200 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
        Disjoint z.toNat 32 (s.sp.toNat - 4176) 4200 ∧
        H [intType] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt s.mem))
      (fun s s' => ∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
        (s'.regs 0).toNat = ptr + (if Spec.byteLen (val256 s.mem z.toNat) = 0 then 0 else 32 - Spec.byteLen (val256 s.mem z.toNat)) ∧
        (s'.regs 1).toNat = Spec.byteLen (val256 s.mem z.toNat) ∧ (s'.regs 2).toNat = Spec.byteLen (val256 s.mem z.toNat) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + (if Spec.byteLen (val256 s.mem z.toNat) = 0 then 0 else 32 - Spec.byteLen (val256 s.mem z.toNat)) + i) 1) (Spec.byteLen (val256 s.mem z.toNat)) = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4176, s.sp.toNat + 24)])) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hout, ⟨hz, hz'⟩, hzo, hzd, hH⟩
  janus_intro hs
  janus_eval_nat h_pt : intType
  rw [h_pt] at hH
  janus_data hd [hw]
  simp only [Disjoint] at hzd
  janus_run until [Extracted.entry + 0x28] calls [hnew.pos]
  rename_i wobj wregs wflags wvreg wmem wo wx hmf hin hle hacc h8 h16 hzb htr
  have hdj := InRanges.disjoint hin hout
  have hdz := InRanges.disjoint hin hzo
  janus_run
  all_goals
    have b0 := Util.readLE8_lt s.mem z.toNat
    have b1 := Util.readLE8_lt s.mem (z.toNat + 8)
    have b2 := Util.readLE8_lt s.mem (z.toNat + 16)
    have b3 := Util.readLE8_lt s.mem (z.toNat + 24)
    have c0 := Util.clz_bl 64 (s.mem.readLE z.toNat 8) b0
    have c1 := Util.clz_bl 64 (s.mem.readLE (z.toNat + 8) 8) b1
    have c2 := Util.clz_bl 64 (s.mem.readLE (z.toNat + 16) 8) b2
    have c3 := Util.clz_bl 64 (s.mem.readLE (z.toNat + 24) 8) b3
    (try simp (disch := (simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; clear hzd hdj hdz h_ddisj0_0; omega)) only [Util.blS_zero', BitVec.add_zero, Util.bl7_asr, Util.bl7_r] at hbr ⊢)
    (try simp only [BitVec.toNat_ofNat, BitVec.toNat_sub, BitVec.toNat_add, Nat.reducePow, Nat.reduceMod] at hbr)
    first
      | (clear hzd hdj hdz h_ddisj0_0; omega)
      | (refine ⟨_, hin, h16, hacc, ?_, ?_, ?_, ?_, ?_⟩
         · simp (disch := (simp only [Spec.byteLen, BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]; clear hzd hdj hdz h_ddisj0_0; omega)) only [Util.mask_asr]
           simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
           clear hzd hdj hdz h_ddisj0_0
           refine Util.ptr_arith _ _ _ _ hle ?_ ?_ ?_ <;> bltac
         · clear hzd hdj hdz h_ddisj0_0
           bltac
         · clear hzd hdj hdz h_ddisj0_0
           bltac
         · clear hzd hdz h_ddisj0_0
           split
           · rename_i hb0
             rw [hb0]; simp only [Spec.fromBE]; exact (Util.byteLen_zero _ hb0).symm
           · rename_i hb0
             refine Util.suffix_be _ _ _ _ ?_ (Util.lt_pow_byteLen _) ?_
             · bltac
             · rw [Util.be32_rev]
               simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
               simp (disch := exact Util.readLE8_lt _ _) only [Nat.reducePow, Nat.zero_mod, Util.rc_rev8, Util.rev8_rev8, Util.rev8_zero]
               (try simp only [Nat.zero_mul, Nat.zero_add]) <;> (try ac_rfl)
         · janus_frame)

namespace Wit

open Janus.Contracts.IfaceModel

def heap : Nat := 0x10000
def tyA : Nat := janus_eval% intType
def cA : Nat := janus_eval% (Extracted.program.contractAddr "runtime.newobject")
def rt : List (Nat × Nat) := [(heap, heap + 0x10000), (tyA, tyA + 16)]

/-- A toy allocator at the runtime.newobject address: `MOVZ X0, #1, LSL #16; RET` (returns the heap at `0x10000`). -/
def impl : List Segment :=
  [{ name := "witness.newobject", base := cA, words := [0xd2a00020, 0xd65f03c0] }]

def H : RtReady := fun args _ _ v =>
  ∃ typ, args = [typ] ∧ InRanges typ 16 rt ∧ typSize v typ ≤ 32768 ∧
    v.accessible heap 0x10000 true = true ∧ ZeroBytes v heap 0x10000

def linked : Program := Extracted.program.link impl

theorem addr : Extracted.program.contractAddr "runtime.newobject" = cA := by decide

theorem callRegs_eq (r : Nat → W64) :
    callRegs r r [BitVec.ofNat 64 heap] = setReg r 0 (BitVec.ofNat 64 heap) := by
  funext i
  simp only [callRegs, setReg]
  rcases i with _ | i
  · rfl
  · simp only [List.getD_cons_succ, List.getD_nil]
    split <;> rfl

theorem hnew : NewobjectContract (Extracted.program.link impl)
    (Extracted.program.contractAddr "runtime.newobject") rt 4096 H := by
  rw [addr]
  intro s hpc ⟨⟨⟨h30a, h30b, _, _, _, _, _⟩, _, _⟩, typ, hargs, hin, hsz, hacc, hz⟩
  simp only [List.cons.injEq, and_true] at hargs
  subst hargs
  change ReachesRet linked _ s _
  janus_run
  refine ⟨BitVec.ofNat 64 heap, s.regs, s.flags, s.vregs, s.mem, s.excl, s.exclPass, ?_, ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩,
    fun hpos => ?_⟩
  · simp only [retStateX]; rw [callRegs_eq]; rfl
  · unfold typSize at hsz
    rw [readLE_rtView (hin.sub (Nat.le_refl _) (by omega))] at hsz
    change typSize s.mem (s.regs 0).toNat ≤ 32768 at hsz
    have hb := blockSize_le_maxSmallSize (typSize s.mem (s.regs 0).toNat)
      (typNoscan s.mem (s.regs 0).toNat) hsz
    have hle : typSize s.mem (s.regs 0).toNat ≤
        blockSize (typSize s.mem (s.regs 0).toNat) (typNoscan s.mem (s.regs 0).toNat) := by
      unfold blockSize; split
      · exact Nat.le_refl _
      · exact le_roundupsize _ _
    simp only [maxSmallSize] at hb
    have hheap : (BitVec.ofNat 64 heap).toNat = heap := by decide
    rw [hheap]
    refine ⟨⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, by simp only [heap]; omega⟩,
      by simp only [heap]; omega, ?_, fun _ => by decide, fun _ _ => by decide, fun _ => ?_, hle⟩
    · rw [rtView_accessible] at hacc
      exact Memory.accessible_mono _ hacc (Nat.le_refl _) (by omega)
    · have := ZeroBytes.of_rtView hz ⟨(heap, heap + 0x10000), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩
      exact fun i hi => this i (by omega)

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dat : DataSegment := Extracted.data.head!
def dlen : Nat := janus_eval% dat.bytes.length

def bytes (a : Nat) : Byte :=
  if a = zp then 0x34 else if a = zp + 1 then 0x12
  else if tyA ≤ a ∧ a < tyA + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - tyA) 0) else 0

def arg : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then arg else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 4176, 4200, true⟩, ⟨g0, 0x100, false⟩, ⟨tyA, dlen, false⟩,
      ⟨heap, 0x10000, true⟩, ⟨zp, 0x100, false⟩]⟩ }

theorem hret : RetAddr linked ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (linked.withExit ret) Extracted.entry [arg] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem dataLoaded : Extracted.program.DataLoaded s0.mem := by
  unfold Program.DataLoaded
  decide

set_option maxRecDepth 100000 in
theorem hH : H [intType] (s0.regs 28).toNat (s0.sp.toNat - 80) (rtView rt s0.mem) := by
  have hpt : intType = tyA := by unfold tyA; decide
  rw [hpt]
  refine ⟨tyA, rfl, ⟨(tyA, tyA + 16), by simp [rt], Nat.le_refl _, Nat.le_refl _⟩, by decide,
    by decide, ?_⟩
  intro i hi
  have h1 : ¬(tyA ≤ heap + i ∧ heap + i < tyA + dlen) := by
    simp only [tyA, heap, dlen]; omega
  have h2 : heap + i ≠ zp ∧ heap + i ≠ zp + 1 := by simp only [heap, zp]; omega
  show (if _ then bytes (heap + i) else 0) = 0
  split
  · simp only [bytes]; rw [if_neg h2.1, if_neg h2.2, if_neg h1]
  · rfl

set_option maxRecDepth 100000 in
theorem pre : GuardOK s0 0 ∧ StackOK s0 4176 24 ∧ Extracted.program.DataLoaded s0.mem ∧
    Outside (s0.sp.toNat - 4176) 4200 rt ∧ Ptr32 s0.mem arg false ∧ Outside arg.toNat 32 rt ∧
    Disjoint arg.toNat 32 (s0.sp.toNat - 4176) 4200 ∧
    H [intType] (s0.regs 28).toNat (s0.sp.toNat - 80) (rtView rt s0.mem) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, dataLoaded,
    by simp only [rt, outside_cons, outside_nil]; decide, ⟨by decide, by decide⟩,
    by simp only [rt, outside_cons, outside_nil]; decide, by unfold Disjoint; decide, hH⟩

-- CALLSITE-BLOCK lean/Fv256/Arm64/CallSites/Bytes.lean
def wsNew0 : State := { s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): at the allocator's entry, `X0 = Int`'s type descriptor, `SP` = the frame
of the caller (the argument of `H` in `hH`), `X28`/memory as in `s0`. -/
def wsNew : State := { wsNew0 with sp := BitVec.ofNat 64 (sp0 - 80), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite H rt 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = intType := by
    have hpt : intType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - 80 := by decide
  show H [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView rt wsNew.mem)
  rw [e0, e1, e2]
  exact hH

/-- The preconditions and the allocator contract are jointly satisfiable: a concrete call state (with the toy allocator linked at
the `runtime.newobject` address) meets every hypothesis of `correctness`. -/
theorem nonvacuous : ∃ (impl : List Segment) (rt : List (Nat × Nat)) (H : RtReady) (ret : Nat) (s : State) (z : BitVec 64),
    NewobjectContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧
    RetAddr (Extracted.program.link impl) ret ∧
    CallSetup ((Extracted.program.link impl).withExit ret) Extracted.entry [z] s ∧
    (GuardOK s 0 ∧ StackOK s 4176 24 ∧ Extracted.program.DataLoaded s.mem ∧
    Outside (s.sp.toNat - 4176) 4200 rt ∧ Ptr32 s.mem z false ∧ Outside z.toNat 32 rt ∧
    Disjoint z.toNat 32 (s.sp.toNat - 4176) 4200 ∧
    H [intType] (s.regs 28).toNat (s.sp.toNat - 80) (rtView rt s.mem)) ∧
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧ NewobjectSite H rt 4096 s_c) ∧
    Returns ((Extracted.program.link impl).withExit ret) s fun s' => ABIReturn s s' ∧ ∃ ptr : Nat, InRanges ptr 32 rt ∧ ptr % 16 = 0 ∧ s'.mem.accessible ptr 32 true = true ∧
        (s'.regs 0).toNat = ptr + (if Spec.byteLen (val256 s.mem z.toNat) = 0 then 0 else 32 - Spec.byteLen (val256 s.mem z.toNat)) ∧
        (s'.regs 1).toNat = Spec.byteLen (val256 s.mem z.toNat) ∧ (s'.regs 2).toNat = Spec.byteLen (val256 s.mem z.toNat) ∧
        Spec.fromBE (fun i => s'.mem.readLE (ptr + (if Spec.byteLen (val256 s.mem z.toNat) = 0 then 0 else 32 - Spec.byteLen (val256 s.mem z.toNat)) + i) 1) (Spec.byteLen (val256 s.mem z.toNat)) = val256 s.mem z.toNat ∧
        MemFrame s.mem s'.mem (rt ++ [(s.sp.toNat - 4176, s.sp.toNat + 24)]) :=
  ⟨impl, rt, H, ret, s0, arg, hnew, hret, setup, pre,
    ⟨wsNew, rfl, wsNew_pre⟩,
    correctness_proof impl rt H arg hnew ret hret s0 setup pre⟩



/-- The theorem fires: for the number `0x1234` the call returns a slice of length 2 inside a fresh object. -/
theorem returns : Returns (linked.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧ (s'.regs 1).toNat = 2 ∧ (s'.regs 2).toNat = 2) := by
  refine (correctness_proof impl rt H arg hnew ret hret s0 setup pre).mono ?_
  intro s' ⟨hab, ptr, _, _, _, _, h1, h2, _⟩
  have e : Spec.byteLen (val256 s0.mem arg.toNat) = 2 := by
    unfold val256; decide
  rw [e] at h1 h2
  exact ⟨hab, h1, h2⟩

end Wit

end Fv256.Arm64.Bytes
