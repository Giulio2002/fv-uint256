import sys
mode=sys.argv[1] if len(sys.argv)>1 else 'probe'
B,A=88,72   # stack window below/above sp (to be refined)
root='/srv/fv-uint256-wd/lean/Fv256/Arm64/SetBytes.lean'
cases=' ∨ '.join(f'len.toNat = {k}' for k in range(32))+' ∨ 32 ≤ len.toNat'
def closer(k):
    if mode=='probe': return '    all_goals (trace_state; sorry)'
    ow='by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]'
    if k<32:
        hv=''.join(f"have := Util.rd1_lt s.mem (ptr.toNat{'' if i==0 else ' + '+str(i)}); " for i in range(k))
        T=("(try simp only [Util.chunk8, Util.chunk4, Util.chunk2, Util.chunk2n, Util.rot0]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; "
           "(try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Nat.mod_eq_of_lt]); (try omega))")
        return f"""    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, {ow}⟩
         {hv}{T})"""
    return f"""    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, {ow}⟩
         rw [show ptr.toNat + len.toNat - 32 = ptr.toNat + (len.toNat - 32) from by omega]
         rw [Util.be32_rev]
         rw [Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _), Util.rc_rev8 _ (Util.readLE8_lt _ _)]
         omega)"""
body=''
names='|'.join(['h']*33)
body+=f'  rcases (show {cases} by omega) with '+' | '.join(f'h{k}' for k in range(32))+' | hbig\n'
import os
ONLY=os.environ.get('ONLY')
ONLY=set(map(int,ONLY.split(','))) if ONLY else None
for k in range(32):
    if ONLY is not None and k not in ONLY:
        body+='  · sorry\n'; continue
    body+=f'''  · have hl : len = BitVec.ofNat 64 {k} := BitVec.eq_of_toNat_eq (by simp; omega)
    subst hl
    simp only [Disjoint, used, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceLT, ite_true, Nat.add_sub_cancel] at hd1 hd2 hd3 hp ⊢
    janus_run
{closer(k)}
'''
if ONLY is not None and 32 not in ONLY:
    body+='  · sorry\n'
else:
  body+=f'''  · simp only [Disjoint, used, if_neg (show ¬ len.toNat < 32 by omega)] at hd1 hd2 hd3 ⊢
    janus_run
{closer(32)}
'''
t=f'''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SetBytes(buf []byte) *Int` (arm64)

**Documented behaviour.** "SetBytes interprets buf as the bytes of a big-endian unsigned integer, sets z to that value, and
returns z. If buf is larger than 32 bytes, the last 32 bytes is used."

**Guarantee.** For every receiver `z` (`X0`) and slice `buf = (ptr, len, cap)` (`X1`-`X3`) with `len ≤ cap < 2^48`, every Go call
whose stack-growth check falls through and whose stack window is writable and aligned, with the 32 bytes at `z` writable, the `len`
bytes at `ptr` readable, and `z` and the used bytes (`min len 32` of them, ending at `ptr + len`) disjoint from each other and from the
stack window: the call returns (no fault, no panic), returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.fromBE` of the
last `min len 32` bytes of `buf`, and no byte outside `z[0..32)` and the stack window changes.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.SetBytes

/-- number of bytes used: all of them up to 32, else the last 32 -/
def used (len : Nat) : Nat := if len < 32 then len else 32

set_option maxHeartbeats 64000000 in
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => GuardOK s 48 ∧ StackOK s {B} {A} ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
        Disjoint z.toNat 32 (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) ∧
        Disjoint z.toNat 32 (s.sp.toNat - {B}) {B+A} ∧
        Disjoint (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) (s.sp.toNat - {B}) {B+A} ∧
        Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - {B}) {B+A})
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - {B}) {B+A}) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, hd, hlc, hc48, ⟨hz, hz'⟩, ⟨hp, hp'⟩, hd1, hd2, hd3, hdg⟩
  janus_intro hs
  janus_data hd [hw]
  simp only [Disjoint] at hdg
{body}
namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def dat : DataSegment := Extracted.data.head!
def dbase : Nat := janus_eval% dat.base
def dlen : Nat := janus_eval% dat.bytes.length

/-- the jump table is in memory (read-only data), everything else is zero -/
def bytes (a : Nat) : Byte :=
  if dbase ≤ a ∧ a < dbase + dlen then BitVec.ofNat 8 (dat.bytes.getD (a - dbase) 0) else 0

def z : BitVec 64 := BitVec.ofNat 64 zp
def ptr : BitVec 64 := BitVec.ofNat 64 (zp + 32)

def s0 : State :=
  {{ regs := fun i => if i = 0 then z else if i = 1 then ptr else if i = 2 then 10 else if i = 3 then 10
      else if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - {B}, {B+A}, true⟩, ⟨g0, 0x100, false⟩, ⟨dbase, dlen, false⟩, ⟨zp, 0x200, true⟩]⟩ }}

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, 10, 10] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 48 ∧ StackOK s0 {B} {A} ∧ Extracted.program.DataLoaded s0.mem ∧
    (10 : BitVec 64).toNat ≤ (10 : BitVec 64).toNat ∧ (10 : BitVec 64).toNat < 2 ^ 48 ∧ Ptr32 s0.mem z true ∧
    Ptr s0.mem ptr (10 : BitVec 64).toNat false ∧
    Disjoint z.toNat 32 (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat) (used (10 : BitVec 64).toNat) ∧
    Disjoint z.toNat 32 (s0.sp.toNat - {B}) {B+A} ∧
    Disjoint (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat) (used (10 : BitVec 64).toNat) (s0.sp.toNat - {B}) {B+A} ∧
    Disjoint ((s0.regs 28).toNat + 16) 8 (s0.sp.toNat - {B}) {B+A} := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, by unfold Program.DataLoaded; decide, by decide, by decide,
    ⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ?_, ?_, ?_, ?_⟩ <;> first | (unfold Disjoint used; decide) | (unfold Disjoint; decide) | (unfold used; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    (GuardOK s 48 ∧ StackOK s {B} {A} ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
      cap.toNat < 2 ^ 48 ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr len.toNat false ∧
      Disjoint z.toNat 32 (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) ∧
      Disjoint z.toNat 32 (s.sp.toNat - {B}) {B+A} ∧
      Disjoint (ptr.toNat + len.toNat - used len.toNat) (used len.toNat) (s.sp.toNat - {B}) {B+A} ∧
      Disjoint ((s.regs 28).toNat + 16) 8 (s.sp.toNat - {B}) {B+A}) :=
  ⟨ret, s0, z, ptr, 10, 10, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat =
        Spec.fromBE (fun i => s0.mem.readLE (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat + i) 1)
          (used (10 : BitVec 64).toNat) ∧
      Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 (s0.sp.toNat - {B}) {B+A} :=
  correctness z ptr 10 10 ret hret s0 setup hpre

end Witness

end Fv256.Arm64.SetBytes
'''
open(root,'w').write(t)
