import sys,os
mode=sys.argv[1] if len(sys.argv)>1 else 'probe'
B,A,G=88,24,48
ONLY=os.environ.get('ONLY'); ONLY=set(map(int,ONLY.split(','))) if ONLY else None
root='/srv/fv-uint256-wd/lean/Fv256/Amd64/SetBytes.lean'
cases=' ∨ '.join(f'len.toNat = {k}' for k in range(32))+' ∨ 32 ≤ len.toNat'
ow='simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]'
BV0="BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_setWidth, BitVec.toNat_ofNat, Nat.shiftLeft_eq, Util.rd4mod, Util.rd2mod, Util.rd1mod, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod, Util.revBytes_readLE"
Z="Util.bv128_zero_toNat, Nat.sub_self, Nat.pow_zero, Nat.div_one, Nat.zero_mod, Nat.zero_div, Nat.mul_zero, Nat.add_zero"
def closer(k):
    if mode=='probe': return '    trace_state\n    all_goals sorry'
    if k<32:
        n=k
        hv=''.join(f"have := Util.rd1_lt s.mem (ptr.toNat{'' if i==0 else ' + '+str(i)}); " for i in range(n))
        def _a(i): return "ptr.toNat" + ('' if i == 0 else ' + ' + str(i))
        h2=''.join(f"have := Util.rd2_lt s.mem (ptr.toNat{'' if i==0 else ' + '+str(i)}); " for i in range(max(n-1,1)))
        h2+=''.join(f"have h2b{i} : s.mem.readLE ({_a(i)}) 2 = s.mem.readLE ({_a(i)}) 1 + 256 * s.mem.readLE ({_a(i+1)}) 1 := Util.rd2_bytes s.mem ({_a(i)}); " for i in range(max(n-1,1)))
        T=(hv+h2+f"(try simp only [{Z}]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); (try simp only [{BV0}]); (try simp (disch := omega) only [Util.bswap16w, Util.bswap16, Util.bswap16n, Util.bswap16m, Util.bswap16x]); all_goals (simp only [Spec.fromBE, Nat.add_zero, Nat.reducePow, Nat.reduceAdd, Nat.add_assoc, Nat.zero_add]; "
           "(try simp (disch := omega) only [Util.or_hi16, Util.or_hi24, Util.or_hi32, Util.or_hi40, Util.or_hi48, Util.or_hi56, Util.orc_hi16, Util.orc_hi24, Util.orc_hi32, Util.orc_hi40, Util.orc_hi48, Util.orc_hi56, Nat.mod_eq_of_lt]); (try omega))")
    else:
        T=("""rw [show ptr.toNat + len.toNat - 32 = ptr.toNat + (len.toNat - 32) from by omega]
         rw [Util.be32_rev]
         rw [show ptr.toNat + (len.toNat - 32) + 24 = len.toNat + ptr.toNat - 8 from by omega,
           show ptr.toNat + (len.toNat - 32) + 16 = len.toNat + ptr.toNat - 16 from by omega,
           show ptr.toNat + (len.toNat - 32) + 8 = len.toNat + ptr.toNat - 24 from by omega,
           show ptr.toNat + (len.toNat - 32) = len.toNat + ptr.toNat - 32 from by omega]
         have h1 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 32) 8)
         have h2 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 24) 8)
         have h3 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 16) 8)
         have h4 := Util.revBytes_lt 8 (s.mem.readLE (len.toNat + ptr.toNat - 8) 8)
         simp only [Nat.reducePow] at h1 h2 h3 h4
         omega""")
    return f"""    all_goals first
      | (exfalso; omega)
      | (refine ⟨?_, by {ow}⟩
         {T})"""
body=f'  rcases (show {cases} by omega) with '+' | '.join(f'h{k}' for k in range(32))+' | hbig\n'
for k in range(33):
    if ONLY is not None and k not in ONLY:
        body+='  · sorry\n'; continue
    if k<32:
        body+=f'''  · have hl : len = BitVec.ofNat 64 {k} := BitVec.eq_of_toNat_eq (by simp; omega)
    have hu : used len.toNat = {k} := by subst hl; simp [used]
    rw [hu] at hd1 hd3 ⊢
    subst hl
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.add_sub_cancel] at hd1 hd2 hd3 hp
    janus64_run [Util.readLE_32]
{closer(k)}
'''
    else:
        body+=f'''  · have hu : used len.toNat = 32 := by simp [used]; omega
    rw [hu] at hd1 hd3 ⊢
    janus64_run [Util.readLE_32]
{closer(k)}
'''
PRE=f"""StackGuardOK s {G} ∧ StackWritable s {B} {A} ∧ Extracted.program.DataLoaded s.mem ∧ len.toNat ≤ cap.toNat ∧
        cap.toNat < 2 ^ 48 ∧ Buffer s z 32 true ∧ Buffer s ptr len.toNat false ∧
        (z.toNat + 32 ≤ ptr.toNat + len.toNat - used len.toNat ∨ ptr.toNat + len.toNat ≤ z.toNat) ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - {B} ∨ (s.regs regSP).toNat + {A} ≤ z.toNat) ∧
        (ptr.toNat + len.toNat ≤ (s.regs regSP).toNat - {B} ∨ (s.regs regSP).toNat + {A} ≤ ptr.toNat + len.toNat - used len.toNat) ∧
        ((s.regs 14).toNat + 16 + 8 ≤ (s.regs regSP).toNat - {B} ∨ (s.regs regSP).toNat + {A} ≤ (s.regs 14).toNat + 16)"""
PRE0=PRE.replace('s.regs','s0.regs').replace('StackGuardOK s ','StackGuardOK s0 ').replace('StackWritable s ','StackWritable s0 ').replace('DataLoaded s.mem','DataLoaded s0.mem').replace('Buffer s ','Buffer s0 ').replace('len.toNat','(10 : BitVec 64).toNat').replace('cap.toNat','(10 : BitVec 64).toNat').replace('used len','used').replace('used (10','used (10')
PRE0=PRE0.replace('ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat','ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat')
t=f'''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).SetBytes(buf []byte) *Int` (amd64)

**Documented behaviour.** "SetBytes interprets buf as the bytes of a big-endian unsigned integer, sets z to that value, and
returns z. If buf is larger than 32 bytes, the last 32 bytes is used."

**Guarantee.** For every receiver `z` (`RAX`) and slice `buf = (ptr, len, cap)` (`RBX`, `RCX`, `RDI`) with `len ≤ cap < 2^48`, every
Go call whose stack-growth check falls through and whose stack window `[RSP-{B}, RSP+{A})` is writable, with the 32 bytes at `z`
writable, the `len` bytes at `ptr` readable, `z` and the used bytes (`min len 32`, ending at `ptr + len`) disjoint from each other and
from the stack window, and the goroutine's stack-guard word outside the window: the call returns (no fault, no panic), returns `z`
in `RAX`, the number at `z` afterwards is `Fv256.Spec.fromBE` of the last `min len 32` bytes of `buf`, and no byte outside `z[0..32)`
and the stack window changes.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.SetBytes

/-- number of bytes used: all of them up to 32, else the last 32 -/
def used (len : Nat) : Nat := if len < 32 then len else 32

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 100000 in
theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => {PRE})
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 =
          Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + len.toNat - used len.toNat + i) 1) (used len.toNat) ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - {B}) {B+A}) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, hd, hlc, hc48, ⟨hzw, hz⟩, ⟨hpw, hp⟩, hd1, hd2, hd3, hdg⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hd2 hd3 hdg
  janus64_data hd [hacc]
  simp only [valueAt]
{body}
namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x300000
def zp : Nat := 0x30800
def dsegs : List DataSegment := Extracted.data

/-- the jump table is in memory (read-only data), everything else is zero -/
def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20 else
  match dsegs.find? (fun d => decide (d.base ≤ a ∧ a < d.base + d.bytes.length)) with
  | some d => BitVec.ofNat 8 (d.bytes.getD (a - d.base) 0)
  | none => 0

def dregs : List Region := dsegs.map (fun d => ⟨d.base, d.bytes.length, false⟩)

def z : BitVec 64 := BitVec.ofNat 64 zp
def ptr : BitVec 64 := BitVec.ofNat 64 (zp + 32)

def s0 : State :=
  {{ regs := fun i => if i = 0 then z else if i = 3 then ptr else if i = 1 then 10 else if i = 7 then 10
      else if i = 4 then BitVec.ofNat 64 sp0 else if i = 14 then BitVec.ofNat 64 g0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩, xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - {B}, {B+A}, true⟩, ⟨g0, 0x100, false⟩, ⟨zp, 0x200, true⟩] ++ dregs⟩ }}

set_option maxRecDepth 100000 in
theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, 10, 10] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : {PRE0} := by
  refine ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ⟨by decide, by decide, by decide⟩,
    by unfold Janus.Amd64.Program.DataLoaded; decide, by decide, by decide, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ?_, ?_, ?_, ?_⟩ <;> first | (unfold used; decide) | decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    ({PRE}) :=
  ⟨ret, s0, z, ptr, 10, 10, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧
      valueAt s' z 32 =
        Spec.fromBE (fun i => s0.mem.readLE (ptr.toNat + (10 : BitVec 64).toNat - used (10 : BitVec 64).toNat + i) 1)
          (used (10 : BitVec 64).toNat) ∧
      Util.OnlyWrites2 s0.mem s'.mem z.toNat 32 ((s0.regs regSP).toNat - {B}) {B+A} :=
  correctness z ptr 10 10 ret hret s0 setup hpre

end Witness

end Fv256.Amd64.SetBytes
'''
open(root,'w').write(t)
