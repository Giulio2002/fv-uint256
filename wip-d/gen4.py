root='/srv/fv-uint256-wd/lean/Fv256/'
def amd(op,iop,spec):
    t=open(root+f'Amd64/{op}.lean').read().split('\n')
    i0=next(k for k,l in enumerate(t) if l.startswith('  rcases hzx with rfl | hzx'))
    i1=next(k for k,l in enumerate(t) if k>i0+1 and l.startswith('  · try simp only [Disjoint, Alias] at *'))
    body=t[i0+1:i1]
    while body and body[-1].strip()=='' : body.pop()
    body=[l[2:] if l.startswith('  ') else l for l in body]
    body='\n'.join(body).replace('· try simp only [Disjoint, Alias] at *','try simp only [Disjoint, Alias] at *',1)
    body=body.replace('Janus.Spec.onlyWrites_writeLE_iff, Janus.Spec.onlyWrites_self','Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff')
    sym={'Lsh':'<<','Rsh':'>>'}[op]
    mh=''
    # keep maxHeartbeats option from base
    out=f'''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).I{op}(n uint) *Int` (amd64): in place, `z = z {sym} n`

**Guarantee.** For every pointer `z` (receiver, `RAX`), every shift count `n` (`RBX`, any 64-bit value; counts of 256 or more
give zero) and every Go call state such that the stack-growth check falls through (`StackGuardOK s 0`), the window
`[SP-40, SP+8)` (the 32-byte frame, the saved frame pointer and the callee's return address, plus the caller's return-address
slot) is writable, the 32 bytes at `z` are writable and do not overlap the frame window: the call returns (no fault, no panic),
obeys the ABI, returns `z` in `RAX`, the number at `z` afterwards is `Fv256.Spec.{spec}` of the number at `z` before the call, shifted
by `n`, and no byte outside `z[0..32)` and the frame window `[SP-40, SP)` changes (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z`.
-/

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.I{op}

set_option maxHeartbeats 16000000 in
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧
        (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat))
      (fun s s' => s'.regs 0 = z ∧
        valueAt s' z 32 = Spec.{spec} (valueAt s z 32) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 ((s.regs regSP).toNat - 40) 40) := by
  intro ret hret s hs ⟨hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩
  janus64_intro hs
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regSP, regG, stackguard0Offset, stackguard0] at hgl hgb hnw2 hgr hacc hlow hnw hds
  simp only [valueAt, Disjoint] at *
{body}

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  {{ regs := fun i => if i = 0 then z else if i = 3 then n else if i = 4 then BitVec.ofNat 64 wsp
      else if i = 14 then BitVec.ofNat 64 wg else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }}

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackGuardOK s0 0 ∧ StackWritable s0 40 8 ∧ Buffer s0 z 32 true ∧
    (z.toNat + 32 ≤ (s0.regs regSP).toNat - 40 ∨ (s0.regs regSP).toNat + 8 ≤ z.toNat) :=
  ⟨⟨by decide, by decide, by unfold stackguard0 stackguard0Offset regG regSP; decide⟩, ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (StackGuardOK s 0 ∧ StackWritable s 40 8 ∧ Buffer s z 32 true ∧
      (z.toNat + 32 ≤ (s.regs regSP).toNat - 40 ∨ (s.regs regSP).toNat + 8 ≤ z.toNat)) :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ valueAt s' z 32 = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  simp only [valueAt, Spec.{spec}]
  decide

end Witness

end Fv256.Amd64.I{op}
'''
    open(root+f'Amd64/I{op}.lean','w').write(out)
amd('Lsh','ILsh','lsh'); amd('Rsh','IRsh','rsh')
