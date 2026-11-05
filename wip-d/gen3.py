root='/srv/fv-uint256-wd/lean/Fv256/'
def arm(op,iop,spec):
    t=open(root+f'Arm64/{op}.lean').read().split('\n')
    i0=next(k for k,l in enumerate(t) if l.startswith('  rcases hzx with rfl | hzx'))
    i1=next(k for k,l in enumerate(t) if k>i0+1 and l.startswith('  · simp only [Disjoint] at *'))
    body=t[i0+1:i1]
    while body and body[-1].strip()=='' : body.pop()
    body=[l[2:] if l.startswith('  ') else l for l in body]
    body='\n'.join(body).replace('· simp only [Disjoint] at *','  simp only [Disjoint] at *',1)
    k=body.index('\n',body.index('janus_run'))
    body=body[:k]+'\n  all_goals refine And.intro ?_ (by simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff])'+body[k:]
    sym={'Lsh':'<<','Rsh':'>>'}[op]
    out=f'''import Extracted
import Fv256.Spec
import Fv256.Util

/-!
# `(*uint256.Int).I{op}(n uint) *Int` (arm64): in place, `z = z {sym} n`

**Guarantee.** For every pointer `z` (receiver, `X0`), every shift count `n` (`X1`, any 64-bit value; counts of 256 or more give
zero) and every Go call state such that the stack-growth check falls through (`GuardOK s 0`), the window `[SP-56, SP)` (the 56-byte
frame) is writable and aligned (`StackOK s 56 0`), the 32 bytes at `z` are writable and do not overlap the frame window: the call
returns (no fault, no panic), obeys the ABI, returns `z` in `X0`, the number at `z` afterwards is `Fv256.Spec.{spec}` of the number at
`z` before the call, shifted by `n`, and no byte outside `z[0..32)` and the frame window changes (`Fv256.Util.OnlyWrites2`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns `z`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.I{op}

theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 56)
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.{spec} (val256 s.mem z.toNat) n.toNat ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - 56) 56) := by
  intro ret hret s hs ⟨⟨hg1, hg2, hg3⟩, ⟨hal, hb, ha, hw⟩, ⟨hz, hz'⟩, hd1⟩
  janus_intro hs
{body}

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

def s0 : State :=
  {{ regs := fun i => if i = 0 then z else if i = 1 then n
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }}

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 56 0 ∧ Ptr32 s0.mem z true ∧ Disjoint z.toNat 32 (s0.sp.toNat - 56) 56 :=
  ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    (GuardOK s 0 ∧ StackOK s 56 0 ∧ Ptr32 s.mem z true ∧ Disjoint z.toNat 32 (s.sp.toNat - 56) 56) :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ s'.regs 0 = z ∧ val256 s'.mem z.toNat = 0 := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, h.2.1, ?_⟩
  rw [h.2.2.1]
  decide

end Witness

end Fv256.Arm64.I{op}
'''
    open(root+f'Arm64/I{op}.lean','w').write(out)
arm('Lsh','ILsh','lsh'); arm('Rsh','IRsh','rsh')
