body=open('/srv/fv-uint256-wd/wip-d/lsh_body_arm.txt').read()
body='\n'.join(l[2:] if l.startswith('  ') else l for l in body.split('\n')).lstrip()
body=body.replace('n.toNat','(s.regs 2).toNat')
first,rest=body.split('\n',1)
rest=rest.lstrip()
L=f'''import Extracted
import Fv256.Spec
import Fv256.Util

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

/-- `Lsh(z, x, n)` as a callee (`z` in `X0`, `x` in `X1`, `n` in `X2`), `z` and `x` disjoint. -/
def LshSummary (p : Program) (entry : Nat) (z x : BitVec 64) : Prop :=
  Summary p entry
    (fun s => (s.regs 30).toNat % 4 = 0 ∧ (s.regs 30).toNat < 2 ^ 56 ∧ s.regs 0 = z ∧ s.regs 1 = x ∧
      Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Disjoint z.toNat 32 x.toNat 32)
    (fun s s' => s'.pc = s.regs 30 ∧ s'.sp = s.sp ∧ s'.regs 28 = s.regs 28 ∧ s'.regs 29 = s.regs 29 ∧
      s'.regs 30 = s.regs 30 ∧ s'.regs 18 = s.regs 18 ∧ s'.regs 0 = z ∧
      val256 s'.mem z.toNat = Spec.lsh (val256 s.mem x.toNat) (s.regs 2).toNat ∧
      MemFrame s.mem s'.mem [(z.toNat, z.toNat + 32)])

set_option maxHeartbeats 16000000 in
theorem lsh_summary (z x : BitVec 64) :
    LshSummary Extracted.program (segAddr Extracted.program "github.com/holiman/uint256.(*Int).Lsh") z x := by
  intro s hpc ⟨h30a, h30b, hz0, hx0, ⟨hz, hz'⟩, ⟨hx, hx'⟩, hd⟩
  simp only [Disjoint] at *
  {first}
  all_goals (refine ⟨?_, ?_⟩; rotate_right; janus_frame)
  {rest}

end Fv256.Arm64.Float64
'''
open('/srv/fv-uint256-wd/lean/Fv256/Arm64/Float64Lsh.lean','w').write(L)
main=open('/srv/fv-uint256-wd/wip-d/f64_arm_main2.txt').read()
M=f'''import Extracted
import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.UtilD
import Fv256.Arm64.Float64Lsh

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.Float64

{main}
end Fv256.Arm64.Float64
'''
open('/srv/fv-uint256-wd/lean/Fv256/Arm64/Float64.lean','w').write(M)
