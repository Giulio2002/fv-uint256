#!/usr/bin/env python3
"""cs_newobj_a64.py : add the runtime.newobject call-site conjunct to the uniform arm64 NewobjectContract witnesses."""
import subprocess, sys, re
CFG = {  # file: (K, hH name)
 'Bytes': (80, 'hH'), 'Clone': (48, 'hH'), 'FromBig': (48, 'hH'), 'FromHex': (48, 'hH'),
 'MustFromBig': (48, 'hH'), 'MustFromHex': (48, 'hH'), 'DivMod': (160, 'hHW'), 'NewInt': (48, 'hH'),
}
BLOCK = '''def wsNew0 : State := {{ s0 with regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else s0.regs i }}
/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): at the allocator's entry, `X0 = Int`'s type descriptor, `SP` = the frame
of the caller (the argument of `H` in `{hH}`), `X28`/memory as in `s0`. -/
def wsNew : State := {{ wsNew0 with sp := BitVec.ofNat 64 (sp0 - {K}), pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") }}

set_option maxRecDepth 100000 in
theorem wsNew_pre : NewobjectSite {Hn} {rtn} 4096 wsNew := by
  refine ⟨⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
    typeOK_of (by decide) (by decide), by decide⟩, ?_⟩
  have e0 : (wsNew.regs 0).toNat = intType := by
    have hpt : intType = tyA := by unfold tyA; decide
    rw [hpt]; decide
  have e1 : (wsNew.regs 28).toNat = (s0.regs 28).toNat := by decide
  have e2 : wsNew.sp.toNat = s0.sp.toNat - {K} := by decide
  show {Hn} [(wsNew.regs 0).toNat] (wsNew.regs 28).toNat wsNew.sp.toNat (rtView {rtn} wsNew.mem)
  rw [e0, e1, e2]
  exact {hH}
'''
def apply(fn):
    K, hH = CFG[fn]
    f = f'lean/Fv256/Proofs/Arm64/{fn}.lean'
    subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
    s = open(f).read()
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    ns = f'namespace Fv256.Arm64.{fn}\n'
    assert ns in s
    s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
    open(f, 'w').write(s)
    Hn = 'HW' if fn == 'DivMod' else 'H'; rtn = 'rtW' if fn == 'DivMod' else 'rt'
    blk = BLOCK.format(K=K, hH=hH, Hn=Hn, rtn=rtn)
    bf = f'lean/Fv256/Proofs/Arm64/CallSites/{fn}.lean'
    open(bf, 'w').write(blk)
    A = '(Extracted.program.contractAddr "runtime.newobject")'
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf,
        '--conj', f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {A} ∧ NewobjectSite H rt 4096 s_c', '--proof', '⟨wsNew, rfl, wsNew_pre⟩'],
        capture_output=True, text=True)
    print(fn, r.stdout.strip(), r.stderr.strip()[-200:])
for fn in sys.argv[1:]: apply(fn)
