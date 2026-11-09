#!/usr/bin/env python3
"""slicebytetostring call-site for arm64 witnesses with readiness H1 (args [0, HEAP, N]): Hex (K=112,N=3), PrettyDec (K=400,N=5)."""
import subprocess, sys
CFG = {'Hex': (112, 3), 'PrettyDec': (400, 5)}
BLOCK = '''def csSb0 : State := {{ s0 with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 HEAP else if i = 2 then BitVec.ofNat 64 {N} else s0.regs i }}
/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `slicebytetostring(nil, HEAP, {N})` at its entry, in the caller's frame (`SP = sp0 - {K}`). -/
def csSb : State := {{ csSb0 with sp := BitVec.ofNat 64 (sp0 - {K}), pc := BitVec.ofNat 64 ssAddr }}

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show H1 (argWords csSb 3) (csSb.regs 28).toNat csSb.sp.toNat (rtView rtW csSb.mem)
    refine ⟨by decide, by decide, ?_, by decide⟩
    decide
'''
for fn in sys.argv[1:]:
    K, N = CFG[fn]
    f = f'lean/Fv256/Proofs/Arm64/{fn}.lean'
    subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
    s = open(f).read()
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    ns = f'namespace Fv256.Arm64.{fn}\n'
    s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
    open(f, 'w').write(s)
    bf = f'lean/Fv256/Proofs/Arm64/CallSites/{fn}.lean'
    open(bf, 'w').write(BLOCK.format(K=K, N=N))
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf,
        '--conj', '∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c',
        '--proof', '⟨csSb, rfl, csSb_pre⟩'], capture_output=True, text=True)
    print(fn, r.stdout.strip(), r.stderr.strip()[-200:])
