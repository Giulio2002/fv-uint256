#!/usr/bin/env python3
"""add the slicebytetostring call-site conjunct to the arm64 witnesses whose H is `H0` (all argument words 0): Dec, String."""
import subprocess, sys
BLOCK = '''def csSb0 : State := { s0 with regs := fun i => if i = 28 then BitVec.ofNat 64 g0 else if i = 30 then BitVec.ofNat 64 ret else 0 }
/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): at its entry, the empty string (`buf = nil, ptr = 0, n = 0`: every argument word is `0`, as `H0` asks). -/
def csSb : State := { csSb0 with sp := BitVec.ofNat 64 (sp0 - 32), pc := BitVec.ofNat 64 ssAddr }

set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre rtW 4096 H0 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), by decide, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show Ready H0 rtW (argWords csSb 3) csSb
    intro j
    (simp [argWords, wordsFrom, arg, csSb, csSb0]) <;> (rcases j with _ | _ | _ | j <;> simp)
'''
for fn in sys.argv[1:]:
    f = f'lean/Fv256/Arm64/{fn}.lean'
    subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
    s = open(f).read()
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    ns = f'namespace Fv256.Arm64.{fn}\n'
    s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
    open(f, 'w').write(s)
    bf = f'lean/Fv256/Arm64/CallSites/{fn}.lean'
    open(bf, 'w').write(BLOCK)
    r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf,
        '--conj', '∃ s_c : State, s_c.pc = BitVec.ofNat 64 ssAddr ∧ RtPre rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c',
        '--proof', '⟨csSb, rfl, csSb_pre⟩'], capture_output=True, text=True)
    print(fn, r.stdout.strip(), r.stderr.strip()[-200:])
