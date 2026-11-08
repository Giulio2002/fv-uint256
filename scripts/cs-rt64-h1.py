#!/usr/bin/env python3
"""cs-rt64-h1.py FN : U-WITNESS-CALLSITE for the slicebytetostring RtContract64 (H1: args [0, HEAP, N]) of Hex (K=112,N=3) / PrettyDec (K=400,N=5), amd64."""
import sys
CFG = {'Hex': (112, 3), 'PrettyDec': (400, 5)}
fn = sys.argv[1]; K, N = CFG[fn]
f = f'lean/Fv256/Amd64/{fn}.lean'; s = open(f).read()
if 'csSb_pre' in s: print('skip'); sys.exit()
s = s.replace('\nimport ', '\nimport Fv256.Amd64.CallSites.Live\nimport ', 1)
blk = f'''/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `slicebytetostring(nil, HEAP, {N})` at its entry, in the
caller's frame (`RSP = sp0 - {K}`). -/
def csSb : Amd64.State :=
  {{ s0 with rip := BitVec.ofNat 64 ssAddr, regs := fun i => if i = 0 then 0 else if i = 3 then BitVec.ofNat 64 HEAP else if i = 1 then BitVec.ofNat 64 {N} else if i = 4 then BitVec.ofNat 64 (sp0 - {K}) else s0.regs i }}

theorem csSb_rip : csSb.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSb_pre : RtPre64 rtW 4096 H1 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSb := by
  have hargs : argWords64 csSb 3 = [0, HEAP, {N}] := by
    unfold argWords64 csSb; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show H1 (argWords64 csSb 3) (csSb.regs 14).toNat (csSb.regs 4).toNat (rtView rtW csSb.mem)
      rw [hargs]
      refine ⟨by decide, by decide, ?_, by decide⟩
      decide
    · trivial

'''
i = s.index('theorem nonvacuous')
j = s.rfind('/--', 0, i)
if j == -1 or '-/' not in s[j:i] or '\n\n' in s[s.index('-/', j):i].strip('\n'): j = i
s = s[:j] + blk + s[j:]
a = s.index('theorem nonvacuous'); a2 = s.index('    RetAddr (Extracted.program.link impl) ret ∧', a)
s = s[:a2] + '    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧\n      RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧\n' + s[a2:]
assert 'model, ?w1, ?w2, pre,' in s
s = s.replace('model, ?w1, ?w2, pre,', 'model, ⟨csSb, csSb_rip, csSb_pre⟩, ?w1, ?w2, pre,', 1)
open(f, 'w').write(s); print('ok', f)
