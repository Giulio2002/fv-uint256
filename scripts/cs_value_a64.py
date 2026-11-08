#!/usr/bin/env python3
"""Value arm64: RtLive call sites (slicebytetostring [0,zp,16] at sp0-416; convTstring [zp,16] at sp0-32), closed L=[] b=2^20."""
import subprocess, sys, re
SS = 'slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»'
def blk(nm, regs, k, addr, spec, live, okshape, nargs):
    return f'''def cs{nm}0 : State := {{ s0 with regs := fun i => {regs} else s0.regs i }}
def cs{nm} : State := {{ cs{nm}0 with sp := BitVec.ofNat 64 (sp0 - {k}), pc := BitVec.ofNat 64 {addr} }}

set_option maxRecDepth 100000 in
theorem cs{nm}_pre : RtLivePre 4096 RW ({spec}) {live} {addr} [] 0x100000 cs{nm} := by
  have hrt : RW.rt = toyRt [] := rfl
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial,
    ⟨guardOK_of (by decide) (by decide) (by decide), ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · {{pre}}
  · {{reads}}
  · simp only [calleeStack, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · {{ok}}
  · exact s0_inv _ _ (by simp [HSIZE])
  · intro r hr
    simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)
'''
SSPRE = 'simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]; exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩'
SSRD = 'simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]; intro r hr; simp at hr; subst hr; simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, Outside, calleeStack]; decide'
B = ''
B += blk('Sb', 'if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then 16', 416, 'ssAddr', SS, 'slicebytetostringLive', '', 3)\
  .replace('{pre}', SSPRE).replace('{reads}', SSRD).replace('{ok}', 'exact Or.inl ⟨rfl, zp, by decide⟩')
B += '\n' + blk('Cv', 'if i = 0 then BitVec.ofNat 64 zp else if i = 1 then 16', 32, 'cvAddr', 'convTstringSpec', 'convTstringLive', '', 2)\
  .replace('{pre}', 'trivial').replace('{reads}', 'intro r hr; simp [convTstringSpec] at hr').replace('{ok}', 'exact Or.inr ⟨rfl, zp, by decide⟩')
fn = 'Value'
f = f'lean/Fv256/Arm64/{fn}.lean'
subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
s = open(f).read()
s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
ns = f'namespace Fv256.Arm64.{fn}\n'
s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
s = re.sub(r'(correctness [^\n]*?) ⟨(pre8?), \?w5⟩⟩', r'\1 \2⟩', s)  # fv/wrun bug: `100 ≤ val` is not part of correctness' pre
open(f, 'w').write(s)
bf = f'lean/Fv256/Arm64/CallSites/{fn}.lean'
open(bf, 'w').write(B)
def conj(addr, pre): return f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {addr} ∧ {pre} s_c'
r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf,
  '--conj', conj('ssAddr', f'RtLivePre 4096 R ({SS}) slicebytetostringLive ssAddr [] 0x100000'), '--proof', '⟨csSb, rfl, csSb_pre⟩',
  '--conj', conj('cvAddr', 'RtLivePre 4096 R convTstringSpec convTstringLive cvAddr [] 0x100000'), '--proof', '⟨csCv, rfl, csCv_pre⟩'],
  capture_output=True, text=True)
print(r.stdout.strip(), r.stderr.strip()[-300:])
