#!/usr/bin/env python3
"""cs-value-amd64.py : Value amd64: RtLive call sites (slicebytetostring [0,zp,16] at sp0-416; convTstring [zp,16] at sp0-32), closed L=[] b=2^20."""
import subprocess, sys
SS = 'slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»'
def blk(nm, assigns, k, addr, spec, live, nargs, ok, pre, reads):
    a = ' else '.join(f'if i = {i} then {v}' for i, v in assigns)
    return f'''def cs{nm}0 : Amd64.State :=
  {{ s0 with regs := fun i => {a} else if i = 4 then BitVec.ofNat 64 (sp0 - {k}) else s0.regs i }}
def cs{nm} : Amd64.State := {{ cs{nm}0 with rip := BitVec.ofNat 64 {addr} }}

theorem cs{nm}_rip : cs{nm}.rip = BitVec.ofNat 64 {addr} := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem cs{nm}_pre : RtLivePre64 4096 RW ({spec}) {live} {addr} [] 0x100000 cs{nm} := by
  have hrt : RW.rt = toyRt [] := rfl
  have hw : argWords64 cs{nm} {nargs} = {ok[0]} := by
    unfold argWords64 cs{nm} cs{nm}0; decide +kernel
  unfold RtLivePre64
  refine ⟨by decide, ?_, ?_, trivial, ⟨by decide, ?_⟩, ?_, ?_, by decide, liveSep_nil _, ?_⟩
  · {pre}
  · {reads}
  · simp only [calleeStack64, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide
  · show RW.ok {addr} (argWords64 cs{nm} {nargs}); rw [hw]; {ok[1]}
  · exact s0_inv 0x100000 (cs{nm}.regs 14).toNat (by simp [HSIZE])
  · intro r hr
    simp only [liveWin64, calleeStack64, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with (rfl | rfl) | rfl <;> (simp only [hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; decide)
'''
SSPRE = 'simp only [slicebytetostringSpec, hw, Contracts.arg, BufOK, StrIn]; exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩'
SSRD = 'simp only [slicebytetostringSpec, hw, ReadsOutside]; intro r hr; simp only [List.mem_singleton] at hr; subst hr; simp only [Contracts.arg, hrt, toyRt, HEAP, HEND, HSIZE, BUMP, WBUF, calleeStack64, outside_append, outside_cons, outside_nil, List.map_nil, List.append_nil]; refine ⟨?_, ?_, trivial⟩ <;> decide'
B = blk('Sb', [(0, '0'), (3, 'arg'), (1, '16')], 416, 'ssAddr', SS, 'slicebytetostringLive', 3,
        ('[0, zp, 16]', 'exact Or.inl ⟨rfl, zp, by decide⟩'), SSPRE, SSRD)
B += '\n' + blk('Cv', [(0, 'arg'), (3, '16')], 32, 'cvAddr', 'convTstringSpec', 'convTstringLive', 2,
        ('[zp, 16]', 'exact Or.inr ⟨rfl, zp, by decide⟩'), 'trivial', 'intro r hr; simp [convTstringSpec] at hr')
fn = 'Value'
f = f'lean/Fv256/Amd64/{fn}.lean'
s = open(f).read()
if 'import Fv256.Amd64.CallSites.Live' not in s:
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
open(f, 'w').write(s)
bf = '/tmp/cs-Value.lean'
open(bf, 'w').write(B)
def conj(addr, pre): return f'∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 {addr} ∧ {pre} s_c'
r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, 'nonvacuous', '--block', bf, '--block-name', 'Value',
  '--conj', conj('ssAddr', f'RtLivePre64 4096 R ({SS}) slicebytetostringLive ssAddr [] 0x100000'), '--proof', '⟨csSb, csSb_rip, csSb_pre⟩',
  '--conj', conj('cvAddr', 'RtLivePre64 4096 R convTstringSpec convTstringLive cvAddr [] 0x100000'), '--proof', '⟨csCv, csCv_rip, csCv_pre⟩'],
  capture_output=True, text=True)
print(r.stdout.strip(), r.stderr.strip()[-300:])
