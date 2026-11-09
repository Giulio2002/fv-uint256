#!/usr/bin/env python3
"""cs-marsh-amd64.py FN... : MarshalJSON / MarshalText amd64 call sites (slicebytetostring + concatbyte3 | stringtoslicebyte), nonvacuous and big."""
import subprocess, sys, re
SS = 'slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»'
R = 'if i = 0 then 0 else '
def st(name, base, rip, rsp, assigns):
    a = ' else '.join(f'if i = {i} then {v}' for i, v in assigns)
    return (f'def {name} : Amd64.State :=\n  {{ {base} with rip := BitVec.ofNat 64 {rip}, regs := fun i => if i = 0 then 0 else {a} else '
            f'if i = 4 then BitVec.ofNat 64 (sp0 - {rsp}) else {base}.regs i }}\n')
def rt3(sfx, name, spec, specname, base, H, rt, acc, N, rsp, addr):
    zp = 'BitVec.ofNat 64 zp'
    return st(f'{name}{sfx}', base, addr, rsp, [(3, zp), (1, f'BitVec.ofNat 64 {N}')]) + f'''
open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem {name}{sfx}_pre : RtPre64 {rt} 4096 {H} ({spec}) {name}{sfx} := by
  have hargs : argWords64 {name}{sfx} 3 = [0, zp, {N}] := by
    unfold argWords64 {name}{sfx}; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [{specname}, hargs, Contracts.arg, BufOK, StrIn]
    refine ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [{specname}, hargs, ReadsOutside]
    intro r hr; simp only [List.mem_singleton] at hr; subst hr
    simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> decide
  · split
    · show {H} (argWords64 {name}{sfx} 3) ({name}{sfx}.regs 14).toNat ({name}{sfx}.regs 4).toNat (rtView {rt} {name}{sfx}.mem)
      rw [hargs]
      refine ⟨SBW, by rw [{acc}]; decide, by rw [{acc}]; decide, by decide, by decide⟩
    · trivial

'''
def cb(sfx, base, H, rt, acc, N, rsp, sbw):
    zp = 'BitVec.ofNat 64 zp'
    return st(f'csCb{sfx}', base, 'cbAddr', rsp, [(3, '5181392'), (1, '1'), (7, zp), (6, f'BitVec.ofNat 64 {N}'), (8, '5181392'), (9, '1')]) + f'''
open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csCb{sfx}_pre : RtPre64 {rt} 4096 {H} (concatbyteSpec 3) csCb{sfx} := by
  have hargs : argWords64 csCb{sfx} 7 = [0, 5181392, 1, zp, {N}, 5181392, 1] := by
    unfold argWords64 csCb{sfx}; decide +kernel
  refine ⟨by decide, ?_, ?_, trivial, ?_⟩
  · simp only [concatbyteSpec, hargs]
    refine ⟨Or.inl (by decide), strsIn_of (fun x hx => ?_) (by decide)⟩
    simp only [strPairs, hargs, Contracts.arg, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨by decide, fun _ => by decide⟩
  · intro r hr
    simp only [concatbyteSpec, strPairs, hargs, Contracts.arg, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (simp only [Contracts.arg, calleeStack64, outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> decide)
  · split
    · show {H} (argWords64 csCb{sfx} 7) (csCb{sfx}.regs 14).toNat (csCb{sfx}.regs 4).toNat (rtView {rt} csCb{sfx}.mem)
      rw [hargs]
      refine ⟨Or.inr ⟨zp, rfl⟩, by rw [{acc}]; decide, by rw [{acc}]; decide, by decide, by decide⟩
    · trivial

'''
CFG = {
 'MarshalJSON': [('nonvacuous', '', 's0', 'Hw', 'rtT', 'rtView_acc', 2, 464, 'cb', 80),
                 ('big', '8', 's08', 'Hw8', 'rtT16', 'rtView_acc16', 8, 464, 'cb', 80)],
 'MarshalText': [('nonvacuous', '', 's0', 'Hw', 'rtT', 'rtView_acc', 2, 432, 'stb', 48),
                 ('big', '8', 's08', 'Hw8', 'rtT', 'rtView_acc', 8, 432, 'stb', 48)],
}
def conj(addr, pre): return f'∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 {addr} ∧ {pre} s_c'
for fn in sys.argv[1:]:
    f = f'lean/Fv256/Proofs/Amd64/{fn}.lean'
    s = open(f).read()
    if 'import Fv256.Proofs.Amd64.CallSites.Live' not in s:
        s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Amd64.CallSites.Live\n', 1)
    open(f, 'w').write(s)
    for (thm, sfx, base, H, rt, acc, N, kss, sec, k2) in CFG[fn]:
        bf = f'/tmp/cs-{fn}-{thm}.lean'
        sbw = 'Or.inl ⟨zp, rfl⟩' if sec == 'cb' else '⟨zp, rfl⟩'
        b = rt3(sfx, 'csSb', SS, 'slicebytetostringSpec', base, H, rt, acc, N, kss, 'ssAddr').replace('SBW', sbw)
        if sec == 'stb':
            b += rt3(sfx, 'csSt', 'stringtoslicebyteSpec', 'stringtoslicebyteSpec', base, H, rt, acc, N, k2, 'stAddr').replace('SBW', '⟨zp, rfl⟩')
            c2, spec2, p2 = 'stAddr', 'stringtoslicebyteSpec', f'csSt{sfx}'
        else:
            b += cb(sfx, base, H, rt, acc, N, k2, sbw)
            c2, spec2, p2 = 'cbAddr', '(concatbyteSpec 3)', f'csCb{sfx}'
        open(bf, 'w').write(b)
        r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, thm, '--block', bf, '--block-name', f'{fn}.{thm}',
            '--conj', conj('ssAddr', f'RtPre64 rt 4096 H ({SS})'), '--proof', f'⟨csSb{sfx}, rfl, csSb{sfx}_pre⟩',
            '--conj', conj(c2, f'RtPre64 rt 4096 H {spec2}'), '--proof', f'⟨{p2}, rfl, {p2}_pre⟩'], capture_output=True, text=True)
        print(fn, thm, r.stdout.strip(), r.stderr.strip()[-300:])
