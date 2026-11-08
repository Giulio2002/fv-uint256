#!/usr/bin/env python3
"""MarshalJSON / MarshalText arm64: Rt call sites (slicebytetostring + concatbyte3 | stringtoslicebyte), nonvacuous and big."""
import subprocess, sys, re
SS = 'slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s»'
def one(sfx, s, H, rt, acc, N, kss, second, k2):
    # first call: slicebytetostring [0, zp, N], sp0 - kss
    b = f'''def csSb0{sfx} : State := {{ {s} with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 {N} else {s}.regs i }}
def csSb{sfx} : State := {{ csSb0{sfx} with sp := BitVec.ofNat 64 (sp0 - {kss}), pc := BitVec.ofNat 64 ssAddr }}

set_option maxRecDepth 100000 in
theorem csSb{sfx}_pre : RtPre {rt} 4096 {H} ({SS}) csSb{sfx} := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show {H} (argWords csSb{sfx} 3) (csSb{sfx}.regs 28).toNat csSb{sfx}.sp.toNat (rtView {rt} csSb{sfx}.mem)
    refine ⟨{{SBW}}, by rw [{acc}]; decide, by rw [{acc}]; decide⟩

'''
    sbw = 'Or.inl ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩' if second == 'cb' else '⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩'
    b = b.replace('{SBW}', sbw)
    if second == 'stb':
        b2 = f'''def csSt0{sfx} : State := {{ {s} with regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 zp else if i = 2 then BitVec.ofNat 64 {N} else {s}.regs i }}
def csSt{sfx} : State := {{ csSt0{sfx} with sp := BitVec.ofNat 64 (sp0 - {k2}), pc := BitVec.ofNat 64 stAddr }}

set_option maxRecDepth 100000 in
theorem csSt{sfx}_pre : RtPre {rt} 4096 {H} stringtoslicebyteSpec csSt{sfx} := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), ⟨by decide, fun _ => by decide⟩, fun h => absurd (by decide) h⟩
  · simp only [stringtoslicebyteSpec, argWords, wordsFrom, arg, ReadsOutside]
    intro r hr; simp at hr; subst hr; simp only [Outside, calleeStack]; decide
  · show {H} (argWords csSt{sfx} 3) (csSt{sfx}.regs 28).toNat csSt{sfx}.sp.toNat (rtView {rt} csSt{sfx}.mem)
    refine ⟨⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [{acc}]; decide, by rw [{acc}]; decide⟩

'''
    else:
        b2 = f'''def csCb0{sfx} : State := {{ {s} with regs := fun i => if i = 0 then 0 else if i = 1 then 1007400 else if i = 2 then 1 else if i = 3 then BitVec.ofNat 64 zp else if i = 4 then BitVec.ofNat 64 {N} else if i = 5 then 1007400 else if i = 6 then 1 else {s}.regs i }}
def csCb{sfx} : State := {{ csCb0{sfx} with sp := BitVec.ofNat 64 (sp0 - {k2}), pc := BitVec.ofNat 64 cbAddr }}

set_option maxRecDepth 100000 in
theorem csCb{sfx}_pre : RtPre {rt} 4096 {H} (concatbyteSpec 3) csCb{sfx} := by
  refine ⟨callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), ?_, ?_, trivial, ?_⟩
  · refine ⟨Or.inl (by decide), strsIn_of (fun x hx => ?_) (by decide)⟩
    simp only [strPairs, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl <;> exact ⟨by decide, fun _ => by decide⟩
  · intro r hr
    simp only [concatbyteSpec, strPairs, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> (simp only [Outside, calleeStack]; decide)
  · show {H} (argWords csCb{sfx} 7) (csCb{sfx}.regs 28).toNat csCb{sfx}.sp.toNat (rtView {rt} csCb{sfx}.mem)
    refine ⟨Or.inr ⟨BitVec.toNat (BitVec.ofNat 64 zp), by decide⟩, by rw [{acc}]; decide, by rw [{acc}]; decide⟩

'''
    return b + b2

CFG = {
 'MarshalJSON': [('nonvacuous', '', 's0', 'Hw', 'rtT', 'rtView_acc', 2, 464, 'cb', 80),
                 ('big', '8', 's08', 'Hw8', 'rtT16', 'rtView_acc16', 8, 464, 'cb', 80)],
 'MarshalText': [('nonvacuous', '', 's0', 'Hw', 'rtT', 'rtView_acc', 2, 432, 'stb', 48),
                 ('big', '8', 's08', 'Hw8', 'rtT', 'rtView_acc', 8, 432, 'stb', 48)],
}
def conj(addr, pre): return f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {addr} ∧ {pre} s_c'
for fn in sys.argv[1:]:
    f = f'lean/Fv256/Arm64/{fn}.lean'
    subprocess.run(['git', 'checkout', 'fv/wrun', '--', f], check=True)
    s = open(f).read()
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    ns = f'namespace Fv256.Arm64.{fn}\n'
    s = s.replace(ns, 'open Fv256.Arm64.CallSites\n\n' + ns, 1)
    s = re.sub(r'(correctness [^\n]*?) ⟨(pre8?), \?w5⟩⟩', r'\1 \2⟩', s)  # fv/wrun bug: `100 ≤ val` is not part of correctness' pre
    open(f, 'w').write(s)
    for (thm, sfx, st, H, rt, acc, N, kss, sec, k2) in CFG[fn]:
        bf = f'lean/Fv256/Arm64/CallSites/{fn}.{thm}.lean'
        open(bf, 'w').write(one(sfx, st, H, rt, acc, N, kss, sec, k2))
        cname = 'csSt' if sec == 'stb' else 'csCb'
        c2 = f'(slicebytetostringSpec' if False else None
        spec2 = 'stringtoslicebyteSpec' if sec == 'stb' else '(concatbyteSpec 3)'
        addr2 = 'stAddr' if sec == 'stb' else 'cbAddr'
        r = subprocess.run(['python3', 'scripts/callsite-splice.py', f, thm, '--block', bf,
            '--conj', conj('ssAddr', f'RtPre rt 4096 H ({SS})'), '--proof', f'⟨csSb{sfx}, rfl, csSb{sfx}_pre⟩',
            '--conj', conj(addr2, f'RtPre rt 4096 H {spec2}'), '--proof', f'⟨{cname}{sfx}, rfl, {cname}{sfx}_pre⟩'],
            capture_output=True, text=True)
        print(fn, thm, r.stdout.strip(), r.stderr.strip()[-200:])
