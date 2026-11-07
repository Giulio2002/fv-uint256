#!/usr/bin/env python3
"""cs_unm_a64.py (FV-CSA2 fork C2): call-site conjuncts (U-WITNESS-CALLSITE) for arm64 UnmarshalJSON / UnmarshalText.
   Edits lean/Fv256/Arm64/{NS}WitC.lean (block + core statements/proofs) and {NS}Main.lean (thin witnesses). Idempotent (checks out fv/wrun? no: from HEAD~ copy)."""
import re, subprocess, sys

def okpos(i, n, x):
    if i == n - 1: return 'Or.inr (' * i + x + ')' * i
    return 'Or.inr (' * i + 'Or.inl (' + x + ')' + ')' * i

A = lambda x: f'(Extracted.program.contractAddr "{x}")'
CALLOK = 'callOK_of (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)'
GUARD = 'guardOK_of (by decide) (by decide) (by decide)'
SEP2 = ('(by intro r hr; rw [rt_eq]; simp only [calleeStack, List.mem_cons, List.not_mem_nil, or_false] at hr; '
        'rcases hr with rfl | rfl <;> (simp only [outside_cons, outside_nil]; decide))')
SEP1 = ('(by intro r hr; rw [rt_eq]; simp only [List.mem_singleton] at hr; subst hr; simp only [outside_cons, outside_nil]; decide)')
CS_OUT = '(by simp only [calleeStack, outside_cons, outside_nil]; decide)'

def block(NS):
    N = 6  # ok disjuncts: new w1 w2 mg mv sb
    sb = f'Fv256.Arm64.{NS}.sbAddr'; st = f'Fv256.Arm64.{NS}.stAddr'
    sbp = 'Or.inr rfl'
    return f'''
/-! ### Call-site states (U-WITNESS-CALLSITE): `s0` with `PC` at each runtime stub's entry and the argument registers of a request
the toy runtime `R` serves (`ok`); the live set is `[]` and the budget `bW` (`inv0`). -/

def csNew : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject"),
    regs := fun i => if i = 0 then BitVec.ofNat 64 numErrT else s0.regs i }}
def csW1 : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier1") }}
def csW2 : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.gcWriteBarrier2") }}
def csMg : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.mallocgc"),
    regs := fun i => if i = 0 then 1 else if i = 1 then 0 else if i = 2 then 0 else s0.regs i }}
def csMv : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.memmove"),
    regs := fun i => if i = 0 then BitVec.ofNat 64 loW else if i = 1 then BitVec.ofNat 64 0x301000 else if i = 2 then 1 else s0.regs i }}
def csCm : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.cmpstring"),
    regs := fun i => if i = 0 then 0 else if i = 1 then 0 else if i = 2 then 0 else if i = 3 then 0 else s0.regs i }}
def csIf : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.ifaceeq"),
    regs := fun i => if i = 0 then 0 else s0.regs i }}
def csSb : State := {{ s0 with pc := BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring"),
    regs := fun i => if i = 0 then 0 else if i = 1 then BitVec.ofNat 64 0x302000 else if i = 2 then 48 else s0.regs i }}

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectLiveSite R {A('runtime.newobject')} 4096 [] bW csNew := by
  refine ⟨⟨{CALLOK}, typeOK_of (by decide) (by decide), by decide⟩, ⟨{GUARD}, {CS_OUT}⟩,
    ?_, inv0, by decide, liveSep_nil _, {SEP2}⟩
  rw [addr_new]; exact {okpos(0, N, '⟨rfl, by decide⟩')}

set_option maxRecDepth 100000 in
theorem csW1_pre : WbLiveSite R {A('runtime.gcWriteBarrier1')} 4096 1 [] bW csW1 := by
  refine ⟨{CALLOK}, ?_, inv0, liveSep_nil _, {SEP1}⟩
  rw [addr_w1]; exact {okpos(1, N, '⟨rfl, rfl⟩')}

set_option maxRecDepth 100000 in
theorem csW2_pre : WbLiveSite R {A('runtime.gcWriteBarrier2')} 4096 2 [] bW csW2 := by
  refine ⟨{CALLOK}, ?_, inv0, liveSep_nil _, {SEP1}⟩
  rw [addr_w2]; exact {okpos(2, N, '⟨rfl, rfl⟩')}

set_option maxRecDepth 100000 in
theorem csMg_pre : MallocgcLiveSite R {A('runtime.mallocgc')} 4096 [] bW csMg := by
  refine ⟨⟨{CALLOK}, by decide, Or.inl (by decide)⟩, ⟨{GUARD}, {CS_OUT}⟩,
    ?_, inv0, by decide, liveSep_nil _, {SEP2}⟩
  rw [addr_mg]; exact {okpos(3, N, '⟨rfl, 1, by decide, by decide, by decide⟩')}

set_option maxRecDepth 100000 in
theorem csMv_pre : MemmoveLiveSite R {A('runtime.memmove')} 4096 [] bW csMv := by
  refine ⟨⟨{GUARD}, {CALLOK}, {CS_OUT}⟩, ⟨?_, inv0, liveSep_nil _, {SEP2}⟩,
    ⟨by decide, by decide, {CS_OUT}⟩, ⟨by decide, by decide, {CS_OUT}, Or.inr (by rw [rt_eq]; simp only [outside_cons, outside_nil]; decide)⟩⟩
  rw [addr_mv]; exact {okpos(4, N, '⟨rfl, loW, 0x301000, 1, by decide, by decide, by decide⟩')}

set_option maxRecDepth 100000 in
theorem csCm_pre : Janus.Contracts.Cmpstring.CmpstringPre 16 csCm :=
  ⟨{CALLOK}, Or.inl rfl, Or.inl rfl⟩

theorem r0env : R0.Env s0.mem (s0.regs 28) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _⟩ := env0
  exact h

set_option maxRecDepth 100000 in
theorem csIf_pre : IfaceeqSite R0 csIf := by
  refine ⟨⟨r0env, {GUARD}, {CALLOK}, ?_⟩, fun h => absurd (by decide) h⟩
  simp only [R0_priv, R0_depth, outside_cons, outside_nil, and_true]; decide

set_option maxRecDepth 100000 in
theorem csSb_pre : RtLivePre 4096 R (slicebytetostringSpec {st}) slicebytetostringLive {sb} [] bW csSb := by
  have hok : R.ok {sb} (argWords csSb 3) := by
    rw [show {sb} = sbA by decide]
    exact {okpos(5, N, f'⟨rfl, 0, 0x302000, by decide, {sbp}⟩')}
  unfold RtLivePre
  refine ⟨{CALLOK}, ?_, ?_, trivial, ⟨{GUARD}, {CS_OUT}⟩, hok, inv0, by decide, liveSep_nil _, {SEP2}⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, BufOK, StrIn]
    exact ⟨Or.inl (by decide), by decide, fun h => absurd (by decide) h⟩
  · simp only [slicebytetostringSpec, argWords, wordsFrom, arg, ReadsOutside, calleeStack, outside_cons, outside_nil]
    decide

'''

def conj(NS):
    sb = f'Fv256.Arm64.{NS}.sbAddr'; st = f'Fv256.Arm64.{NS}.stAddr'
    pc = lambda x: f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {A(x)} ∧ '
    L = [
      (pc('runtime.newobject') + f'NewobjectLiveSite R {A("runtime.newobject")} 4096 L b s_c', '⟨csNew, rfl, csNew_pre⟩'),
      (pc('runtime.mallocgc') + f'MallocgcLiveSite R {A("runtime.mallocgc")} 4096 L b s_c', '⟨csMg, rfl, csMg_pre⟩'),
      (pc('runtime.memmove') + f'MemmoveLiveSite R {A("runtime.memmove")} 4096 L b s_c', '⟨csMv, rfl, csMv_pre⟩'),
      (pc('runtime.gcWriteBarrier1') + f'WbLiveSite R {A("runtime.gcWriteBarrier1")} 4096 1 L b s_c', '⟨csW1, rfl, csW1_pre⟩'),
      (pc('runtime.gcWriteBarrier2') + f'WbLiveSite R {A("runtime.gcWriteBarrier2")} 4096 2 L b s_c', '⟨csW2, rfl, csW2_pre⟩'),
      (pc('runtime.cmpstring') + 'Janus.Contracts.Cmpstring.CmpstringPre 16 s_c', '⟨csCm, rfl, csCm_pre⟩'),
      (pc('runtime.ifaceeq') + 'IfaceeqSite R2 s_c', '⟨csIf, rfl, csIf_pre⟩'),
      (f'∃ s_c : State, s_c.pc = BitVec.ofNat 64 {sb} ∧ RtLivePre 4096 R (slicebytetostringSpec {st}) slicebytetostringLive {sb} L b s_c', '⟨csSb, rfl, csSb_pre⟩'),
    ]
    return L

def apply(NS):
    wf = f'lean/Fv256/Arm64/{NS}WitC.lean'; mf = f'lean/Fv256/Arm64/{NS}Main.lean'
    s = open(wf).read()
    if 'CALLSITE-BLOCK' in s: print(NS, 'WitC already done'); return
    s = s.replace('import Extracted\n', 'import Extracted\nimport Fv256.Arm64.CallSites.Base\n', 1)
    s = s.replace(f'namespace Fv256.Arm64.{NS}Wit\n', f'open Fv256.Arm64.CallSites\n\nnamespace Fv256.Arm64.{NS}Wit\n', 1)
    cj = conj(NS)
    ctext = ''.join(f'    ({c}) ∧\n' for c, _ in cj)   # inserted before the last conjunct? appended at the end below
    # insert block before the first core theorem docstring
    i = s.index('/-- The statement of the witness theorem `nonvacuous`')
    s = s[:i] + '-- CALLSITE-BLOCK\n' + block(NS) + s[i:]
    # each core: statement ends with `... :=\n  ⟨implA, ...` ; append conjuncts before ` :=`, proofs before final ⟩
    cores = [m for m in re.finditer(r'^theorem (nonvacuous_core|unquoted_core|hex_core) : ', s, re.M)]
    out = s; off = 0
    for m in cores:
        st = m.start() + off
        j = out.index(' :=\n  ⟨implA', st)
        stmt_add = ' ∧\n' + ' ∧\n'.join(f'    ({c})' for c, _ in cj)
        out = out[:j] + stmt_add + out[j:]
        k = out.index('⟩\n', out.index(' :=\n  ⟨implA', st))
        proof_add = ',\n    ' + ',\n    '.join(p for _, p in cj)
        out = out[:k] + proof_add + out[k:]
        off = len(out) - len(s)
    open(wf, 'w').write(out)
    # Main: thin witnesses
    t = open(mf).read()
    names = [f'hc{i}' for i in range(1, 9)]
    pat = ', '.join(names)
    stm = ' ∧\n    '.join(f'({c})' for c, _ in cj)
    w0 = t.index('namespace Witness')
    for thm, last in (('nonvacuous', 'hp11'), ('unquoted', 'hp12'), ('hex', 'hp12')):
        m = re.compile(r'^theorem ' + thm + r' : ', re.M).search(t, w0)
        if not m: continue
        st = m.start()
        r = t.index('    Returns (', st)
        t = t[:r] + '    ' + stm + ' ∧\n' + t[r:]
        o = t.index('obtain ⟨', st); oe = t.index(':=', o)
        assert f', {last}⟩' in t[o:oe]
        t = t[:o] + t[o:oe].replace(f', {last}⟩', f', {last}, {pat}⟩') + t[oe:]
        e = t.index('exact ⟨', o); ee = t.index('correctness impl', e)
        t = t[:ee] + pat + ',\n    ' + t[ee:]
    open(mf, 'w').write(t)
    print(NS, 'done')

for ns in sys.argv[1:]: apply(ns)
