#!/usr/bin/env python3
"""cs_format_amd64.py : add the 12 call-site conjuncts (U-WITNESS-CALLSITE) to amd64 Format (idempotent: pristine fv/wrun-state files first).
Edits FormatWitB (nonvacuous_core), FormatWitBig (nonvacuous_big_core), FormatWitN (nil_core), Format.lean (3 witnesses); appends csAll16/csAll0 to FormatCS.lean.
(FormatWitA's Hw / models and hw_of in B/Big are edited by hand.)"""
import subprocess
D = 'lean/Fv256/Proofs/Amd64/'
for f in ['FormatWitB', 'FormatWitBig', 'FormatWitN', 'Format']:
    subprocess.run(['git', 'checkout', 'HEAD', '--', D + f + '.lean'], check=True)
for f in ['FormatWitB', 'FormatWitBig']:  # hw_of: Hw accepts also the 2-argument list
    p = D + f + '.lean'; t = open(p).read()
    o = "  refine ⟨ha, ?_, ?_, Or.inl (by omega), Or.inl (by simp only [hA, hB] at *; omega)⟩"
    assert o in t; open(p, 'w').write(t.replace(o, o.replace("⟨ha,", "⟨Or.inl ha,")))

A = lambda n: '(Extracted.program.contractAddr "%s")' % n
FA = '7340032'
def conjs(R='R', H='H', R2='R2', rt='rt', data='data', tab='tab', ch='ch', zv='16'):
    out = []
    def site(addr_expr, pre, proof):
        out.append(('∃ (s_c : State), s_c.rip = BitVec.ofNat 64 %s ∧ %s' % (addr_expr, pre), proof))
    site(A('runtime.typeAssert'), 'Fv256.Amd64.FormatCS.TypeAssertSite %s %s s_c' % (R, H), '⟨csTA, rfl, csTA_pre⟩')
    n = A('runtime.newobject')
    site(n, 'Fv256.CallSites.NewobjectLiveSite %s %s 4096 [] 0x400 s_c' % (R2, n), '⟨csNew, rfl, csNew_pre⟩')
    for k in (1, 2):
        a = A('runtime.gcWriteBarrier%d' % k)
        site(a, 'Fv256.CallSites.WbLiveSite %s %s 4096 %d [] 0x400 s_c' % (R2, a, k), '⟨csW%d, rfl, csW%d_pre⟩' % (k, k))
    site(A('runtime.slicebytetostring'), 'RtPre64 %s 4096 %s (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c' % (rt, H), '⟨csSs, rfl, csSs_pre⟩')
    site(A('runtime.stringtoslicebyte'), 'RtPre64 %s 4096 %s stringtoslicebyteSpec s_c' % (rt, H), '⟨csSt, rfl, csSt_pre⟩')
    for na in (1, 1, 2):
        site(FA, 'ICallPre64 %d 4608 80 %s (fun _ => True) s_c' % (na, rt), '⟨callSt64At (BitVec.ofNat 64 %s) 0 0 0 0 0 flatMem, rfl, ic_true %s %d (by omega) (by omega)⟩' % (FA, FA, na))
    fb = 'fb16' if zv == '16' else 'fb0'
    bs = '[49, 54]' if zv == '16' else '[48]'
    ln = 2 if zv == '16' else 1
    site(FA, 'ICallPre64 4 4608 80 %s (Fv256.FormatFast.FastWP %s (Fv256.FormatSpec.fastBytes %s (%s.toNat %% 2 ^ 32))) s_c' % (rt, data, zv, ch),
         '⟨callSt64At (BitVec.ofNat 64 %s) %s (BitVec.ofNat 64 %d) 0x2000 0 (BitVec.ofNat 64 %d) (strMem %s 0x2000), rfl, by rw [%s %s hch]; exact wr_pre %s %s %s (by decide) (by decide)⟩' % (FA, data, ln, ln, bs, fb, ch, FA, data, bs))
    site(A('fmt.Fprint'), 'ICallPre64 5 4608 80 %s (Fv256.Amd64.FormatNil.FpArg %s) s_c' % (rt, data),
         '⟨callSt64At (BitVec.ofNat 64 (Extracted.program.contractAddr "fmt.Fprint")) 0 (BitVec.ofNat 64 (2 ^ 40 + 56)) %s 1 1 m_fp, rfl, fp_pre _ %s⟩' % (data, data))
    bf = A('math/big.(*Int).Format')
    site(bf, 'ICallPre64 4 4608 80 %s (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat %s ∧ sc.regs 3 = %s ∧ sc.regs 1 = %s ∧ (sc.regs 7).toNat %% 2 ^ 32 = %s.toNat %% 2 ^ 32) s_c' % (rt, zv, tab, data, ch),
         '⟨callSt64At (BitVec.ofNat 64 (Extracted.program.contractAddr "math/big.(*Int).Format")) 0x2000 %s %s 0 %s m_bf%s, rfl, bf_pre%s _ %s %s %s⟩' % (data, tab, ch, zv, zv, tab, data, ch))
    return out

def cs_text(**kw):
    return '(' + ' ∧\n    '.join('(' + c + ')' for c, _ in conjs(**kw)) + ')'

def agg(zv, name):
    cs = conjs(R='R0', H='Hw', R2='R2', rt='rtT', data='data', tab='tab', ch='ch', zv=zv)
    stm = ' ∧\n    '.join('(' + c + ')' for c, _ in cs)
    prf = ',\n    '.join(p for _, p in cs)
    return '\ntheorem %s (tab data ch : BitVec 64) (hch : ch.toNat %% 2 ^ 32 ≠ 120) :\n    %s := by\n  exact ⟨%s⟩\n' % (name, stm, prf)

f = D + 'FormatCS.lean'
s = open(f).read()
s = s.split('\n-- AGGREGATE-BEGIN')[0]
s = s.replace('end Fv256.Amd64.FormatCS\n', '').rstrip('\n') + '\n'
s += '\n-- AGGREGATE-BEGIN (scripts/cs_format_amd64.py)\n' + agg('16', 'csAll16') + agg('0', 'csAll0') + '\nend Fv256.Amd64.FormatCS\n'
open(f, 'w').write(s)

def rw(fn, fun):
    p = D + fn + '.lean'
    t = open(p).read(); t2 = fun(t); assert t2 != t, fn; open(p, 'w').write(t2)

import re
def unify_rp(t):
    # hW and hP are indistinguishable call sites (same callee, arity, property): the auditor matches both to the first, so the
    # witnesses use ONE result relation for them (RP := RW)
    t = t.replace('(RW RP RF RWr RFp RBf : Res)', '(RW RF RWr RFp RBf : Res)')
    t = t.replace('RW, RP, RF, RWr, RFp, RBf', 'RW, RF, RWr, RFp, RBf')
    t = t.replace('R0z, R0z, R0z, R0z, R0z, R0z,', 'R0z, R0z, R0z, R0z, R0z,')
    return re.sub(r'\bRP\b', 'RW', t)

IMP = 'import Fv256.Proofs.Amd64.FormatCS\n'
def core(zv, tail_old, tail_new, imp_after):
    def f(t):
        t = t.replace(imp_after, imp_after + IMP, 1)
        stm_old = ' := by\n  refine ⟨implAll'
        assert t.count(stm_old) == 1
        t = t.replace(stm_old, ' ∧\n    ' + cs_text(zv=zv) + ' := by\n  refine ⟨implAll')
        assert t.count(tail_old) == 1
        return unify_rp(t.replace(tail_old, tail_new))
    return f
def st_core(t0, t1):  # the 'PreF ... s) := by' becomes 'PreF ... s) ∧ CS := by'  (statement end); handled by the generic ' := by\n  refine' split above
    pass
rw('FormatWitB', core('16', 'pre⟩⟩', 'pre⟩, Fv256.Amd64.FormatCS.csAll16 tabV dataV chV (by decide)⟩', 'import Fv256.Proofs.Amd64.FormatWitA\n'))
rw('FormatWitBig', core('16', 'bigPath_taken⟩⟩', 'bigPath_taken⟩, Fv256.Amd64.FormatCS.csAll16 tabV dataV chV (by decide)⟩', 'import Fv256.Proofs.Amd64.FormatWitA\n'))
rw('FormatWitN', core('0', 'preN⟩⟩', 'preN⟩, Fv256.Amd64.FormatCS.csAll0 0 0 chV (by decide)⟩', 'import Fv256.Proofs.Amd64.FormatWitB\n'))

# Format.lean: three witnesses
def ff(t):
    t = t.replace('import Fv256.Proofs.Amd64.FormatWitB\n', 'import Fv256.Proofs.Amd64.FormatCS\nimport Fv256.Amd64.FormatWitB\n', 1)
    # 1. statements: insert (CS) conjunct before 'Returns' of each witness
    for zv, name in (('16', 'nonvacuous'), ('0', 'nil'), ('16', 'big')):
        i = t.index('theorem %s : ∃' % name)
        j = t.index('    Returns ((Extracted.program.link impl).withExit ret)', i)
        t = t[:j] + '    ' + cs_text(zv=zv) + ' ∧\n' + t[j:]
    # 2. the obtain / exact
    g = 'h14, h15, h16, hret, hsetup, hp17'
    for old, rep in ((g + ', hp18, hp19⟩ :=', '⟨' + g + ', hp18, hp19⟩, hcs⟩ :='), (g + '⟩ :=', '⟨' + g + '⟩, hcs⟩ :='),
                     (g + ',\n    correctness', '⟨' + g + '⟩, hcs,\n    correctness'),
                     (g + ', hp18, hp19⟩ :=', None)):
        if rep is None: continue
        t = t.replace(old, rep)
    t = t.replace(g + ', hp18, hp19,\n    correctness', '⟨' + g + ', hp18, hp19⟩, hcs,\n    correctness')
    i = t.index('namespace Witness')
    return t[:i] + unify_rp(t[i:])
rw('Format', ff)
print('ok')
