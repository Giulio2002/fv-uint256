#!/usr/bin/env python3
"""cs_format_a64.py : add the 12 call-site conjuncts (U-WITNESS-CALLSITE) to arm64 Format (idempotent: pristine fv/wrun files first).
Edits: FormatWitA (Hw accepts the type-assertion call [x0,x1]; models), FormatWitB (hw_of, nonvacuous_core), FormatWitG (models, big_core),
FormatWitN (nil_core), Format.lean (3 witnesses); appends the aggregate lemmas csAll16 / csAll0 to FormatCS.lean."""
import subprocess, re
D = 'lean/Fv256/Arm64/'
for f in ['FormatWitA', 'FormatWitB', 'FormatWitG', 'FormatWitN', 'Format']:
    subprocess.run(['git', 'checkout', 'fv/wrun', '--', D + f + '.lean'], check=True)

A = lambda n: '(Extracted.program.contractAddr "%s")' % n
def conjs(R='R', H='H', R2='R2', rt='rt', fa='fa', data='data', tab='tab', ch='ch', zv='16'):
    """list of (conjunct text, proof term)"""
    out = []
    def site(addr_expr, pre, proof):
        out.append(('∃ (s_c : State), s_c.pc = BitVec.ofNat 64 %s ∧ %s' % (addr_expr, pre), proof))
    site(A('runtime.typeAssert'), 'Fv256.Arm64.FormatCS.TypeAssertSite %s %s s_c' % (R, H), '⟨csTA, rfl, csTA_pre⟩')
    n = A('runtime.newobject')
    site(n, 'Fv256.Arm64.CallSites.NewobjectLiveSite %s %s 4096 [] 0x400 s_c' % (R2, n), '⟨csNew, rfl, csNew_pre⟩')
    for k in (1, 2):
        a = A('runtime.gcWriteBarrier%d' % k)
        site(a, 'Fv256.Arm64.CallSites.WbLiveSite %s %s 4096 %d [] 0x400 s_c' % (R2, a, k), '⟨csW%d, rfl, csW%d_pre⟩' % (k, k))
    site(A('runtime.slicebytetostring'), 'RtPre %s 4096 %s (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c' % (rt, H), '⟨csSs, rfl, csSs_pre⟩')
    site(A('runtime.stringtoslicebyte'), 'RtPre %s 4096 %s stringtoslicebyteSpec s_c' % (rt, H), '⟨csSt, rfl, csSt_pre⟩')
    for na in (1, 1, 2):
        site(fa, 'ICallPre %d 4608 120 %s (fun _ => True) s_c' % (na, rt), '⟨csI amA 0 0 0 0 0 flatMem, rfl, ic_true amA %d (by omega) (by omega)⟩' % na)
    fb = 'fb16' if zv == '16' else 'fb0'
    bs = '[49, 54]' if zv == '16' else '[48]'
    ln = 2 if zv == '16' else 1
    site(fa, 'ICallPre 4 4608 120 %s (Fv256.FormatFastA64.FastWP %s (Fv256.FormatSpec.fastBytes %s (%s.toNat %% 2 ^ 32))) s_c' % (rt, data, zv, ch),
         '⟨csI amA %s 0x2000 (BitVec.ofNat 64 %d) (BitVec.ofNat 64 %d) 0 (strMem %s 0x2000), rfl, by rw [%s %s hch]; exact wr_pre amA %s %s (by decide) (by decide)⟩' % (data, ln, ln, bs, fb, ch, data, bs))
    site(A('fmt.Fprint'), 'ICallPre 5 4608 80 %s (Fv256.Arm64.FormatNil.FpArg %s) s_c' % (rt, data),
         '⟨csI (Extracted.program.contractAddr "fmt.Fprint") 0 %s (BitVec.ofNat 64 (2 ^ 40 + 56)) 1 1 m_fp, rfl, fp_pre _ %s⟩' % (data, data))
    bf = A('math/big.(*Int).Format')
    site(bf, 'ICallPre 4 4608 120 %s (fun sc => ∃ P : Nat, (sc.regs 0).toNat = P ∧ Fv256.IntoBig.BigObj sc.mem P %s ∧ sc.regs 1 = %s ∧ sc.regs 2 = %s ∧ (sc.regs 3).toNat %% 2 ^ 32 = %s.toNat %% 2 ^ 32) s_c' % (rt, zv, tab, data, ch),
         '⟨csI (Extracted.program.contractAddr "math/big.(*Int).Format") 0x2000 %s %s %s 0 m_bf%s, rfl, bf_pre%s _ %s %s %s⟩' % (tab, data, ch, zv, zv, tab, data, ch))
    return out

def cs_text(**kw):  # '(c1) ∧\n (c2) ∧ ... (c12)'
    return ' ∧\n    '.join('(' + c + ')' for c, _ in conjs(**kw))

# --- FormatCS aggregate lemmas
def agg(zv, name):
    cs = conjs(R='R0', H='Hw', R2='R2', rt='rtT', fa='amA', data='data', tab='tab', ch='ch', zv=zv)
    stm = ' ∧\n    '.join('(' + c + ')' for c, _ in cs)
    prf = ',\n    '.join(p for _, p in cs)
    return '\ntheorem %s (tab data ch : BitVec 64) (hch : ch = 100) :\n    %s := by\n  exact ⟨%s⟩\n' % (name, stm, prf)

f = D + 'FormatCS.lean'
s = open(f).read()
s = s.split('\n-- GENERATED-BEGIN')[0]
s = s.replace('end Fv256.Arm64.FormatCS\n', '').rstrip('\n') + '\n'
s += '''
-- GENERATED-BEGIN (scripts/cs_format_a64.py)
theorem ic_true (pc nargs : Nat) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ 120) :
    ICallPre nargs 4608 120 rtT (fun _ => True) (csI pc 0 0 0 0 0 flatMem) :=
  csI_pre (m := flatMem) rfl rtT (outside_far 120 (by omega)) (by omega) (by omega) hn hab trivial

open Janus.Contracts.IfaceModel in
-- AGGREGATE-BEGIN
'''
s += agg('16', 'csAll16') + agg('0', 'csAll0')
s += '\nend Fv256.Arm64.FormatCS\n'
open(f, 'w').write(s)

def rw(fn, fun):
    p = D + fn + '.lean'
    t = open(p).read(); t2 = fun(t); assert t2 != t, fn; open(p, 'w').write(t2)

IMP = 'import Fv256.Arm64.FormatCS\n'
# --- A: Hw + model proofs
def fa_(t):
    t = t.replace('''def Hw : RtReady := fun a _ _ view =>
  ((∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, p, 4])) ∧''', '''def Hw : RtReady := fun a _ _ view =>
  (((∃ p, a = [0, p, 2]) ∨ (∃ p, a = [0, p, 4])) ∨ (∃ x y, a = [x, y])) ∧''')
    t = t.replace('  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩\n', '''  replace hpp := hpp.resolve_right (fun ⟨x, y, hp⟩ => absurd (congrArg List.length hp) (by simp [argWords, wordsFrom, slicebytetostringSpec, stringtoslicebyteSpec]))
  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩\n''')
    return t
rw('FormatWitA', fa_)
def fg_(t):
    t = t.replace('  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩\n', '''  replace hpp := hpp.resolve_right (fun ⟨x, y, hp⟩ => absurd (congrArg List.length hp) (by simp [argWords, wordsFrom, slicebytetostringSpec, stringtoslicebyteSpec]))
  rcases hpp with ⟨p, hp⟩ | ⟨p, hp⟩\n''')
    return t

def core(fn, zv, extra=lambda t: t, nm='nonvacuous_core', tuple_end='pre⟩⟩'):
    def g(t):
        t = extra(t)
        t = t.replace('import Extracted\n', 'import Extracted\n' + IMP, 1)
        # statement end
        i = t.index('theorem ' + nm)
        j = t.index(') := by\n  refine ⟨impl', i)
        t = t[:j] + ') ∧\n    ' + cs_text(R='R', H='H', R2='R2', rt='rt', fa='fa', data='data', tab='tab', ch='ch', zv=zv) + ' := by\n  refine ⟨impl' + t[j + len(') := by\n  refine ⟨impl'):]
        # tail of the refine (up to the closing of the core theorem)
        st = t.index('  refine ⟨impl', j)
        e = t.index('\n\nend Fv256', st)
        blk = t[st:e].rstrip()
        assert blk.endswith('⟩⟩'), blk[-60:]
        blk = blk[:-1] + ', Fv256.Arm64.FormatCS.csAll%s _ _ _ rfl⟩' % zv
        return t[:st] + blk + t[e:]
    return g
def withargs(zv, tab, data):
    return lambda t: t
# the tab/data/ch arguments differ per witness: patch after generation
def core2(fn, zv, targs, extra=lambda t: t, nm='nonvacuous_core'):
    g = core(fn, zv, extra, nm)
    def h(t):
        t = g(t)
        return t.replace('csAll%s _ _ _ rfl' % zv, 'csAll%s %s rfl' % (zv, targs))
    return h
rw('FormatWitB', core2('FormatWitB', '16', 'tabV dataV chV', lambda t: t.replace('  refine ⟨ha, ?_, ?_⟩', '  refine ⟨Or.inl ha, ?_, ?_⟩')))
rw('FormatWitG', core2('FormatWitG', '16', 'tabV dataV chV', fg_, nm='big_core'))
rw('FormatWitN', core2('FormatWitN', '0', '0 0 chV', nm='nil_core'))

# --- Format.lean
def fmt(t):
    t = t.replace('import Extracted\n', 'import Extracted\n' + IMP, 1)
    for nm, zv in (('nonvacuous', '16'), ('nil', '0'), ('big', '16')):
        i = t.index('theorem %s :' % nm)
        j = t.index('    Returns ((Extracted.program.link impl)', i)
        t = t[:j] + '    (' + cs_text(R='R', H='H', R2='R2', rt='rt', fa='fa', data='data', tab='tab', ch='ch', zv=zv) + ') ∧\n' + t[j:]
        k = t.index('  obtain ⟨impl', j)
        e = t.index('\n', t.index(':= Fv256', k))
        ob = t[k:e]
        m = re.search(r'⟨h1, (.*?)⟩, h10, (.*?)(hp1[68])⟩, hp17', ob)
        # obtain pattern: first group, then flatten rest; add hcs
        ob2 = ob.replace(', hp16⟩ :=', ', hp16⟩, hcs⟩ :=').replace(', hp18⟩ :=', ', hp18⟩, hcs⟩ :=')
        ob2 = ob2.replace('⟩, h10, ', '⟩, ⟨h10, ', 1).replace('h10⟩, h11, ', 'h10⟩, ⟨h11, ', 1)
        t = t[:k] + ob2 + t[e:]
        ex = t.index('  exact ⟨impl', k)
        ee = t.index('correctness impl', ex)
        seg = t[ex:ee]
        if '⟨h10' in seg or '⟨h11' in seg:   # fv/wrun already nests the trailing group
            seg2 = seg.rstrip() + ' hcs,\n    '
        else:
            seg2 = seg.replace('⟩, h10, ', '⟩, ⟨h10, ', 1).replace('h10⟩, h11, ', 'h10⟩, ⟨h11, ', 1).rstrip()
            assert seg2.endswith(',')
            seg2 = seg2[:-1] + '⟩, hcs,\n    '
        t = t[:ex] + seg2 + t[ee:]
    return t
rw('Format', fmt)
print('done')
