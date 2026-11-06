#!/usr/bin/env python3
"""gen_segment.py TRACE.out [--lean OUT.lean --module NS --prog PROGRAM --entry ENTRYEXPR --cut CUTEXPR --pre PREABBREV [--imports "import A\nimport B"] [--frame "(lo1, hi1), (lo2, hi2)"] [--isa amd64]]
(amd64 only for now).  Without --lean it just prints the parsed state.
Older description: gen_segment.py TRACE.out OUT.lean-fragment : turn the final state record printed by `janus64_run ... until [pc]` (trace_state of the
ReachesRet goal) into an existential postcondition: every changed register / stack word gets a variable `v_k` and a fact
`S'.regs i = BitVec.ofNat 64 v_k` / `S'.mem.readLE addr 8 = v_k % 2^64`, plus `v_k = <small expression over the entry reads>`.
Prints: the list of (kind, key, expr)."""
import re,sys
import argparse
ap=argparse.ArgumentParser()
ap.add_argument('trace'); ap.add_argument('--lean'); ap.add_argument('--module',default='Seg'); ap.add_argument('--prog',default='P')
ap.add_argument('--entry',default='entry'); ap.add_argument('--cut',default='cut'); ap.add_argument('--pre',default='Pre')
ap.add_argument('--imports',default=''); ap.add_argument('--frame',default=''); ap.add_argument('--isa',default='amd64')
args=ap.parse_args()
if args.isa!='amd64': sys.exit('only amd64 is supported')
t=open(args.trace).read()
i=t.index('⊢ ReachesRet')
g=re.sub(r'\s+',' ',t[i:])
def grp(e,start=0):
    assert e[start]=='('
    d=0
    for n in range(start,len(e)):
        if e[n]=='(': d+=1
        elif e[n]==')':
            d-=1
            if d==0: return e[start+1:n], n+1
# regs chain
a=g.index('regs := ')+len('regs := ')
b=g.index(', rip :=')
regs=g[a:b].strip()
items=[]
e=regs
while e.startswith('setRegF'):
    e2=e[len('setRegF'):].lstrip()
    if e2.startswith('('):
        inner,pos=grp(e2)
    else:
        sp=e2.index(' '); inner=e2[:sp]; pos=sp
    rest=e2[pos:].lstrip()
    m=re.match(r'(\d+) ',rest)
    idx=int(m.group(1)); rest=rest[m.end():]
    if rest.startswith('('):
        val,_=grp(rest)
    else:
        val=rest.split(' ')[0]
    items.append(('reg',idx,val))
    e=inner.strip()
items.reverse()
# mem chain
c=g.index('mem := ')+len('mem := ')
d_=g.index(', ymmHi')
mem=g[c:d_].strip()
writes=[]
while True:
    m=re.search(r'\)\.writeLE ',mem[::-1] and mem)  # placeholder
    break
# parse from the right: "(<inner>).writeLE <addr> 8 (<val>)" repeatedly
e=mem
while e.startswith('('):
    inner,pos=grp(e)
    rest=e[pos:].lstrip()
    if not rest.startswith('.writeLE'): break
    rest=rest[len('.writeLE'):].lstrip()
    # addr: parenthesised group or atom
    if rest.startswith('('):
        addr,p2=grp(rest); rest=rest[p2:].lstrip()
    else:
        sp=rest.index(' '); addr=rest[:sp]; rest=rest[sp:].lstrip()
    m=re.match(r'(\d+) ',rest); n=int(m.group(1)); rest=rest[m.end():]
    if rest.startswith('('):
        val,p3=grp(rest)
    else:
        val=rest.split(' ')[0]
    writes.append((addr,n,val))
    e=inner.strip()
writes.reverse()
for k,i_,v in items: print('REG',k,i_,v[:160])
print('MEM base:',e[:60])
for a,n,v in writes: print('MEMW',a,n,v[:160])


# ---- Lean emission ----------------------------------------------------------------------------------------------------------
ALT = " | exact (Nat.mod_eq_of_lt (by first | exact (s.regs 0).isLt | exact Util.readLE8_lt _ _)).symm"
def emit(items, writes):
    vars_=[]; facts=[]; wit=[]; proofs=[]
    for kind,idx,val in items:
        m=re.match(r'BitVec\.ofNat 64 \((.*)\)$',val)
        if m:
            k=len(vars_); vars_.append('v%d'%k); wit.append(m.group(1))
            facts.append("S'.regs %d = BitVec.ofNat 64 v%d"%(idx,k)); proofs.append('first | rfl | simp [setRegF]'+ALT)
            facts.append('v%d = %s'%(k,m.group(1))); proofs.append('rfl')
        else:
            facts.append("S'.regs %d = %s"%(idx,val)); proofs.append('first | rfl | simp [setRegF]'+ALT)
    for addr,n,val in writes:
        k=len(vars_); vars_.append('v%d'%k); wit.append(val)
        facts.append("S'.mem.readLE (%s) %d = v%d %% 2 ^ 64"%(addr,n,k))
        proofs.append('first | rfl | simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self, Nat.reducePow]'+ALT)
        facts.append('v%d = %s'%(k,val)); proofs.append('rfl')
    return vars_,wit,facts,proofs
if args.lean:
    vars_,wit,facts,proofs=emit(items,writes)
    L=[args.imports,'','open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic','','namespace '+args.module,'',
       'set_option maxHeartbeats 64000000 in','set_option maxRecDepth 200000 in',
       'theorem seg (s : State) (hpc : s.rip = BitVec.ofNat 64 %s) (hpre : %s s) :'%(args.entry,args.pre),
       '    ReachesRet %s (BitVec.ofNat 64 (%s)) s (fun S\' =>'%(args.prog,args.cut),
       '      ∃ %s, %s%s) := by'%(" ".join(vars_)," ∧ ".join('(%s)'%f for f in facts),(' ∧ MemFrame s.mem S\'.mem ['+args.frame+']') if args.frame else ''),
       '  -- the caller supplies the unpacking of `hpre` and the guard facts here (see ReduceSegA.lean for an example)',
       '  janus64_run [Util.readLE_32]']
    for w in wit: L.append('  refine ⟨%s, ?_⟩'%w)
    for pf in proofs:
        L.append('  refine ⟨?_, ?_⟩'); L.append('  · '+pf)
    L.append('  janus_frame' if args.frame else '  trivial')
    L+=['','end '+args.module,'']
    open(args.lean,'w').write("\n".join(L))
