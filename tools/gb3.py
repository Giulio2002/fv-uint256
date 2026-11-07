#!/usr/bin/env python3
"""gb3.py: helpers for FV-B3 stage glue generation"""
import re
D='/srv/fv-uint256-wBm/lean/Fv256/Amd64/'
LIVE=open(D+'RecipLive.lean').read()
def ldef(name):
    i=LIVE.index('def %s (s S : State)'%name)
    j=LIVE.index(':= ',i) if False else LIVE.index('Prop :=',i)
    head=LIVE[i:j]
    args=re.search(r'State\) \(([^:]*) : Nat\)',head).group(1).split()
    k=LIVE.find('\ndef ',j)
    body=LIVE[j+7:k if k>0 else len(LIVE)]
    conj=[c.strip() for c in re.split(r'\s*∧\n',body.strip())]
    return args,conj
def bnd(name,var,h):
    """projection path of the conjunct `var < 2 ^ 64` of hypothesis h : L<name> ..."""
    args,conj=ldef(name)
    idx=[i for i,c in enumerate(conj) if c==var+' < 2 ^ 64']
    assert idx,(name,var)
    i=idx[0]; n=len(conj)
    p='.2'*i + ('' if i==n-1 else '.1')
    return '(%s%s)'%(h,p) if p else h
def theorem_stmt(path,thm):
    t=open(path).read()
    i=t.index('theorem '+thm); j=t.index(':= by',i)
    return t[i:j]

def split_conj(s):
    return [x.strip() for x in s.split(' ∧ ')]
def gen_stage4():
    A=D+'RecipArith4p.lean'
    st=theorem_stmt(A,'sum4p')
    m=re.search(r'∃ ([^,]*), (L660 s S [^∧]*)∧ RecRegs s S ∧ RecMem s S.mem y3 ∧(.*)$',st,re.S)
    p4vars=m.group(1).split(); l660=m.group(2).split()[3:]
    facts=split_conj(m.group(3).strip())
    # binder names of L660 in sum4q
    q660,_=ldef('L660')
    mp=dict(zip(q660,l660))   # 4q binder -> actual var in sum4p's world
    qst=theorem_stmt(D+'RecipArith4q.lean','sum4q')
    hh=re.findall(r'\((h[lh])(\d\d) : (\S+) = w(\d) \* y(\d) (%|/) 18446744073709551616\)',qst)
    return p4vars,l660,facts,mp,hh,q660
if __name__=='__main__':
    p4vars,l660,facts,mp,hh,q660=gen_stage4()
    print(len(p4vars),len(l660),len(facts),len(hh)); print(facts[:3]); print(hh[:4])

def subst(txt,mp):
    return re.sub(r'\b[a-z0-9_]+\b',lambda m:mp.get(m.group(0),m.group(0)),txt)
