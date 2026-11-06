import json,re
sel=json.load(open('/srv/fv-uint256-wB3/scratch/q_eqs.json'))
BL='18446744073709551616'
def split_top(s, sep=' + '):
    out=[];d=0;cur='';i=0
    while i<len(s):
        ch=s[i]
        if ch=='(':d+=1
        elif ch==')':d-=1
        if d==0 and s.startswith(sep,i):
            out.append(cur);cur='';i+=len(sep);continue
        cur+=ch;i+=1
    out.append(cur);return out
def pw(k): return '2 ^ %d'%(64*k)
VAR=re.compile(r'\bx[0-9a-f]+[rm][0-9]+\b')
terms={}   # name -> (kind,i,j,canon text)
stages={}  # prefix -> list of (v,inner)
order=[]
for n,e in sel:
    if n.startswith('x114'):
        m=re.match(r'^(a|u)(\d) \* (a|u)(\d) (%|/) '+BL+r'( % '+BL+')?$',e) or re.match(r'^(a|u)(\d) \* (a|u)(\d) (%|/) '+BL+'$',e)
        mm=re.match(r'^([au])(\d) \* ([au])(\d) ([%/]) '+BL+r'( % '+BL+r')?$',e)
        assert mm,(n,e)
        x,xi,y,yi,op,mod=mm.groups()
        if x=='a': i,j=int(xi),int(yi)
        else: i,j=int(yi),int(xi)
        kind='lo' if op=='%' else 'hi'
        terms[n]=(kind,i,j,e,bool(mod))
    else:
        pre=n[:n.index('r')]
        if pre not in stages: stages[pre]=[]; order.append(pre)
        assert e.startswith('(') and e.endswith(') %% %s'%BL) or e.endswith(') %s'%('% '+BL)),e
        inner=e[1:e.rindex(') % '+BL)]
        stages[pre].append((n,inner))
def tpos(n):
    k,i,j,_,_=terms[n]
    return i+j-4 if k=='lo' else i+j-3
# duplicates check
seen={}
for n,(k,i,j,_,_) in terms.items():
    assert (k,i,j) not in seen,(n,seen.get((k,i,j)))
    seen[(k,i,j)]=n
ACC={}   # pos->var
pos={}
for n in terms: pos[n]=tpos(n)
S_terms=[]   # cumulative term list
lemmas=[]    # (text)
calls=[]
inv_prev=None
stage_info=[]
for pre in order:
    eqs=stages[pre]
    newv=[v for v,_ in eqs]
    leaves=[]
    for v,inn in eqs:
        for w in VAR.findall(inn):
            if w not in newv and w not in leaves: leaves.append(w)
    tl=[w for w in leaves if w in terms]; ol=[w for w in leaves if w not in terms]
    for v,inn in eqs:
        t=split_top(inn)[0]
        pos[v]=pos[t]
    # drop
    drop=None
    v0,in0=eqs[0]
    ops=split_top(in0)
    if '/' in in0:
        car=ops[-1]; assert car.endswith(') / '+BL)
        dinner=car[1:car.rindex(') / '+BL)]
        drop=('q0w',dinner,pos[v0]-1)
    topv,topin=eqs[-1]
    toppos=pos[topv]
    old_consumed=ol
    for w in ol: assert w in ACC.values(),(pre,w)
    # lemma sid
    lhs=' + '.join('%s * %s'%(pw(pos[v]),v) for v in newv)
    if drop: lhs+=' + %s * q0w'%pw(drop[2]) if drop[2] else ' + q0w'
    lhs+=' + %s * tc'%pw(toppos+1)
    rhs=' + '.join(('%s * %s'%(pw(pos[w]),w)) for w in leaves)
    hy=['(b_%s : %s < 2 ^ 64)'%(w,w) for w in leaves]
    hy+=['(h_%s : %s = (%s) %% %s)'%(v,v,inn,BL) for v,inn in eqs]
    hy+=['(h_tc : tc = (%s) / %s)'%(topin,BL)]
    if drop: hy+=['(h_q0w : q0w = (%s) %% %s)'%(drop[1],BL)]
    names=leaves+newv+['tc']+(['q0w'] if drop else [])
    substs=['h_'+v for v in newv]+['h_tc']+(['h_q0w'] if drop else [])
    lemmas.append('''theorem sid_%s (%s : Nat) %s :
    %s = %s := by
  subst %s
  janus_carry
'''%(pre,' '.join(names),' '.join(hy),lhs,rhs,' '.join(substs)))
    # update ACC and S
    newterms=tl
    S_prev=list(S_terms)
    S_terms+=tl
    ACC_prev=dict(ACC)
    for w in ol:
        for p in [p for p,x in ACC.items() if x==w]: del ACC[p]
    for v in newv: ACC[pos[v]]=v
    if drop: ACC[drop[2]]=drop[0]
    stage_info.append(dict(pre=pre,newv=newv,leaves=leaves,tl=tl,ol=ol,toppos=toppos,drop=drop,S_prev=S_prev,S=list(S_terms),ACC_prev=ACC_prev,ACC=dict(ACC)))
def Sexpr(L): return ' + '.join('%s * %s'%(pw(pos[w]),w) for w in L) if L else '0'
def Aexpr(A): return ' + '.join('%s * %s'%(pw(p),A[p]) for p in sorted(A)) if A else '0'
def pairfacts(L):
    prods={}
    for w in L:
        k,i,j,_,_=terms[w]; prods.setdefault((i,j),{})[k]=w
    out=[];hyps=[]
    for (i,j),d in sorted(prods.items()):
        lo=seen.get(('lo',i,j)); hi=seen.get(('hi',i,j))
        if lo and hi: out.append(('pf_%d%d'%(i,j),'%s + 2 ^ 64 * %s ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)'%(lo,hi)))
        elif hi: out.append(('pf_%d%d'%(i,j),'2 ^ 64 * %s ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1)'%hi))
        else: raise Exception('lo only')
    return out
calls_txt=[]
for k,si in enumerate(stage_info):
    pre=si['pre']
    pf=pairfacts(si['S'])
    allnames=sorted(set(VAR.findall(' '.join(t for _,t in pf)+Sexpr(si['S']))))
    # bound lemma
    lemmas.append('''theorem sb_%s (%s : Nat) %s :
    %s < %s := by
  omega
'''%(pre,' '.join(allnames),' '.join('(%s : %s)'%(n,t) for n,t in pf),Sexpr(si['S']),pw(si['toppos']+1)))
    # inv step
    newv=si['newv']; drop=si['drop']
    invprev='%s = %s'%(Aexpr(si['ACC_prev']),Sexpr(si['S_prev']))
    invnew='%s = %s'%(Aexpr(si['ACC']),Sexpr(si['S']))
    lhs=' + '.join('%s * %s'%(pw(pos[v]),v) for v in newv)
    if drop: lhs+=' + %s * q0w'%pw(drop[2]) if drop[2] else ' + q0w'
    lhs+=' + %s * tc'%pw(si['toppos']+1)
    rhs=' + '.join(('%s * %s'%(pw(pos[w]),w)) for w in si['leaves'])
    idt='%s = %s'%(lhs,rhs)
    sbt='%s < %s'%(Sexpr(si['S']),pw(si['toppos']+1))
    txt=' '.join([invprev,idt,sbt,invnew])
    allnames=sorted(set(VAR.findall(txt))|{'tc'}|({'q0w'} if (drop or 'q0w' in txt) else set()))
    lemmas.append('''theorem si_%s (%s : Nat) (hp : %s) (hi : %s) (hs : %s) : %s := by
  omega
'''%(pre,' '.join(allnames),invprev,idt,sbt,invnew))
json.dump(dict(stage_info=stage_info,terms={k:list(v) for k,v in terms.items()}),open('/srv/fv-uint256-wB3/scratch/stages.json','w'),default=str)
open('/srv/fv-uint256-wB3/scratch/stage_lemmas.lean','w').write('\n'.join(lemmas))
print(len(lemmas)); print(stage_info[-1]['ACC'])
