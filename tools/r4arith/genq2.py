exec(open('/srv/fv-uint256-wB3/scratch/genq.py').read().split("json.dump(dict(stage_info")[0])
# ---- reconstruct binder name lists as in generator
out=[]
HDR='''import Fv256.Arm64.R4Nat
set_option linter.unusedVariables false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 1024
namespace Fv256.Arm64.R4Nat

theorem bdm {v E : Nat} (h : v = E %% %s) : v < 2 ^ 64 := by rw [h]; exact Nat.mod_lt _ (by decide)
theorem bdh {a u v : Nat} (ha : a < 2 ^ 64) (hu : u < 2 ^ 64) (h : v = a * u / %s) : v < 2 ^ 64 := by
  rw [h]
  have := Nat.mul_lt_mul'' ha hu
  exact Nat.div_lt_of_lt_mul (by omega)
theorem pb2 (a u : Nat) (ha : a < 2 ^ 64) (hu : u < 2 ^ 64) : a * u %% 2 ^ 64 + 2 ^ 64 * (a * u / 2 ^ 64) ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
  have h1 : a * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 := Nat.div_add_mod (a * u) (2 ^ 64)
  omega
theorem pb1 (a u : Nat) (ha : a < 2 ^ 64) (hu : u < 2 ^ 64) : 2 ^ 64 * (a * u / 2 ^ 64) ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by
  have h1 : a * u ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := Nat.mul_le_mul (by omega) (by omega)
  have h2 := Nat.div_add_mod (a * u) (2 ^ 64)
  omega
'''%(BL,BL)
out.append(HDR.replace('%%','%'))
out.append(open('/srv/fv-uint256-wB3/scratch/stage_lemmas.lean').read())
# fin lemma
T='''2 ^ 256 * ((a3 * u0 / 2 ^ 64) + (a2 * u1 / 2 ^ 64) + (a1 * u2 / 2 ^ 64) + (a0 * u3 / 2 ^ 64)) +
      2 ^ 256 * (a4 * u0 + a3 * u1 + a2 * u2 + a1 * u3 + a0 * u4) +
      2 ^ 320 * (a4 * u1 + a3 * u2 + a2 * u3 + a1 * u4) +
      2 ^ 384 * (a4 * u2 + a3 * u3 + a2 * u4) +
      2 ^ 448 * (a4 * u3 + a3 * u4) +
      2 ^ 512 * (a4 * u4)'''
last=stage_info[-1]
inv_last='%s = %s'%(Aexpr(last['ACC']),Sexpr(last['S']))
fh=[];fn=set(['q0w'])
for (k,i,j),n in sorted(seen.items(), key=lambda t:(t[0][1],t[0][2],t[0][0])):
    pass
prods=sorted(set((i,j) for (k,i,j) in seen))
for (i,j) in prods:
    lo=seen.get(('lo',i,j)); hi=seen.get(('hi',i,j))
    if lo and hi: fh.append('(hP_%d%d : a%d * u%d = %s + 2 ^ 64 * %s)'%(i,j,i,j,lo,hi))
    elif hi: fh.append('(hP_%d%d : %s = a%d * u%d / 2 ^ 64)'%(i,j,hi,i,j))
    else: raise
names_fin=sorted(set(VAR.findall(inv_last+' '.join(fh)))|{'q0w'}|{'a%d'%i for i in range(5)}|{'u%d'%i for i in range(5)})
V5='x1d8r3 + '+' + '.join('%s * x1d8r%s'%(pw(k),n) for k,n in zip(range(1,5),['4','6','7','9']))
out.append('''theorem fin (%s : Nat) (hq : q0w < 2 ^ 64) (hinv : %s) %s :
    %s = (%s) / 2 ^ 320 := by
  omega
'''%(' '.join(names_fin),inv_last,' '.join(fh),V5.replace('2 ^ 0 * ','',1) if False else V5,T))
# q_chain
allv=[n for n,_ in sel]
hy=' '.join('(h_%s : %s = %s)'%(n,n,e) for n,e in sel)
body=[]
body.append('  have ha : ∀ x : Nat, x < 2 ^ 64 → x < 2 ^ 64 := fun x h => h')
ai={'a%d'%i:'h%d'%i for i in range(5)}; ai.update({'u%d'%i:'g%d'%i for i in range(5)})
# canonical term defs and bounds
for n,(k,i,j,e,mod) in terms.items():
    swapped = e.startswith('u')
    if k=='lo':
        c='a%d * u%d %% %s'%(i,j,BL)
        pf='by rw [h_%s%s]'%(n,(', Nat.mul_comm u%d a%d'%(j,i)) if swapped else '')
        body.append('  have c_%s : %s = %s := %s'%(n,n,c,pf))
        body.append('  have b_%s : %s < 2 ^ 64 := bdm c_%s'%(n,n,n))
    else:
        c='a%d * u%d / %s'%(i,j,BL)
        if mod:
            pf='by rw [h_%s%s]; exact Nat.mod_eq_of_lt (bdh h%d g%d rfl)'%(n,(', Nat.mul_comm u%d a%d'%(j,i)) if swapped else '',i,j)
        else:
            pf='by rw [h_%s%s]'%(n,(', Nat.mul_comm u%d a%d'%(j,i)) if swapped else '')
        body.append('  have c_%s : %s = %s := %s'%(n,n,c,pf))
        body.append('  have b_%s : %s < 2 ^ 64 := bdh h%d g%d c_%s'%(n,n,i,j,n))
for n,e in sel:
    if n not in terms: body.append('  have b_%s : %s < 2 ^ 64 := bdm h_%s'%(n,n,n))
body.append('  have b_q0w : ((%s) %% %s) < 2 ^ 64 := Nat.mod_lt _ (by decide)'%(stage_info[7]['drop'][1],BL))
# pair facts
for (i,j) in prods:
    lo=seen.get(('lo',i,j)); hi=seen.get(('hi',i,j))
    if lo and hi: body.append('  have pf_%d%d : %s + 2 ^ 64 * %s ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by rw [c_%s, c_%s]; exact pb2 _ _ h%d g%d'%(i,j,lo,hi,lo,hi,i,j))
    else: body.append('  have pf_%d%d : 2 ^ 64 * %s ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) := by rw [c_%s]; exact pb1 _ _ h%d g%d'%(i,j,hi,hi,i,j))
for (i,j) in prods:
    lo=seen.get(('lo',i,j)); hi=seen.get(('hi',i,j))
    if lo and hi: body.append('  have hP_%d%d : a%d * u%d = %s + 2 ^ 64 * %s := by rw [c_%s, c_%s]; exact (Nat.mod_add_div _ _).symm'%(i,j,i,j,lo,hi,lo,hi))
    else: body.append('  have hP_%d%d : %s = a%d * u%d / 2 ^ 64 := by rw [c_%s]'%(i,j,hi,i,j,hi))
# stage calls
q0expr='(((%s) %% %s))'%(stage_info[7]['drop'][1],BL)
prev='(rfl : (0:Nat) = 0)'
for k,si in enumerate(stage_info):
    pre=si['pre']; newv=si['newv']; drop=si['drop']; leaves=si['leaves']
    tcE=None
    topin=stages[pre][-1][1]
    tc='((%s) / %s)'%(topin,BL)
    q0='(((%s) %% %s))'%(drop[1],BL) if drop else None
    names=leaves+newv+[tc]+([q0] if drop else [])
    args=' '.join(names if False else [(n if n not in ('tc',) else n) for n in names])
    args=' '.join(leaves+newv)+' '+tc+(' '+q0 if drop else '')
    hs=' '.join(['b_%s'%w for w in leaves]+['h_%s'%v for v in newv]+['rfl']+(['rfl'] if drop else []))
    body.append('  have id_%s := sid_%s %s %s'%(pre,pre,args,hs))
    # sb
    pf=pairfacts(si['S'])
    allnames=sorted(set(VAR.findall(' '.join(t for _,t in pf)+Sexpr(si['S']))))
    body.append('  have sb_%s := sb_%s %s %s'%(pre,pre,' '.join(allnames),' '.join('pf_'+n[3:] for n,_ in pf)))
    invprev_t='%s = %s'%(Aexpr(si['ACC_prev']),Sexpr(si['S_prev']))
    invnew_t='%s = %s'%(Aexpr(si['ACC']),Sexpr(si['S']))
    idt_names=None
    txt=' '.join([invprev_t, ' + '.join('%s * %s'%(pw(pos[v]),v) for v in newv)+' '+(('+ '+pw(drop[2])+' * q0w') if drop else ''), ' + '.join('%s * %s'%(pw(pos[w]),w) for w in leaves),Sexpr(si['S'])])
    nm=sorted(set(VAR.findall(txt))|{'tc'}|({'q0w'} if (drop or 'q0w' in txt) else set()))
    # args: tc and q0w expressions
    def argof(n):
        if n=='tc': return tc
        if n=='q0w': return q0expr
        return n
    body.append('  have iv_%s := si_%s %s %s id_%s sb_%s'%(pre,pre,' '.join(argof(n) for n in nm),prev if k==0 else 'iv_'+stage_info[k-1]['pre'],pre,pre))
body.append('  exact fin %s b_q0w iv_%s %s'%(' '.join(q0expr if n=='q0w' else n for n in names_fin),stage_info[-1]['pre'],' '.join('hP_%d%d'%p for p in prods)))
qc='''theorem q_chain (a0 a1 a2 a3 a4 u0 u1 u2 u3 u4 %s : Nat)
    (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) (h2 : a2 < 2 ^ 64) (h3 : a3 < 2 ^ 64) (h4 : a4 < 2 ^ 64)
    (g0 : u0 < 2 ^ 64) (g1 : u1 < 2 ^ 64) (g2 : u2 < 2 ^ 64) (g3 : u3 < 2 ^ 64) (g4 : u4 < 2 ^ 64)
    %s :
    x1d8r3 + 2 ^ 64 * x1d8r4 + 2 ^ 128 * x1d8r6 + 2 ^ 192 * x1d8r7 + 2 ^ 256 * x1d8r9 = (%s) / 2 ^ 320 := by
'''%(' '.join(allv),hy,T)
open('/srv/fv-uint256-wB3/scratch/qc_body.txt','w').write('\n'.join(body))
open('/srv/fv-uint256-wB3/scratch/qc_head.txt','w').write(qc)
open('/srv/fv-uint256-wB3/scratch/qc_pre.txt','w').write('\n'.join(out))
print(names_fin)
