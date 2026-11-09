import re
BL='18446744073709551616'
def eqs_of(f,P,L):
    t=open('/srv/fv-uint256-wB3/lean/Fv256/Proofs/Arm64/R4G/%s.lean'%f).read()
    i=t.index('def '+P); j=t.index('set_option maxHeartbeats',i)
    body=t[i:j].split("%s S' "%L,1)[1]
    parts=body.split(' ∧ ')
    eqs=[]
    for p in parts[1:]:
        m=re.match(r'(x[0-9a-f]+[rm][0-9]+) = (.*)$',p.strip(),re.S)
        if m: eqs.append((m.group(1),m.group(2)))
    return eqs
e1=eqs_of('G_284_2b4','P_284_2b4','L2b4')
e2=eqs_of('G_2b4_2f4','P_2b4_2f4','L2f4')
out='''import Fv256.Proofs.Arm64.R4Nat
import Fv256.Proofs.Common.MulModMath
set_option linter.unusedVariables false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 1024
namespace Fv256.Arm64.R4Nat
'''
vs1=' '.join(n for n,_ in e1)
hy1=' '.join('(h_%s : %s = %s)'%(n,n,e) for n,e in e1)
A='x284m32 + 2 ^ 64 * x284m24 + 2 ^ 128 * x284m16 + 2 ^ 192 * x284m120 + 2 ^ 256 * x284m8'
Bq='x284r26 + 2 ^ 64 * x284r3 + 2 ^ 128 * x284r4 + 2 ^ 192 * x284r6 + 2 ^ 256 * x284r5'
D='x2b4r7 + 2 ^ 64 * x2b4r3 + 2 ^ 128 * x2b4r4 + 2 ^ 192 * x2b4r6 + 2 ^ 256 * x2b4r5'
out+='''theorem r4_sub (x284r26 x284r3 x284r4 x284r6 x284r5 x284m32 x284m24 x284m16 x284m120 x284m8 %s : Nat)
  (b0 : x284r26 < 2 ^ 64) (b1 : x284r3 < 2 ^ 64) (b2 : x284r4 < 2 ^ 64) (b3 : x284r6 < 2 ^ 64) (b4 : x284r5 < 2 ^ 64)
  (a0 : x284m32 < 2 ^ 64) (a1 : x284m24 < 2 ^ 64) (a2 : x284m16 < 2 ^ 64) (a3 : x284m120 < 2 ^ 64) (a4 : x284m8 < 2 ^ 64)
  %s :
  (x2b4r8 = 0 ↔ %s ≤ %s) ∧ (x2b4r8 = 0 → %s + (%s) = %s) ∧ (x2b4r8 ≠ 0 → %s + (%s) = %s + 2 ^ 320) := by
  subst %s
  simp only [dt]
  iterate 6 (all_goals (try split))
  all_goals omega
'''%(vs1.replace('x284r26','').replace('x284r3','').replace('x284r4','').replace('x284r5','').replace('x284r6',''),hy1,Bq,A,D,Bq,A,D,Bq,A,' '.join('h_'+n for n,_ in e1))
vs2=' '.join(n for n,_ in e2)
hy2=' '.join('(h_%s : %s = %s)'%(n,n,e) for n,e in e2)
M='x2b4r2 + 2 ^ 64 * x2b4r1 + 2 ^ 128 * x2b4r12 + 2 ^ 192 * x2b4m72'
C='x2f4r7 + 2 ^ 64 * x2f4r3 + 2 ^ 128 * x2f4r4 + 2 ^ 192 * x2f4r6 + 2 ^ 256 * x2f4r5'
out+='''theorem r4_fix0 (x2b4r1 x2b4r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x2b4r12 x2b4m72 %s : Nat)
  (h : x2b4r8 = 0) %s :
  %s = %s := by
  subst %s
  simp only [h, ite_true]
theorem r4_fix1 (x2b4r1 x2b4r2 x2b4r3 x2b4r4 x2b4r5 x2b4r6 x2b4r7 x2b4r8 x2b4r12 x2b4m72 %s : Nat)
  (h : x2b4r8 ≠ 0)
  (b1 : x2b4r1 < 2 ^ 64) (b2 : x2b4r2 < 2 ^ 64) (b3 : x2b4r3 < 2 ^ 64) (b4 : x2b4r4 < 2 ^ 64) (b5 : x2b4r5 < 2 ^ 64) (b6 : x2b4r6 < 2 ^ 64) (b7 : x2b4r7 < 2 ^ 64) (b12 : x2b4r12 < 2 ^ 64) (b72 : x2b4m72 < 2 ^ 64)
  %s :
  %s = ((%s) + (%s)) %% 2 ^ 320 := by
  subst %s
  simp only [h, ite_false]
  janus_carry
end Fv256.Arm64.R4Nat
'''%(' '.join(n for n,_ in e2),hy2,C,D,' '.join('h_'+n for n,_ in e2),' '.join(n for n,_ in e2),hy2,C,D,M,' '.join('h_'+n for n,_ in e2))
out=out.replace('import Fv256.Proofs.Arm64.R4Nat\n','import Fv256.Proofs.Arm64.R4Nat\nimport Fv256.Arm64.R4Loop\n',1).replace('namespace Fv256.Arm64.R4Nat\n','namespace Fv256.Arm64.R4Nat\n',1)
open('/srv/fv-uint256-wB3/lean/Fv256/Proofs/Arm64/R4Qr.lean','w').write(out)
