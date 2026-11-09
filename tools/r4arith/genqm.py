import re,sys
sys.path.insert(0,'/srv/fv-uint256-wB3/scratch')
BL='18446744073709551616'
t=open('/srv/fv-uint256-wB3/lean/Fv256/Proofs/Arm64/R4G/G_1d8_284.lean').read()
i=t.index('def P_1d8_284'); j=t.index('set_option maxHeartbeats',i)
d=t[i:j]
body=d.split("L284 S' ",1)[1]
parts=body.split(' ∧ ')
eqs=[]
for p in parts[1:]:
    m=re.match(r'(x[0-9a-f]+[rm][0-9]+) = (.*)$',p.strip(),re.S)
    if m: eqs.append((m.group(1),m.group(2)))
vs=' '.join(n for n,_ in eqs)
hy=' '.join('(h_%s : %s = %s)'%(n,n,e) for n,e in eqs)
out='''import Fv256.Proofs.Arm64.R4Nat
set_option linter.unusedVariables false
set_option maxHeartbeats 64000000
set_option maxRecDepth 200000
set_option exponentiation.threshold 1024
namespace Fv256.Arm64.R4Nat
theorem qm_low (x1d8r1 x1d8r2 x1d8r3 x1d8r4 x1d8r5 x1d8r6 x1d8r7 x1d8r9 x1d8m64 %s : Nat)
  (b1 : x1d8r1 < 2 ^ 64) (b2 : x1d8r2 < 2 ^ 64) (b3 : x1d8r3 < 2 ^ 64) (b4 : x1d8r4 < 2 ^ 64) (b5 : x1d8r5 < 2 ^ 64) (b6 : x1d8r6 < 2 ^ 64) (b7 : x1d8r7 < 2 ^ 64) (b9 : x1d8r9 < 2 ^ 64) (bm : x1d8m64 < 2 ^ 64)
  %s :
  x284r26 + 2 ^ 64 * x284r3 + 2 ^ 128 * x284r4 + 2 ^ 192 * x284r6 + 2 ^ 256 * x284r5 =
  ((x1d8r3 + 2 ^ 64 * x1d8r4 + 2 ^ 128 * x1d8r6 + 2 ^ 192 * x1d8r7 + 2 ^ 256 * x1d8r9) * (x1d8r2 + 2 ^ 64 * x1d8r1 + 2 ^ 128 * x1d8m64 + 2 ^ 192 * x1d8r5)) %% 2 ^ 320 := by
  subst %s
  janus_carry
end Fv256.Arm64.R4Nat
'''%(vs,hy,' '.join('h_'+n for n,_ in eqs))
open('/srv/fv-uint256-wB3/lean/Fv256/Proofs/Arm64/R4Qm.lean','w').write(out)
