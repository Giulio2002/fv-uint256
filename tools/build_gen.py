import sys,re
sys.path.insert(0,'/srv/fv-uint256-wf/scratch')
from genG1 import *
import emitG2
LEAN='/srv/fv-uint256-wf/lean/Fv256/Amd64/'
# --- type 1 lemmas
hdr='''import Fv256.Amd64.AddModShapes
/-! AddMod amd64 generic path (m[3]=0 or reduction needed): closers for the no-overflow aliasing variants (generated). -/
open Janus Janus.Amd64
set_option maxRecDepth 100000
set_option linter.all false
namespace Fv256.F

'''
lem=[]
kind={}
for i in range(len(cs)):
    hy,g=split(cs[i])
    if g.startswith("Arm64.Memory.readLE s'.mem"): kind[i]='A'
    elif g.startswith("Arm64.Memory.readLE w"): kind[i]='B'
    else: kind[i]='T'
src=open('tgA.lean').read()
body=src[src.index('theorem gA'):src.index('end Fv256.F')]
open(LEAN+'AddModShapesG.lean','w').write(hdr+body+"\nend Fv256.F\n")
# --- gen theorem

lines=open('/srv/fv-uint256-wf/lean/Fv256/Amd64/AddModGen.lean').read().split('\n')
# keep through the janus_frame line
k=[j for j,l in enumerate(lines) if l.startswith('  all_goals (first | janus_frame | skip)')][0]
pre=lines[:k+1]
pre=[l for l in pre]
idx=[j for j,l in enumerate(pre) if l.startswith('import Fv256.Amd64.ModSum')][0]
pre.insert(idx+1,'import Fv256.Amd64.AddModShapes\nimport Fv256.Amd64.AddModShapesG\nimport Fv256.Amd64.AddModTac')
out=pre[:]
def bclose(i):
    c=emitG2.closer(i).replace('KEYNAME','hL2')
    c=c.replace('left_d','hL2')
    head='''rename_i hL1 hL2 hR
  have key := hL2
  clear hL1 hL2 hR
  have hrodv : s.mem.readLE 5184344 16 = 18446744073709551616 := by rw [h_rodata _ _ (by decide)]; decide
  have hzd : z.toNat + 32 ≤ 5184320 ∨ 5184320 + 96 ≤ z.toNat := by
    janus64_data hdata [hz]
    first | exact h_ddisj0_0 | assumption
'''
    c=c.replace("  have key := hL2\n  clear CLEARS\n","")
    return head+c
for i in range(len(cs)):
    k_=kind[i]
    if k_=='T':
        out.append(f"  · -- goal {i}: m = 0\n    simp [Fv256.F.addmodSpec]")
    elif k_=='A':
        out.append(f"  · -- goal {i}\n    with_reducible apply Fv256.F.gA{i} <;> first | exact Fv256.Util.readLE8_lt _ _ | (with_reducible assumption)")
    else:
        body=bclose(i)
        body='\n'.join(('    '+l[2:] if l.startswith('  ') else '    '+l) if j>0 else l for j,l in enumerate(body.split('\n')))
        out.append(f"  · -- goal {i}\n    {body}")
out.append('\nend Fv256.Amd64.AddModGen\n')
open(LEAN+'AddModGen.lean','w').write('\n'.join(out))
