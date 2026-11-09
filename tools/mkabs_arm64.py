#!/usr/bin/env python3
"""mkabs_arm64.py LOG N OUT.lean NAMESPACE: turn the N leaf goals (`case hq` blocks of a `trace_state` log of
Arm64/AddModF.lean) into Extracted-free shape lemmas over abstract limbs x0..x3 y0..y3 m0..m3 (statements only,
proof body = `sorry` placeholder `PROOF`)."""
import re,sys
sup=str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')
def san(s):
    return re.sub(r'([A-Za-z_]+)✝([⁰¹²³⁴⁵⁶⁷⁸⁹]*)',lambda m:m.group(1)+'_d'+m.group(2).translate(sup),s)
log,n,out,ns=sys.argv[1],int(sys.argv[2]),sys.argv[3],sys.argv[4]
t=open(log).read()
blocks=('\n'+t).split('\ncase ')[1:]
def abst(s):
    s=re.sub(r'\s+',' ',s)
    for v,r in (('x',1),('y',2),('m',3)):
        for i,o in enumerate(['',' + 8',' + 16',' + 24']):
            if o: s=s.replace(f's.mem.readLE (BitVec.toNat (s.regs {r}){o}) 8',f'{v}{i}')
            else: s=s.replace(f's.mem.readLE (BitVec.toNat (s.regs {r})) 8',f'{v}0')
    return s
res=[]
for idx in range(min(n,len(blocks))):
    c=blocks[idx]
    if '\n⊢' not in c: continue
    h=c[:c.index('\n⊢')]; g=c[c.index('\n⊢')+2:]
    g=g.split('\nFv256/Proofs/Arm64')[0]
    hyps=[];cur=None
    for l in h.split('\n')[1:]:
        if re.match(r'^\S',l):
            if cur: hyps.append(cur)
            cur=l
        elif cur is not None: cur+='\n'+l
    if cur: hyps.append(cur)
    keep=[]
    for hh in hyps:
        name=hh.split(' :')[0]; ty=abst(san(hh[len(name)+2:]))
        if not (name.startswith('hbr') or name in('hm3','hx3','hy3')): continue
        if re.search(r's\.|regs|BitVec.toNat s',ty): continue
        keep.append((san(name),ty))
    g=abst(san(g)).strip()
    g=g.replace('F.addmodSpec','Fv256.F.addmodSpec').replace('B.modSpec','Fv256.B.modSpec')
    hs=" ".join(f"({n_} : {ty})" for n_,ty in keep)
    def atoms(s):
        s=re.sub(r'\b([xym])([0-3])\b',lambda m_: '(M.readLE (p%s%s) 8)'%(m_.group(1),'' if m_.group(2)=='0' else ' + '+str(8*int(m_.group(2)))) if m_.group(2)!='0' else '(M.readLE p%s 8)'%m_.group(1),s)
        return s
    hs=atoms(hs); g=atoms(g)
    BOUNDS=" ".join("(b%s%d : M.readLE %s 8 < 2^64)"%(v,i,("p%s"%v if i==0 else "(p%s + %d)"%(v,8*i))) for v in "xym" for i in range(4))
    res.append(f"""theorem shape{len(res)} (M : Janus.Arm64.Memory) (px py pm : Nat)
  {BOUNDS}
  {hs} :
  {g} := by
  PROOF
""")
open(out,'w').write("import Fv256.Proofs.Common.UtilF\nimport Fv256.UtilAM\n\nset_option maxRecDepth 100000\nset_option linter.all false\nnamespace "+ns+"\n\n"+"\n".join(res)+"\nend "+ns+"\n")
print(len(res),"shapes")
