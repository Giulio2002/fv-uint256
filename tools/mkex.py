import re,sys
sup=str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')
def san(s):
    return re.sub(r'([A-Za-z_]+)✝([⁰¹²³⁴⁵⁶⁷⁸⁹]*)',lambda m:m.group(1)+'_d'+m.group(2).translate(sup),s)
src,idx,out=sys.argv[1],int(sys.argv[2]),sys.argv[3]
t=open(src).read()
cases=t.split('\ncase ')[1:]
c=cases[idx]
h=c[:c.index('⊢')]; g=c[c.index('⊢')+1:]
lines=h.split('\n')[1:]
hyps=[];cur=None
for l in lines:
    if re.match(r'^\S',l):
        if cur: hyps.append(cur)
        cur=l
    elif cur is not None:
        cur+='\n'+l
if cur: hyps.append(cur)
keep=[]
for hh in hyps:
    name=hh.split(' :')[0]
    ty=hh[len(name)+2:]
    if re.search(r'Extracted|CallSetup|RetAddr|StackGuardOK|DataLoaded|\.rip|ymmHi|retAddrOf|s\'\.regs|s\'\.xmm|s\'\.df|s\'\.mxcsr|Reaches|dataRead|StackWritable|accessible|^\s*s\.',ty) and not name.startswith(('left','hbr','right')): continue
    if name.startswith(('left','right')) and re.search(r"s'\.regs|s'\.xmm|s'\.df|s'\.mxcsr|\.rip",ty): continue
    if name in ('s','z','x','y','m','ret','s\'') or re.match(r'w✝',name): continue
    keep.append((name,ty))
decl="(s : Janus.Amd64.State) (z x y m : BitVec 64) (w_d1 w_d2: Janus.Arm64.Memory)"
body="\n".join(f"  ({san(n)} :{san(ty)})" for n,ty in keep)
g=san(g)
if '\n    MemFrame' in g: g=g[:g.index('\n    MemFrame')].rstrip().rstrip('∧').rstrip()
g=g.replace("s'.mem","w_d2").strip()
src2=f"""import Fv256.Proofs.Common.UtilF
open Janus Janus.Amd64
set_option maxRecDepth 100000
example {decl}
{body} :
  {g} := by
  sorry
"""
src2=src2.replace("w✝¹","w_d1")
src2=src2.replace("B.modSpec","Fv256.B.modSpec").replace("F.addmodSpec","Fv256.F.addmodSpec").replace("B.wv","Fv256.B.wv")
src2=re.sub(r'Arm64\.Memory\.readLE','Janus.Arm64.Memory.readLE',src2)
open(out,'w').write(src2)
print(len(keep),[n for n,_ in keep])
