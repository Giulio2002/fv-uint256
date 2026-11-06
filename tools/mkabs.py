import re,sys
sup=str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')
def san(s):
    return re.sub(r'([A-Za-z_]+)✝([⁰¹²³⁴⁵⁶⁷⁸⁹]*)',lambda m:m.group(1)+'_d'+m.group(2).translate(sup),s)
src,idx=sys.argv[1],int(sys.argv[2])
t=open(src).read()
c=('\n'+t).split('\ncase ')[1:][idx]
h=c[:c.index('⊢')]; g=c[c.index('⊢')+1:]
hyps=[];cur=None
for l in h.split('\n')[1:]:
    if re.match(r'^\S',l):
        if cur: hyps.append(cur)
        cur=l
    elif cur is not None: cur+='\n'+l
if cur: hyps.append(cur)
def abst(s):
    s=re.sub(r'\s+',' ',s)
    for v in 'xym':
        for i,o in enumerate(['',' + 8',' + 16',' + 24']):
            if o: s=s.replace(f'Arm64.Memory.readLE s.mem ({v}.toNat{o}) 8',f'{v}{i}')
            else: s=s.replace(f'Arm64.Memory.readLE s.mem {v}.toNat 8',f'{v}0')
    return s
keep=[]
for hh in hyps:
    name=hh.split(' :')[0]; ty=abst(san(hh[len(name)+2:]))
    if not name.startswith('hbr') and name not in('hm3','hx3','hy3'): continue
    if re.search(r's\.|regs|\.toNat \+ 32',ty) : continue
    keep.append((san(name),ty))
g=san(g)
if '\n    MemFrame' in g: g=g[:g.index('\n    MemFrame')].rstrip().rstrip('∧').rstrip()
g=abst(g).strip()
g=g.replace('B.modSpec','Fv256.B.modSpec').replace('F.addmodSpec','Fv256.F.addmodSpec')
hs=" ".join(f"({n} : {ty})" for n,ty in keep)
print(f"""theorem shape{idx} (x0 x1 x2 x3 y0 y1 y2 y3 m0 m1 m2 m3 : Nat) (bx0 : x0 < 2^64) (bx1 : x1 < 2^64) (bx2 : x2 < 2^64) (bx3 : x3 < 2^64) (by0 : y0 < 2^64) (by1 : y1 < 2^64) (by2 : y2 < 2^64) (by3 : y3 < 2^64) (bm0 : m0 < 2^64) (bm1 : m1 < 2^64) (bm2 : m2 < 2^64) (bm3 : m3 < 2^64)
  {hs} :
  {g} := by
  sorry
""")
