#!/usr/bin/env python3
"""merge-l10.py ISA(Amd64|Arm64) N : merge the generated L10Cases/*.lean case modules into N modules G01..GNN (same theorems)."""
import sys,re,os,glob
isa,n=sys.argv[1],int(sys.argv[2])
d='lean/Fv256/%s/'%isa
names=[os.path.basename(f)[:-5] for f in glob.glob(d+'L10Cases/*.lean') if not os.path.basename(f).startswith('G')]
def key(s):
    if s=='Zero': return (-1,0)
    m=re.match(r'C(\d)_(\d+)',s); return (int(m.group(1)),int(m.group(2)))
names.sort(key=key)
per=-(-len(names)//n)
groups=[names[i:i+per] for i in range(0,len(names),per)]
modof={}
for gi,g in enumerate(groups):
    gname='G%02d'%(gi+1)
    txt=None; bodies=[]
    for nm in g:
        t=open(d+'L10Cases/%s.lean'%nm).read()
        i=t.index('\nnamespace '); j=t.rindex('\nend ')
        if txt is None: txt=t[:j][:i+1]+ t[i+1:].split('\n',1)[0]+'\n'
        bodies.append(t[i:j].split('\n',2)[2])
        modof[nm]=gname
    open(d+'L10Cases/%s.lean'%gname,'w').write(txt+''.join(bodies)+'\nend Fv256.%s.Log10\n'%isa)
    sys.stderr.write('%s: %d cases\n'%(gname,len(g)))
for nm in names: os.remove(d+'L10Cases/%s.lean'%nm)
# rewrite Log10.lean imports
p=d+'Log10.lean'; t=open(p).read()
seen=set(); out=[]
for line in t.split('\n'):
    m=re.match(r'import Fv256\.%s\.L10Cases\.(\S+)$'%isa,line)
    if m:
        g=modof[m.group(1)]
        if g in seen: continue
        seen.add(g); line='import Fv256.%s.L10Cases.%s'%(isa,g)
    out.append(line)
open(p,'w').write('\n'.join(out))
