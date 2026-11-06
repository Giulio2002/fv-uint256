import re
t=open('/srv/fv-uint256-wB3/lean/Fv256/Arm64/R4G/C_20_1d8.lean').read()
i=t.index('def PC_20_1d8'); j=t.index('set_option maxHeartbeats')
d=t[i:j]
body=d.split(', L1d8 S\'',1)[1]
parts=body.split(' ∧ ')
eqs=[]
for p in parts[1:]:
    m=re.match(r'(x[0-9a-f]+[rm][0-9]+) = (.*)$',p.strip(),re.S)
    if m: eqs.append((m.group(1),m.group(2)))
def sub(e):
    for k in range(5):
        e=e.replace('s.mem.readLE (BitVec.toNat (s.regs 1) + %d) 8'%(24+8*k),'a%d'%k)
        e=e.replace('s.mem.readLE (BitVec.toNat (s.regs 3) + %d) 8'%(8*k) if k else 's.mem.readLE (BitVec.toNat (s.regs 3)) 8','u%d'%k)
    return e
eqs=[(n,sub(e)) for n,e in eqs]
# closure
goal=['x1d8r3','x1d8r4','x1d8r6','x1d8r7','x1d8r9']
d_=dict(eqs)
need=set();st=list(goal)
while st:
    v=st.pop()
    if v in need: continue
    need.add(v)
    for w in re.findall(r'\bx[0-9a-f]+[rm][0-9]+\b',d_[v]): st.append(w)
sel=[(n,e) for n,e in eqs if n in need]
for n,e in sel:
    assert 'readLE' not in e,(n,e)
import json
json.dump(sel,open('q_eqs.json','w'))
print(len(sel))
