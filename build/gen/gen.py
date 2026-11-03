import re,sys,os
D='/srv/fv-uint256-wB/lean/Fv256/Amd64/'
OUT=sys.argv[1] if len(sys.argv)>1 else '/srv/fv-uint256-wB/build/gen/out/'
os.makedirs(OUT,exist_ok=True)
files=['UdivremC','UdivremD','UdivremE','UdivremF','UdivremG','UdivremH','UdivremI','UdivremJ','UdivremK','UdivremL']
def sub(t):
    t=re.sub(r'\bulen ≤ 4','ulen ≤ L',t)
    t=re.sub(r'\bul ≤ 4','ul ≤ L',t)
    t=re.sub(r'\bul = 4','ul = L',t)
    t=re.sub(r'\bql = 4','ql = L',t)
    t=t.replace('up + 32','up + 8 * L')
    t=t.replace('qp + 32','qp + 8 * L')
    t=re.sub(r'accessible up 32 ','accessible up (8 * L) ',t)
    t=re.sub(r'accessible qp 32 ','accessible qp (8 * L) ',t)
    t=re.sub(r'(wv [A-Za-z0-9\']+ up) 4\b',r'\1 L',t)
    t=re.sub(r'(wv [A-Za-z0-9\']+ qp) 4\b',r'\1 L',t)
    t=re.sub(r'(wv_of_frame [^\n]*? up) 4\b',r'\1 L',t)
    t=re.sub(r'(wv_of_frame [^\n]*? qp) 4\b',r'\1 L',t)
    t=re.sub(r'(wv_congr M\' M remp up) 4\b',r'\1 L',t)
    t=re.sub(r'(wv_zero_word M0 qp) 4\b',r'\1 L',t)
    t=re.sub(r'(wv_ext M4 qp ulen) 4\b',r'\1 L',t)
    t=re.sub(r'\bj < 4 → M0.readLE \(qp','j < L → M0.readLE (qp',t)
    t=t.replace('(e6 : R 6 = BitVec.ofNat 64 4)','(e6 : R 6 = BitVec.ofNat 64 L)').replace('e6 : R 6 = BitVec.ofNat 64 4\n','e6 : R 6 = BitVec.ofNat 64 L\n')
    t=t.replace('(s.regs 6).toNat = 4 ∧ (s.regs 3).toNat = 4','(s.regs 6).toNat = L ∧ (s.regs 3).toNat = L')
    t=t.replace('have e6 : s.regs 6 = BitVec.ofNat 64 4','have e6 : s.regs 6 = BitVec.ofNat 64 L')
    return t
names=set()
res={}
for f in files:
    t=sub(open(D+f+'.lean').read())
    # split into theorem chunks
    parts=re.split(r'(?m)^(?=(?:set_option [^\n]*\n)*(?:theorem|def|structure) )',t)
    out=[]
    for ch in parts:
        m=re.search(r'(?m)^theorem (\w+) \(s0 : State\)',ch)
        if m and re.search(r'\bL\b',ch.split(':= by')[0]) :
            ch=ch.replace('theorem %s (s0 : State)'%m.group(1),'theorem %s {L : Nat} (hL : L ≤ 8) (s0 : State)'%m.group(1),1)
            names.add((f,m.group(1)))
        out.append(ch)
    res[f]=''.join(out)
# call sites
for f in files:
    t=res[f]
    for (g,n) in names:
        t=re.sub(r'(?<![\w.])(?:Fv256\.Amd64\.%s\.)?%s s0 '%(g,n), lambda m: m.group(0).replace(' s0 ',' hL s0 '), t)
    res[f]=t
for f in files:
    t=res[f]
    t=t.replace('structure Front (R : Nat → W64)','structure Front (L : Nat) (R : Nat → W64)')
    t=re.sub(r'(?<![\w])Front (R\'?|R) ',lambda m:'Front L '+m.group(1)+' ',t)
    t=t.replace('def UPost (s0 : State)','def UPost (L : Nat) (s0 : State)')
    t=re.sub(r'(?<![\w])UPost (s0) ',r'UPost L \1 ',t)
    t=re.sub(r'(UdivremC\.mid1 hL s0 dp qp qcap ql up remp n) 4 ',r'\1 L ',t)
    t=re.sub(r'(UdivremD\.mid2 hL s0 dp qp qcap ql up remp n) 4 ',r'\1 L ',t)
    t=re.sub(r'(UdivremC\.ulen_loop hL s0 up qp M5 [^\n]*? hqp) 4 ',r'\1 L ',t)
    if f in ('UdivremK','UdivremL'):
        t=t.replace('Buffer s (s.regs 0) 32 true','Buffer s (s.regs 0) (8 * L) true').replace('Buffer s (s.regs 7) 32 false','Buffer s (s.regs 7) (8 * L) false')
        t=t.replace('(s.regs 0).toNat + 32','(s.regs 0).toNat + 8 * L').replace('(s.regs 7).toNat + 32','(s.regs 7).toNat + 8 * L')
        t=re.sub(r'(wv [^ ]+ \(s\.regs [07]\)\.toNat) 4\b',r'\1 L',t)
        t=t.replace('theorem udivrem_summary :','theorem udivrem_summary {L : Nat} (hL : L ≤ 8) :')
        t=t.replace('theorem udivrem_nil :','theorem udivrem_nil {L : Nat} (hL : L ≤ 8) :').replace('theorem udivrem_rem :','theorem udivrem_rem {L : Nat} (hL : L ≤ 8) :')
        t=t.replace('Fv256.Amd64.UdivremK.udivrem_summary s hpc','Fv256.Amd64.UdivremK.udivrem_summary hL s hpc')
        t=t.replace('UdivremH.front s ','UdivremH.front hL s ')
        t=re.sub(r'(UdivremI\.case[KL]|UdivremJ\.caseOne) s ',r'\1 hL s ',t)
        t=t.replace('UPost s s.mem','UPost L s s.mem')
    open(OUT+f+'.lean','w').write(t)
print(sorted(names))
