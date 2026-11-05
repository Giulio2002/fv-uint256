import re,sys,hashlib
sup=str.maketrans('⁰¹²³⁴⁵⁶⁷⁸⁹','0123456789')
def san(s):
    return re.sub(r'([A-Za-z_]+)✝([⁰¹²³⁴⁵⁶⁷⁸⁹]*)',lambda m:m.group(1)+'_d'+m.group(2).translate(sup),s)
def cases(path):
    t=open(path).read()
    return ('\n'+t).split('\ncase ')[1:]
def split(c):
    h=c[:c.index('⊢')]; g=c[c.index('⊢')+1:]
    if '\n../scratch' in g: g=g[:g.find('\n../scratch')]
    hyps=[];cur=None
    for l in h.split('\n')[1:]:
        if re.match(r'^\S',l):
            if cur: hyps.append(cur)
            cur=l
        elif cur is not None: cur+='\n'+l
    if cur: hyps.append(cur)
    out=[]
    for hh in hyps:
        n=hh.split(' :')[0]; out.append((n,re.sub(r'\s+',' ',hh[len(n)+2:]).strip()))
    return out,re.sub(r'\s+',' ',g).strip()
def abst(s):
    names={}
    def rep(m):
        mem,v,off=m.group(1),m.group(2),m.group(3)
        k=(mem,v,off or '0')
        n=('s' if mem=='s' else 't')+v+(off.replace(' + ','') if off else '0')
        return n
    s=re.sub(r"Arm64\.Memory\.readLE (s'?)\.mem \(?(\w)\.toNat(?: \+ (\d+))?\)? 8",lambda m: ('s' if m.group(1)=='s' else 't')+m.group(2)+str({None:0,'8':1,'16':2,'24':3}[m.group(3)]),s)
    return s
if __name__=='__main__':
    cs=cases(sys.argv[1])
    for i,c in enumerate(cs):
        hy,g=split(c)
        keep=[(san(n),abst(san(t))) for n,t in hy if not re.search(r"regs|setRegF|MemFrame|StackGuard|State|rip|xmm|\bs'\b|df|mxcsr|ddisj|Memory\.writeLE|BitVec 64|: Nat|Flags|W64|Memory$",n+' : '+t) and not t.startswith(('BitVec 64','Nat','State','Memory','Flags'))]
        gg=abst(san(g))
        print(i,len(keep),hashlib.md5((gg+str([t for _,t in keep])).encode()).hexdigest()[:6],gg[:70])
