import sys,re
sys.path.insert(0,'.')
from mkabsG import *
cs=cases('genx.out')
def limbs(a):
    l=re.findall(r'\b[st][zxym][0-3]\b',a)
    out={}
    for v in l: out[int(v[-1])]=v
    return [out.get(i,'0') for i in range(4)]
def args_of(body):
    args=[];d=0;cur=''
    for ch in body:
        if ch=='(':
            d+=1
            if d==1: cur='';continue
        if ch==')':
            d-=1
            if d==0: args.append(cur);continue
        if d>=1: cur+=ch
    return args
def gen(i,name):
    hy,g=split(cs[i])
    gg=abst(san(g))
    keep=[(san(n),abst(san(t))) for n,t in hy if n.startswith('hbr') or n.startswith('left') ]
    keep=[(n,t) for n,t in keep if not re.search(r"regs|setRegF|MemFrame|B\.wv",t)]
    names=[n for n,_ in keep]
    atoms=sorted(set(re.findall(r'\b[st][zxym][0-3]\b',gg+' '.join(t for _,t in keep))))
    hs=" ".join(f"({n} : {t})" for n,t in keep)
    bs=" ".join(f"(b{a} : {a} < 2^64)" for a in atoms)
    body=re.search(r'F\.addmodSpec (.*)$',gg).group(1)
    X,Y,M=[limbs(a) for a in args_of(body)]
    return name,atoms,keep,gg,X,Y,M,hs,bs
if __name__=='__main__':
    for i in range(len(cs)):
        hy,g=split(cs[i])
        if not g.startswith("Arm64.Memory.readLE s'.mem"): continue
        name,atoms,keep,gg,X,Y,M,hs,bs=gen(i,'x')
        print(i,[ (n,t[:3]) for n,t in keep], 'ov' if any(n=='hbr' and t.startswith('¬') for n,t in keep) else 'noov')
