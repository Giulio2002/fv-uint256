import sys,random
sys.path.insert(0,'/srv/fv-uint256-wBm/tools')
from recip_model import recip
M64=1<<64
def stage2e(r1,y2,y3):
    a=r1*r1; ah=a//M64; al=a%M64
    return ah*y3+((al*y2)//M64+al*y3+ah*y2)//M64
def stage3q(x,y):
    x0,x1,x2,x3=x; y0,y1,y2,y3=y
    return x2*y0//M64+x1*y1//M64+x0*y2//M64+(x3*y0+x2*y1+x1*y2+x0*y3)+M64*(x3*y1+x2*y2+x1*y3)+2**128*(x3*y2+x2*y3)+2**192*(x3*y3)
def sqw(R,i): return R*R//2**(64*i)%M64
def words(y): return [(y>>(64*i))%M64 for i in range(4)]
def r0f(y):
    y3=y>>192; yh=y3>>32
    return 2**32-1 if yh==2**31 else 2**63//yh
def R1(y):
    y3=y>>192; r0=r0f(y); t1=(r0*r0%M64)*y3//M64
    raw=(2*((r0*2**32+M64-t1)%M64))%M64
    return M64-1 if (raw|(2*y3%M64))==0 else raw
def R2(y):
    y0,y1,y2,y3=words(y); r1=R1(y); e=stage2e(r1,y2,y3)
    raw=(2*(r1*M64)+2**128-(2*e)%2**128)%2**128
    return 2**128-1 if raw==0 and (2*y3%M64)==0 else raw
def R3(y):
    r2=R2(y); V=stage3q([sqw(r2,i) for i in range(4)],words(y))
    return 2*(((r2*2**192+2**320-V)%2**320)//2**128)%2**192
def V4(y):
    r3=R3(y); w=[sqw(r3,i) for i in range(6)]; y0,y1,y2,y3=words(y)
    w0,w1,w2,w3,w4,w5=w
    return (w0*y3+w1*y2+w2*y1+w3*y0)+M64*(w1*y3+w2*y2+w3*y1+w4*y0)+2**128*(w2*y3+w3*y2+w4*y1+w5*y0)+2**192*(w3*y3+w4*y2+w5*y1)+2**256*(w4*y3+w5*y2)+2**320*(w5*y3)
def R4pre(y):
    r3=R3(y); return (r3*2**256+2**448-V4(y))%2**448//2**128
def R4(y):
    r=R4pre(y); return (r+2**320-1)%2**320 if 2**574<r*y else r
def model(m):
    if m<2**192: return 0
    lg=m.bit_length()-1
    if m==2**lg: return 2**256-1+2**256*((M64-1)//2**(lg%64))
    s=255-lg; y=m<<s; r=R4(y)
    return r//2**(62-s) if s<=62 else 2*r%2**320
def stages_ok(m):
    lg=m.bit_length()-1; s=255-lg; y=m<<s
    r1=R1(y); r2=R2(y); r3=R3(y)
    assert r1<M64 and abs(2**319-r1*y)<=2**260
    assert r2<2**128 and abs(2**383-r2*y)<=2**266
    assert r3<2**192 and abs(2**447-r3*y)<=2**260 and r3*y<=2**447+2**132
    rp=R4pre(y)
    assert 2**574-y-2**200<=rp*y<=2**574+2**200
def gen():
    r=random.random(); bits=random.randint(193,256)
    m=random.getrandbits(bits)|(1<<(bits-1))
    if r<0.15: m=(1<<(bits-1))+random.randint(0,5)   # y near 2^255 (if nonpow2)
    elif r<0.3: m=(1<<bits)-random.randint(1,5)
    elif r<0.5:
        # y3 near 2^63 / yh near 2^31
        d=random.choice([0,1,2,3,2**32-1,2**32,2**32+1,2**31]); lo=random.choice([0,1,random.getrandbits(192),2**192-1,random.getrandbits(128),random.getrandbits(64)])
        y=((2**63+d)<<192)+lo; sh=random.randint(0,256-bits) if False else 0
        m=y>>random.randint(0,63)
        if m.bit_length()<193: m=y
    elif r<0.6:
        y3=random.choice([2**63,2**63+1,2**64-1,2**63+2**32-1,2**63+2**32])
        m=(y3<<192)+random.choice([0,1,2**64,2**128,random.getrandbits(192)]); m>>=random.randint(0,60)
    return m
random.seed(int(sys.argv[1]) if len(sys.argv)>1 else 1)
n=0;bad=0
for it in range(int(sys.argv[2]) if len(sys.argv)>2 else 20000):
    m=gen()
    if m>=2**256 or m<2**192: continue
    n+=1
    if model(m)!=recip(m): print("MODEL MISMATCH",hex(m)); bad+=1
    lg=m.bit_length()-1
    if m!=2**lg: 
        try: stages_ok(m)
        except AssertionError: print("STAGE FAIL",hex(m)); bad+=1
    ex=(2**512-1)//m; mu=model(m)
    if not (ex-3<=mu<=ex): print("WEAK FAIL",hex(m)); bad+=1
    if m>=2**193 and not(ex-1<=mu<=ex): print("OK FAIL",hex(m)); bad+=1
print(n,bad)
