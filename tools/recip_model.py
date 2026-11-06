import random
B=1<<64; M=B-1
def mul64(a,b): p=a*b; return p>>64, p&M
def add64(a,b,c): s=a+b+c; return s&M, s>>64
def sub64(a,b,c): d=a-b-c; return d&M, 1 if d<0 else 0
def recip(m, trace=None):
    mm=[(m>>(64*i))&M for i in range(4)]
    if mm[3]==0: return 0
    s=64-mm[3].bit_length(); p=255-s
    if (mm[0]|mm[1]|mm[2]|(mm[3]&((mm[3]-1)&M)))==0:
        mu=[M]*4+[M>>(p&63)]
        return sum(v<<(64*i) for i,v in enumerate(mu))
    y=(m<<s)&((1<<256)-1)
    yy=[(y>>(64*i))&M for i in range(4)]
    yh=yy[3]>>32
    if yh==0x80000000: r0=0xffffffff
    else: r0=(0x80000000<<32)//yh  # Div32(hi=0x80000000,lo=0,yh)
    t1=r0*r0 & M
    t1,_=mul64(t1,yy[3])
    r1=(r0<<32)&M
    r1=(r1-t1)&M
    r1=(r1*2)&M
    if (r1|((yy[3]<<1)&M))==0: r1=M
    # iter2
    a2h,a2l=mul64(r1,r1)
    b2h,_=mul64(a2l,yy[2])
    c2h,c2l=mul64(a2l,yy[3])
    d2h,d2l=mul64(a2h,yy[2])
    e2h,e2l=mul64(a2h,yy[3])
    b2h,c=add64(b2h,c2l,0)
    e2l,c=add64(e2l,c2h,c)
    e2h,_=add64(e2h,0,c)
    _,c=add64(b2h,d2l,0)
    e2l,c=add64(e2l,d2h,c)
    e2h,_=add64(e2h,0,c)
    t2l,b=sub64(0,e2l,0)
    t2h,_=sub64(r1,e2h,b)
    r2l,c=add64(t2l,t2l,0)
    r2h,_=add64(t2h,t2h,c)
    if (r2h|r2l|((yy[3]<<1)&M))==0: r2h=M; r2l=M
    # iter3
    a3h,a3l=mul64(r2l,r2l)
    b3h,b3l=mul64(r2l,r2h)
    c3h,c3l=mul64(r2h,r2h)
    a3h,c=add64(a3h,b3l,0)
    c3l,c=add64(c3l,b3h,c)
    c3h,_=add64(c3h,0,c)
    a3h,c=add64(a3h,b3l,0)
    c3l,c=add64(c3l,b3h,c)
    c3h,_=add64(c3h,0,c)
    x0,x1,x2,x3=a3l,a3h,c3l,c3h
    q0,_=mul64(x2,yy[0])
    q1,t0=mul64(x3,yy[0]); q0,c=add64(q0,t0,0); q1,_=add64(q1,0,c)
    t1,_=mul64(x1,yy[1]); q0,c=add64(q0,t1,0)
    q2,t0=mul64(x3,yy[1]); q1,c=add64(q1,t0,c); q2,_=add64(q2,0,c)
    t1,t0=mul64(x2,yy[1]); q0,c=add64(q0,t0,0); q1,c=add64(q1,t1,c); q2,_=add64(q2,0,c)
    t1,t0=mul64(x1,yy[2]); q0,c=add64(q0,t0,0); q1,c=add64(q1,t1,c)
    q3,t0=mul64(x3,yy[2]); q2,c=add64(q2,t0,c); q3,_=add64(q3,0,c)
    t1,_=mul64(x0,yy[2]); q0,c=add64(q0,t1,0)
    t1,t0=mul64(x2,yy[2]); q1,c=add64(q1,t0,c); q2,c=add64(q2,t1,c); q3,_=add64(q3,0,c)
    t1,t0=mul64(x1,yy[3]); q1,c=add64(q1,t0,0); q2,c=add64(q2,t1,c)
    q4,t0=mul64(x3,yy[3]); q3,c=add64(q3,t0,c); q4,_=add64(q4,0,c)
    t1,t0=mul64(x0,yy[3]); q0,c=add64(q0,t0,0); q1,c=add64(q1,t1,c)
    t1,t0=mul64(x2,yy[3]); q2,c=add64(q2,t0,c); q3,c=add64(q3,t1,c); q4,_=add64(q4,0,c)
    _,b=sub64(0,q0,0)
    _,b=sub64(0,q1,b)
    t3l,b=sub64(0,q2,b)
    t3m,b=sub64(r2l,q3,b)
    t3h,_=sub64(r2h,q4,b)
    r3l,c=add64(t3l,t3l,0)
    r3m,c=add64(t3m,t3m,c)
    r3h,_=add64(t3h,t3h,c)
    # iter4 on python ints (direct translation of the structure)
    a4h,a4l=mul64(r3l,r3l)
    b4h,b4l=mul64(r3l,r3m)
    c4h,c4l=mul64(r3l,r3h)
    d4h,d4l=mul64(r3m,r3m)
    e4h,e4l=mul64(r3m,r3h)
    f4h,f4l=mul64(r3h,r3h)
    b4h,c=add64(b4h,c4l,0)
    e4l,c=add64(e4l,c4h,c)
    e4h,_=add64(e4h,0,c)
    a4h,c=add64(a4h,b4l,0)
    d4l,c=add64(d4l,b4h,c)
    d4h,c=add64(d4h,e4l,c)
    f4l,c=add64(f4l,e4h,c)
    f4h,_=add64(f4h,0,c)
    a4h,c=add64(a4h,b4l,0)
    d4l,c=add64(d4l,b4h,c)
    d4h,c=add64(d4h,e4l,c)
    f4l,c=add64(f4l,e4h,c)
    f4h,_=add64(f4h,0,c)
    X=[0]*7
    def mad(i,j,a,b,lowhi=None): pass
    # multiply by y (as in Go, track exactly via explicit chain)
    x1,x0=mul64(d4h,yy[0])
    x3,x2=mul64(f4h,yy[0])
    t1,t0=mul64(f4l,yy[0]); x1,c=add64(x1,t0,0); x2,c=add64(x2,t1,c); x3,_=add64(x3,0,c)
    t1,t0=mul64(d4h,yy[1]); x1,c=add64(x1,t0,0); x2,c=add64(x2,t1,c)
    x4,t0=mul64(f4h,yy[1]); x3,c=add64(x3,t0,c); x4,_=add64(x4,0,c)
    t1,t0=mul64(d4l,yy[1]); x0,c=add64(x0,t0,0); x1,c=add64(x1,t1,c)
    t1,t0=mul64(f4l,yy[1]); x2,c=add64(x2,t0,c); x3,c=add64(x3,t1,c); x4,_=add64(x4,0,c)
    t1,t0=mul64(a4h,yy[2]); x0,c=add64(x0,t0,0); x1,c=add64(x1,t1,c)
    t1,t0=mul64(d4h,yy[2]); x2,c=add64(x2,t0,c); x3,c=add64(x3,t1,c)
    x5,t0=mul64(f4h,yy[2]); x4,c=add64(x4,t0,c); x5,_=add64(x5,0,c)
    t1,t0=mul64(d4l,yy[2]); x1,c=add64(x1,t0,0); x2,c=add64(x2,t1,c)
    t1,t0=mul64(f4l,yy[2]); x3,c=add64(x3,t0,c); x4,c=add64(x4,t1,c); x5,_=add64(x5,0,c)
    t1,t0=mul64(a4h,yy[3]); x1,c=add64(x1,t0,0); x2,c=add64(x2,t1,c)
    t1,t0=mul64(d4h,yy[3]); x3,c=add64(x3,t0,c); x4,c=add64(x4,t1,c)
    x6,t0=mul64(f4h,yy[3]); x5,c=add64(x5,t0,c); x6,_=add64(x6,0,c)
    t1,t0=mul64(a4l,yy[3]); x0,c=add64(x0,t0,0); x1,c=add64(x1,t1,c)
    t1,t0=mul64(d4l,yy[3]); x2,c=add64(x2,t0,c); x3,c=add64(x3,t1,c)
    t1,t0=mul64(f4l,yy[3]); x4,c=add64(x4,t0,c); x5,c=add64(x5,t1,c); x6,_=add64(x6,0,c)
    _,b=sub64(0,x0,0)
    _,b=sub64(0,x1,b)
    r4l,b=sub64(0,x2,b)
    r4k,b=sub64(0,x3,b)
    r4j,b=sub64(r3l,x4,b)
    r4i,b=sub64(r3m,x5,b)
    r4h,_=sub64(r3h,x6,b)
    r4=r4l+(r4k<<64)+(r4j<<128)+(r4i<<192)+(r4h<<256)
    if trace is not None:
        trace.update(dict(y=y,r0=r0,r1=r1,r2=r2l+(r2h<<64),r3=r3l+(r3m<<64)+(r3h<<128),r4pre=r4,s=s,p=p))
    # final adjustment
    q=r4*y  # full
    over = q > (1<<574)
    if over: r4-=1
    if trace is not None: trace['r4']=r4; trace['over']=over
    pp=(p&63)-1
    if pp<0:
        r4=(r4*2)&((1<<320)-1); pp=0
    mu=(r4>>pp)&((1<<320)-1)
    return mu
if __name__=="__main__":
    random.seed(1)
    bad=0; low=0; n=0
    for it in range(200000):
        bits=random.randint(193,256)
        m=random.getrandbits(bits)|(1<<(bits-1))
        if random.random()<0.1: m=(1<<bits)-random.randint(1,5)
        if random.random()<0.1: m=(1<<(bits-1))+random.randint(0,5)
        ex=((1<<512)-1)//m
        mu=recip(m)
        n+=1
        if mu==ex: continue
        if mu==ex-1: low+=1; continue
        bad+=1
        if bad<5: print("BAD",hex(m),mu-ex)
    print(n,low,bad)
