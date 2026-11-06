#!/usr/bin/env python3
# mkol77.py ROOTMODULE...: compile the (Extracted-free) import closure of the given modules against the current framework into build/ol77
import re, sys, os, subprocess
R="/srv/fv-uint256-wJ"; L=R+"/lean"
FW=sorted(os.listdir("/srv/janus-ops/jcache-shared/v1/framework"))
FW=[f for f in FW if not f.endswith((".lock",".ready"))][0]
FWP="/srv/janus-ops/jcache-shared/v1/framework/%s/.lake/build/lib/lean"%FW
O=R+"/build/ol77"
order=[]; seen=set()
def visit(m):
    if m in seen or m=="Extracted" or m.startswith(("Lean","Init","Std","Janus","Lake")): return
    seen.add(m)
    f=L+"/"+m.replace(".","/")+".lean"
    if not os.path.exists(f): print("missing",m); return
    for l in open(f):
        mm=re.match(r"import (\S+)",l)
        if mm: visit(mm.group(1))
    order.append(m)
for m in sys.argv[1:]: visit(m)
for m in order:
    out=O+"/"+m.replace(".","/")+".olean"
    if os.path.exists(out): continue
    os.makedirs(os.path.dirname(out),exist_ok=True)
    f=m.replace(".","/")+".lean"
    env=dict(os.environ,LEAN_PATH=FWP+":"+O,LEAN_NUM_THREADS="8")
    r=subprocess.run(["memcap","-m","30G","/root/.elan/toolchains/leanprover--lean4---v4.34.1/bin/lean",f,"-o",out],cwd=L,env=env,capture_output=True,text=True)
    errs=[x for x in (r.stdout+r.stderr).split("\n") if "error" in x]
    print(m, "OK" if r.returncode==0 else "FAIL", errs[:2], flush=True)
    if r.returncode!=0: break
