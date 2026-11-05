import sys
n=int(sys.argv[1]); which=int(sys.argv[2]); L=sys.argv[3]
s=open('/srv/fv-uint256-wd/lean/Fv256/Arm64/Float64.lean').read()
i=s.index("  all_goals first"); head=s[:i]; b=s[i:]
starts=[k for k in range(len(b)) if b.startswith("(have hxj",k)]
a=starts[which]; e=starts[which+1]-len("\n    | ") if which+1<len(starts) else b.index("\n    | skip")
br=b[a+1:e].rstrip()
lines=br.split('\n')
k=[t for t,l in enumerate(lines) if l.strip()=='first'][0]
pre=lines[:k]
alt=[l for l in lines[k+1:] if L in l][0].strip()[3:-1]
pre=[l if t==0 else l[3:] for t,l in enumerate(pre)]
open('/srv/fv-uint256-wd/wip-d/exp/C.lean','w').write(head+f"  rotate_left {n}\n  · "+'\n'.join(pre)+"\n    "+alt+"\n  all_goals sorry\n\nend Fv256.Arm64.Float64\n")
