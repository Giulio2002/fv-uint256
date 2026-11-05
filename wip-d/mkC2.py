import sys
n=int(sys.argv[1]); which=int(sys.argv[2])
s=open('/srv/fv-uint256-wd/lean/Fv256/Arm64/Float64.lean').read()
i=s.index("  all_goals first"); head=s[:i]; b=s[i:]
starts=[k for k in range(len(b)) if b.startswith("(have hxj",k)]
a=starts[which]; e=starts[which+1]-len("\n    | ") if which+1<len(starts) else b.index("\n    | skip")
br=b[a+1:e].rstrip()
# drop alt wrapper: take only up to the 'first' and use leaf0 alternative
lines=br.split('\n')
k=[t for t,l in enumerate(lines) if l.strip()=='first'][0]
pre=lines[:k]
alt=lines[k+1:]
# leaf0 alternative lines until line starting with '        | (refine ...leaf1'
j=[t for t,l in enumerate(alt) if 'leaf1' in l][0]
leaf=alt[:j]
leaf[0]=leaf[0].replace('        | (refine','       refine')
leaf=[l for l in leaf]
out=[pre[0]]+[l for l in pre[1:]]+leaf
txt='\n'.join(out)
txt=txt.replace('\n       ','\n    ').replace('\n           ·','\n    ·').replace('\n             omega)','\n      omega')
open('/srv/fv-uint256-wd/wip-d/exp/C.lean','w').write(head+f"  rotate_left {n}\n  · "+txt+"\n  all_goals sorry\n\nend Fv256.Arm64.Float64\n")
