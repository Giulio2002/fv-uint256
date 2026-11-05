import sys
n=int(sys.argv[1]); which=sys.argv[2]  # goal index, branch j
s=open('/srv/fv-uint256-wd/lean/Fv256/Arm64/Float64.lean').read()
i=s.index("  all_goals first")
head=s[:i]
parts=s[i:].split("\n    | (have hxj")
j={'3':1,'2':2,'1':3}[which]
br="(have hxj"+parts[j]
br=br[:br.index("sorry)")+6] if "sorry)" in br else br
br=br.strip()[1:-1].replace("\n       ","\n    ").replace("sorry","trace_state\n    sorry")
open('/srv/fv-uint256-wd/wip-d/exp/C.lean','w').write(head+f"  rotate_left {n}\n  · "+br+"\n  all_goals sorry\n\nend Fv256.Arm64.Float64\n")
