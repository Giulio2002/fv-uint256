#!/bin/bash
# The arm64 IntoBig proof modules re-targeted at Format's extraction, where IntoBig is the segment at 0xb5780
# (build/ex2-arm64-Format).  Output: Fv256/Arm64/FM/<module>.lean (generated).  The namespace is kept (a file imports either the TB or the FM chain).
# usage: gen-fm-intobig-arm64.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Arm64; mkdir -p $D/FM
for m in IntoBigDefs IntoBigFinF IntoBigClose IntoBigLoop IntoBigTail IntoBigSlow3 IntoBigMid IntoBig; do
  dst=$m; [ "$m" = IntoBig ] && dst=IntoBigT
  python3 - "$D/$m.lean" "$D/FM/$dst.lean" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
if 'namespace Witness' in s:
    i=s.index('namespace Witness'); j=s.index('end Witness')+len('end Witness')
    s=s[:i]+s[j:]
s=s.replace('Extracted.entry','Fv256.Arm64.IntoBig.ibEntry')
s=s.replace('Extracted.program.link impl','(Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).IntoBig"]).link impl')
s=re.sub(r'import Fv256\.Arm64\.(IntoBig\w+)',r'import Fv256.Arm64.FM.\1',s)
if 'IntoBigDefs' in sys.argv[1]:
    s=s.replace('import ','import Fv256.FmTac\nimport ',1)
    assert 'Extracted.program.DataLoaded s.mem' in s
    s=s.replace('Extracted.program.DataLoaded s.mem','Pib.DataLoaded s.mem')
    k=s.index('def nm : String')
    s=s[:k]+'/-- IntoBig\'s entry in Format\'s extraction (a definition, like `Extracted.entry`, so that offsets stay symbolic) -/\ndef ibEntry : Nat := 0xb5780\n\n/-- the data objects IntoBig reads: the types of `big.Int` and of `[4]big.Word`.  Format\'s extraction has 26 read-only data objects; `janus_data` makes a fact per object of the program\'s data list, so the precondition speaks of the program with only these two. -/\ndef ibData : List Janus.DataSegment :=\n  Extracted.program.data.filter fun d => d.name == ".rodata+0xdc20" || d.name == ".rodata+0x19b40"\n\n/-- the extracted program with only those data objects -/\ndef Pib : Program := { Extracted.program with data := ibData }\n\ntheorem Pib_dataLoaded {m : Memory} (h : Extracted.program.DataLoaded m) : Pib.DataLoaded m :=\n  fun d hd => h d (List.mem_filter.1 hd).1\n\n'+s[k:]
open(sys.argv[2],'w').write(s)
PY
done
