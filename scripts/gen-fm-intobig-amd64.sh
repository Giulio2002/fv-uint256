#!/bin/bash
# The ToBig IntoBig proof modules (Fv256/Amd64/TB/*, IntoBig as the second segment at ToBig+0x60) re-targeted at Format's extraction,
# where IntoBig is the segment at 0x4b1760 (build/ex2-amd64-Format of /srv/fv-uint256-wf2). Output: Fv256/Amd64/FM/<module>.lean
# (generated, not committed). The addresses inside IntoBig are all derived from its entry (`ripTarget`), so the entry (`ibE`) is
# the only change; the module namespace is kept (a file imports either the TB or the FM chain, never both).
# usage: gen-fm-intobig-amd64.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Amd64; mkdir -p $D/FM
for m in IntoBigDefs IntoBigFinF IntoBigClose IntoBigLoop IntoBigTail IntoBigSlow3 IntoBigMid IntoBigT; do
  python3 - "$D/TB/$m.lean" "$D/FM/$m.lean" <<'PY'
import re,sys
s=open(sys.argv[1]).read()
# IntoBig's entry in Format's extraction as an opaque definition (`ibE`), standing where ToBig's `Extracted.entry + 0x60` stood: a
# bare numeral instead made IntoBigTail 10x slower and several times bigger (the arithmetic on literals is folded by simp)
s=s.replace('(Extracted.entry + 0x60)','ibE')
assert 'Extracted.entry' not in s, 'an Extracted.entry that is not ToBig+0x60 is left'
if sys.argv[2].endswith('/IntoBigDefs.lean'):
    s=s.replace('namespace Fv256.Amd64.IntoBig\n','namespace Fv256.Amd64.IntoBig\n\n/-- IntoBig\'s entry in Format\'s extraction. -/\ndef ibE : Nat := 0x4b1760\n',1)
    assert 'def ibE' in s
    # Format's extraction has ten read-only data objects, ToBig's two. IntoBig reads two of them (the types of big.Int and of the 32-byte
    # array); `janus64_data` makes one fact per object of the program's data list, which swelled IntoBigTail to 50 GB. The precondition
    # therefore speaks of the program with only those two objects (`Pib`); `Pib_dataLoaded` gets it from the full `DataLoaded`.
    assert 'Extracted.program.DataLoaded s.mem' in s
    s=s.replace('Extracted.program.DataLoaded s.mem','Pib.DataLoaded s.mem')
    s=s.replace('def ibE : Nat := 0x4b1760\n','''def ibE : Nat := 0x4b1760

/-- the data objects IntoBig reads: the types of `big.Int` and of the 32-byte array -/
def ibData : List Janus.DataSegment :=
  Extracted.program.data.filter fun d => d.name == ".rodata+0xdc80" || d.name == ".rodata+0x19ba0"

/-- the extracted program with only those data objects -/
def Pib : Amd64.Program := { Extracted.program with data := ibData }

theorem Pib_dataLoaded {m : Amd64.Memory} (h : Extracted.program.DataLoaded m) : Pib.DataLoaded m :=
  fun d hd => h d (List.mem_filter.1 hd).1
''',1)
s=re.sub(r'import Fv256\.Amd64\.TB\.(IntoBig\w+)',r'import Fv256.Amd64.FM.\1',s)
open(sys.argv[2],'w').write(s)
PY
done
