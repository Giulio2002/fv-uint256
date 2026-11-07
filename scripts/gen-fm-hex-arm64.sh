#!/bin/bash
# Re-targets the arm64 Hex proof at Format's extraction (Hex is the segment at Format+0x1c60 = 0xb7c90 - 0xb6030).
# Output: Fv256/Arm64/FM/Hex.lean (generated).  Also: exports InRanges of the result string, and the narrower frame [sp-4208, sp-8)
# (the saved x29/x30 of the caller are not written).
# usage: gen-fm-hex-arm64.sh LEAN_DIR
L=${1:-lean}; D=$L/Fv256/Arm64; mkdir -p $D/FM
python3 - "$D/Hex.lean" "$D/FM/Hex.lean" <<'PY'
import sys
s=open(sys.argv[1]).read()
i=s.index('namespace Witness'); j=s.index('end Witness')+len('end Witness')
s=s[:i]+s[j:]
s=s.replace('Extracted.entry','(Extracted.entry + 0x1c60)')
s=s.replace('Extracted.program.link impl','(Extracted.program.onlySegments ["github.com/holiman/uint256.(*Int).Hex"]).link impl')
# narrower frame
n0=s.count('s.sp.toNat + 8)]')+s.count('BitVec.toNat s.sp + 8)]')
s=s.replace('(s.sp.toNat - 4208, s.sp.toNat + 8)]','(s.sp.toNat - 4208, s.sp.toNat - 8)]')
s=s.replace('(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp + 8)','(BitVec.toNat s.sp - 4208, BitVec.toNat s.sp - 8)')
# InRanges in the post
old="HexOut (val256 s.mem z.toNat) s'.mem (s'.regs 0).toNat (s'.regs 1).toNat ∧"
assert s.count(old)==2, s.count(old)
s=s.replace(old, old+" InRanges (s'.regs 0).toNat (s'.regs 1).toNat rt ∧")
old2="    refine ⟨⟨nib, ?_, ?_⟩, hch.trans hcall fun a n h => ⟨h, h⟩⟩\n"
assert s.count(old2)==1
s=s.replace(old2,"    refine ⟨⟨nib, ?_, ?_⟩, ?_, hch.trans hcall fun a n h => ⟨h, h⟩⟩\n")
old3="        (fun p h1 h2 => hbuf p h1 (by omega))\n"
assert s.count(old3)==1
s=s.replace(old3, old3+"""    · have hl : BitVec.toNat w7 = nib + 2 := by have := hR.1.1; simpa [Spec.strBytes] using this
      rcases hR.2 with h | ⟨h, -⟩ | ⟨h, hb, -⟩ | ⟨-, -, hin⟩
      · omega
      · omega
      · exact absurd rfl hb
      · exact hin
""")
s=s.replace('h_data0','h_data7').replace('h_ddisj0_0','h_ddisj0_7')
s=s.replace('  janus_data hd [hwa]\n','  janus_data hd [hwa]\n  fm_clear_ddisj 7\n')
assert 'fm_clear_ddisj 7' in s
s=s.replace('import ','import Fv256.FmTac\nimport ',1)
s=s.replace('namespace Fv256.Arm64.Hex','namespace Fv256.Arm64.FM.Hex').replace('end Fv256.Arm64.Hex','end Fv256.Arm64.FM.Hex')
open(sys.argv[2],'w').write(s)
PY
