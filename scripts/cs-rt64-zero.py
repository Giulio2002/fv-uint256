#!/usr/bin/env python3
"""cs-rt64-zero.py FILE : U-WITNESS-CALLSITE for the single slicebytetostring RtContract64 (H0, rtW, all-zero args) of Dec/String-shaped witness files."""
import sys
f = sys.argv[1]; s = open(f).read()
if 'csSs_pre' in s: print('skip'); sys.exit()
s = s.replace('\nimport ', '\nimport Fv256.Amd64.CallSites.Live\nimport ', 1)
blk = '''/-- The call state of `runtime.slicebytetostring` (U-WITNESS-CALLSITE): `s0`'s memory at the stub's entry, `RSP` 64 below
`s0`'s (inside the stack window), all argument words zero (`H0`). -/
def csSs : Amd64.State :=
  { s0 with rip := BitVec.ofNat 64 ssAddr, regs := fun i => if i = 0 then 0 else if i = 4 then s0.regs 4 - 64#64 else s0.regs i }

theorem csSs_rip : csSs.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") := rfl

open Fv256.CallSites in
set_option maxRecDepth 100000 in
theorem csSs_pre : RtPre64 rtW 4096 H0 (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») csSs := by
  sorry

'''
i = s.index('theorem nonvacuous')
j = s.rfind('/--', 0, i)
if j == -1 or '-/' not in s[j:i] or '\n\n' in s[s.index('-/', j):i].strip('\n'): j = i
s = s[:j] + blk + s[j:]
a = s.index('theorem nonvacuous'); a2 = s.index('    RetAddr (Extracted.program.link impl) ret ∧', a)
s = s[:a2] + '    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.slicebytetostring") ∧\n      RtPre64 rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuint64s») s_c) ∧\n' + s[a2:]
s = s.replace('model, ?w1, ?w2, pre,', 'model, ⟨csSs, csSs_rip, csSs_pre⟩, ?w1, ?w2, pre,', 1)
open(f, 'w').write(s); print('ok', f)
