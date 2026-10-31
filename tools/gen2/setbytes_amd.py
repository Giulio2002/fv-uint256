#!/usr/bin/env python3 -I
# setbytes_amd.py N [probe|full] [below above]
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys
n = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else 'probe'
below = int(sys.argv[3]) if len(sys.argv) > 3 else 8
above = int(sys.argv[4]) if len(sys.argv) > 4 else 24
s = open(ROOT+'/lean/Fv256/Amd64/SetBytes32.lean').read()
s = s.replace('SetBytes32', f'SetBytes{n}').replace('32 ≤ len.toNat', f'{n} ≤ len.toNat').replace('len.toNat < 32', f'len.toNat < {n}')
s = s.replace('Buffer s ptr 32 false', f'Buffer s ptr {n} false').replace('Buffer s0 ptr 32 false', f'Buffer s0 ptr {n} false')
s = s.replace('(z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + 32 ≤ z.toNat)', f'(z.toNat + 32 ≤ ptr.toNat ∨ ptr.toNat + {n} ≤ z.toNat)')
s = s.replace('(ptr.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨', f'(ptr.toNat + {n} ≤ (s.regs regSP).toNat - 8 ∨').replace('(ptr.toNat + 32 ≤ (s0.regs regSP).toNat - 8 ∨', f'(ptr.toNat + {n} ≤ (s0.regs regSP).toNat - 8 ∨')
s = s.replace('(fun i => s.mem.readLE (ptr.toNat + i) 1) 32', f'(fun i => s.mem.readLE (ptr.toNat + i) 1) {n}').replace('(fun i => s0.mem.readLE (ptr.toNat + i) 1) 32', f'(fun i => s0.mem.readLE (ptr.toNat + i) 1) {n}')
s = s.replace('[z, ptr, len, cap]', '[z, ptr, len, cap]')
s = s.replace('[z, ptr, 32, 32]', f'[z, ptr, {n}, {n}]').replace('z ptr 32 32 ret', f'z ptr {n} {n} ret').replace('z, ptr, 32, 32, hret', f'z, ptr, {n}, {n}, hret')
s = s.replace('if i = 1 then 32 else if i = 7 then 32', f'if i = 1 then {n} else if i = 7 then {n}')
s = s.replace('32 ≤ (32 : BitVec 64).toNat', f'{n} ≤ ({n} : BitVec 64).toNat')
s = s.replace('first 32 bytes', f'first {n} bytes').replace('the 32 bytes at `ptr`', f'the {n} bytes at `ptr`').replace('`len ≥ 32`', f'`len ≥ {n}`').replace('`len < 32`', f'`len < {n}`')
s = s.replace('StackWritable s 8 24', f'StackWritable s {below} {above}').replace('StackWritable s0 8 24', f'StackWritable s0 {below} {above}')
s = s.replace('(s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 24', f'(s.regs regSP).toNat - {below} ∨ (s.regs regSP).toNat + {above}')
s = s.replace('(s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 24', f'(s0.regs regSP).toNat - {below} ∨ (s0.regs regSP).toNat + {above}')
s = s.replace('((s.regs regSP).toNat - 8) 32)', f'((s.regs regSP).toNat - {below}) {below+above})').replace('((s0.regs regSP).toNat - 8) 32', f'((s0.regs regSP).toNat - {below}) {below+above}')
s = s.replace('window `[RSP-8, RSP+24)`', f'window `[RSP-{below}, RSP+{above})`')
if mode == 'probe':
    i = s.index("  refine ⟨?_, ?_⟩")
    j = s.index("\n/-- Out of bounds")
    s = s[:i] + "  trace_state\n  all_goals sorry\n" + s[j:]
open((ROOT+f'/lean/Fv256/Amd64/SetBytes{n}.lean'), 'w').write(s)
