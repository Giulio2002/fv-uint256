#!/usr/bin/env python3 -I
# setbytes_arm.py N [mode]   mode: probe (trace goals) | full
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys
n = int(sys.argv[1]); mode = sys.argv[2] if len(sys.argv) > 2 else 'probe'
below = int(sys.argv[3]) if len(sys.argv) > 3 else 24
above = int(sys.argv[4]) if len(sys.argv) > 4 else 24
tmpl = open(ROOT+'/lean/Fv256/Arm64/SetBytes32.lean').read()
s = tmpl.replace('SetBytes32', f'SetBytes{n}').replace('32 ≤ len.toNat', f'{n} ≤ len.toNat').replace('len.toNat < 32', f'len.toNat < {n}')
s = s.replace('StackOK s 24 24', f'StackOK s {below} {above}').replace('StackOK s0 24 24', f'StackOK s0 {below} {above}')
s = s.replace('(s.sp.toNat - 24) 48', f'(s.sp.toNat - {below}) {below+above}').replace('(s0.sp.toNat - 24) 48', f'(s0.sp.toNat - {below}) {below+above}')
s = s.replace('(s.sp.toNat - 24) 48', f'(s.sp.toNat - {below}) {below+above}')
s = s.replace('Ptr s.mem ptr 32 false', f'Ptr s.mem ptr {n} false').replace('Disjoint z.toNat 32 ptr.toNat 32', f'Disjoint z.toNat 32 ptr.toNat {n}')
s = s.replace('Disjoint ptr.toNat 32 (', f'Disjoint ptr.toNat {n} (').replace('Ptr s0.mem ptr 32 false', f'Ptr s0.mem ptr {n} false')
s = s.replace('Disjoint z.toNat 32 ptr.toNat 32', f'Disjoint z.toNat 32 ptr.toNat {n}')
s = s.replace('fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) 32', f'fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) {n}')
s = s.replace('fromBE (fun i => s0.mem.readLE (ptr.toNat + i) 1) 32', f'fromBE (fun i => s0.mem.readLE (ptr.toNat + i) 1) {n}')
s = s.replace('[z, ptr, 32, 32]', f'[z, ptr, {n}, {n}]').replace('z ptr 32 32', f'z ptr {n} {n}')
s = s.replace('if i = 2 then 32 else if i = 3 then 32', f'if i = 2 then {n} else if i = 3 then {n}')
s = s.replace('32 ≤ (32 : BitVec 64).toNat', f'{n} ≤ ({n} : BitVec 64).toNat').replace('z ptr 32 32 ret', f'z ptr {n} {n} ret')
s = s.replace('z ptr len cap ptr ptr', 'z ptr len cap')
s = s.replace('\n  nonvacuous : ∃ ', '\n  nonvacuous : ∃ ')
s = s.replace('(SetBytes32(in []byte)', f'(SetBytes{n}(in []byte)')
s = s.replace('SetBytes32(in []byte)', f'SetBytes{n}(in []byte)').replace('first 32 bytes', f'first {n} bytes').replace('the 32 bytes at `ptr`', f'the {n} bytes at `ptr`')
s = s.replace('`len ≥ 32`', f'`len ≥ {n}`').replace('`len < 32`', f'`len < {n}`')
# value of z: remaining limbs zero; unify: val256 = fromBE
if mode == 'probe':
    i = s.index("    refine ⟨?_, ?_⟩\n    · rw [Util.be32_rev]")
    j = s.index("  · janus_run")
    s = s[:i] + "    refine ⟨?_, ?_⟩\n    · trace_state; sorry\n    · simp (disch := omega) only [Util.ow2_wl_iff, Util.ow2_wr_iff, Util.ow2_self_iff]\n" + s[j:]
    k = s.index("\nnamespace Witness")
    s = s[:k] + "\nend Fv256.Arm64.SetBytes%d\n" % n
open((ROOT+f'/lean/Fv256/Arm64/SetBytes{n}.lean'), 'w').write(s)
