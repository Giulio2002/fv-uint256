#!/usr/bin/env python3
# usage: genblk3f_a64.py [probe] < lean/Fv256/Arm64/MarshalSSZAppendG.lean > blk3f.lean
# The final arm64 block (limb 3): block-3 text, but it runs on to the return and proves `AppendPost`.
import sys, subprocess, re
probe = len(sys.argv) > 1 and sys.argv[1] == 'probe'
src = sys.stdin.read()
if 'end Fv256.Amd64.Msa' not in src:
    src = src.rstrip('\n') + '\n\nend Fv256.Amd64.Msa\n'
gen = subprocess.run([sys.executable, '/srv/fv-uint256-wC/wipC/genblk.py', '3'], input=src, capture_output=True, text=True).stdout
t = gen
t = t.replace('theorem blk3', 'theorem blk3f')
# signature: drop Q and hcont, fix the conclusion
t = t.replace('    (Q : Amd64.Outcome → Prop)\n', '', 1)
i = t.index('    (hcont :')
j = t.index(':\n    Reaches ((Extracted.program.link impl).withExit ret) S Q := by')
t = t[:i].rstrip('\n') + ' :\n    Reaches ((Extracted.program.link impl).withExit ret) S\n      (IsReturn fun s\' => ABIReturn s s\' ∧ AppendPost R s s\' z dp len0 cap0 b0 L0) := by' + t[j + len(':\n    Reaches ((Extracted.program.link impl).withExit ret) S Q := by'):]
# branch closings
lines = t.split('\n')
def find(prefix, start=0):
    for n in range(start, len(lines)):
        if lines[n].startswith(prefix):
            return n
    raise SystemExit('missing ' + prefix)
a = find('    refine hcont _ pp cc b L')
b = find('  · have hcostK', a)
c = find('    refine hcont _ r0 r2', b)
for n in range(b, c):
    if lines[n].startswith('    janus64_run [hM16, hM70] until'):
        lines[n] = '    have hret48 := hret.user\n    have hMret : M.readLE (s.regs 4).toNat 8 = ret := by\n      rw [hMr _ _ (Outside.of_sub hout (by omega) (by omega)) (by omega),\n        Memory.readLE_writeLE_of_disjoint _ _ (by omega), Memory.readLE_writeLE_of_disjoint _ _ (by omega)]\n      exact h_rd1\n    janus64_run [hM16, hM70, hMret]'
        break
end = find('end Fv256.Amd64.Msa', c)
if probe:
    tail1 = ['    have hret48 := hret.user', '    janus64_run [h_rd1]', '    trace_state', '    sorry']
    tail2 = ['    trace_state', '    sorry', '']
    out = lines[:a] + tail1 + lines[b:c] + tail2 + lines[end:]
else:
    body1 = open('/srv/fv-uint256-wC/wipC/b3fa/branch1.txt').read().rstrip('\n').split('\n')
    body2 = open('/srv/fv-uint256-wC/wipC/b3fa/branch2.txt').read().rstrip('\n').split('\n')
    out = lines[:a] + body1 + lines[b:c] + body2 + [''] + lines[end:]
sys.stdout.write('\n'.join(out))
