#!/usr/bin/env python3
# usage: genblk3f_a64.py [probe] < lean/Fv256/Arm64/MarshalSSZAppendG.lean > blk3f.lean
# The final arm64 block (limb 3): block-3 text, but it runs on to the return and proves `AppendPost`.
import sys, subprocess, re
probe = len(sys.argv) > 1 and sys.argv[1] == 'probe'
src = sys.stdin.read()
gen = subprocess.run([sys.executable, '/srv/fv-uint256-wC/wipC/genblk_a64.py', '3'], input=src, capture_output=True, text=True).stdout
t = gen
t = t.replace('theorem blk3', 'theorem blk3f')
# signature: drop Q and hcont, fix the conclusion
t = t.replace('    (Q : Outcome → Prop)\n', '', 1)
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
b = find('  · obtain ⟨hrd⟩', a)
c = find('    refine hcont _ r0 r2', b)
end = find('end Fv256.Arm64.MarshalSSZAppendG', c)
if probe:
    tail1 = ['    have hret48 := hret.user', '    have hret4 := hret.aligned', '    janus_run [hrd1]', '    trace_state', '    sorry']
    tail2 = ['    have hret48 := hret.user', '    have hret4 := hret.aligned', '    janus_run [hrd1]', '    trace_state', '    sorry', '']
    out = lines[:a] + tail1 + lines[b:c] + tail2 + lines[end:]
else:
    body1 = open('/srv/fv-uint256-wC/wipC/b3f/branch1.txt').read().rstrip('\n').split('\n')
    out = lines[:a] + body1 + lines[b:c] + ['    have hret48 := hret.user', '    have hret4 := hret.aligned', '    janus_run [hrd1]', '    sorry', ''] + lines[end:]
sys.stdout.write('\n'.join(out))
