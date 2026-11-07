#!/usr/bin/env python3
"""cs-newobject.py FILE... : add the U-WITNESS-CALLSITE conjunct for the single NewobjectContract64 hypothesis of the simple
newobject-witness files (Bytes Clone NewInt FromBig FromHex MustFromBig MustFromHex). Idempotent."""
import re, sys
for f in sys.argv[1:]:
    s = open(f).read()
    if 'csNew_pre' in s: print('skip', f); continue
    m = re.search(r'theorem hH : H \[intType\] \(s0\.regs 14\)\.toNat \(\(s0\.regs 4\)\.toNat - (\d+)\)', s)
    k = m.group(1)
    i = s.index('theorem nonvacuous')
    # walk up over a doc comment
    j = i
    pre = s[:i].rstrip('\n')
    if pre.endswith('-/'):
        j = pre.rindex('/--') if '/--' in pre else i
    defs = "open Fv256.CallSites\n\n" + f'''/-- The call state of `runtime.newobject` (U-WITNESS-CALLSITE): `s0`'s memory, at the allocator's entry, `RSP` at the call
frame (`s0`'s `RSP` less {k}), `RAX` the type descriptor. -/
def csNew : Amd64.State :=
  {{ s0 with rip := BitVec.ofNat 64 cA, regs := fun i => if i = 0 then BitVec.ofNat 64 tyA else if i = 4 then s0.regs 4 - {k}#64 else s0.regs i }}

theorem csNew_rip : csNew.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") := by rw [addr]; rfl

set_option maxRecDepth 100000 in
theorem csNew_pre : NewobjectSite H rt 4096 csNew := by
  have ht : (csNew.regs 0).toNat = intType := by
    have : intType = tyA := by unfold tyA; decide
    rw [this]; decide
  refine ⟨⟨by decide, by decide, by decide⟩, ?_⟩
  show H [(csNew.regs 0).toNat] _ _ (rtView rt s0.mem)
  rw [ht]; exact hH

'''
    s = s[:j] + defs + s[j:]
    i = s.index('theorem nonvacuous')
    a = s.index('(Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧\n', i)
    e = a + len('(Extracted.program.contractAddr "runtime.newobject") rt 4096 H ∧\n')
    s = s[:e] + '    (∃ s_c : Amd64.State, s_c.rip = BitVec.ofNat 64 (Extracted.program.contractAddr "runtime.newobject") ∧\n      NewobjectSite H rt 4096 s_c) ∧\n' + s[e:]
    b = s.index('hnew, hret', e)
    s = s[:b] + 'hnew, ⟨csNew, csNew_rip, csNew_pre⟩, hret' + s[b+len('hnew, hret'):]
    open(f, 'w').write(s); print('ok', f, k)
