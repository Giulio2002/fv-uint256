#!/usr/bin/env python3
# usage: gen_growth_witness.py arm64|amd64  -> prints the main file with an extra `Witness2` namespace (growth path)
# Witness2: MarshalSSZAppend(z, dp, len = 32, cap = 32): block 0 needs length 40 > cap 32, so exactly one
# growslice(p, 40, 32, 8, uint8) request is made (new cap 64 = 32 + 32, so the other three appends fit).
import sys, re
isa = sys.argv[1]
path = '/srv/fv-uint256-wC/lean/Fv256/%s/MarshalSSZAppendMain.lean' % ('Arm64' if isa == 'arm64' else 'Amd64')
t = open(path).read()
i = t.index('namespace Witness')
j = t.index('end Witness') + len('end Witness')
w = t[i:j]
w2 = w.replace('namespace Witness', 'namespace Witness2', 1).replace('end Witness', 'end Witness2', 1)
# the single request the runtime serves
w2 = w2.replace('def ok : Nat → List Nat → Prop := fun _ _ => False',
                'def ok : Nat → List Nat → Prop := fun a args => a = grA ∧ ∃ p, args = [p, 40, 32, 8, u8A]')
w2 = w2.replace('theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 1, 0, 1, (u8A, 1, 0).1] := fun _ h => h.elim',
                'theorem hok_gr : ∀ args, ok grA args → ∃ p, args = [p, 40, 32, 8, (u8A, 1, 0).1] := fun _ h => h.2')
w2 = re.sub(r'janus6?4?_?live_growslice \(u8A, 1, 0\) 1 0 1 16 8 hok_gr',
            lambda m: m.group(0).replace('1 0 1 16 8', '40 32 8 64 64'), w2)
# initial state: len = cap = 32
if isa == 'arm64':
    w2 = w2.replace('if i = 3 then 32 else if i = 28', 'if i = 2 then 32 else if i = 3 then 32 else if i = 28')
else:
    w2 = w2.replace('else if i = 7 then 32 else if i = 4', 'else if i = 1 then 32 else if i = 7 then 32 else if i = 4')
w2 = w2.replace('[zV, dpV, 0, 32]', '[zV, dpV, 32, 32]')
# precondition instance: len 32
w2 = w2.replace('(0 : BitVec 64)', '(32 : BitVec 64)')
w2 = w2.replace('fun _ => ⟨by decide, Or.inr ?_⟩,\n    fun h => absurd h (by decide), by decide, ?_⟩',
                'fun h => absurd h (by decide),\n    fun _ _ => by decide, by decide, ?_⟩')
# drop the now-unused Outside dp goal (room clause is vacuous)
w2 = w2.replace("  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide\n  · simp [Fv256.Msa.Ready]",
                "  · have hgc : growCap 1 true 40 32 = 64 := by decide\n    simp [Fv256.Msa.Ready, hgc, ok, grA, ut_eq]") if isa == 'arm64' else w2.replace(
                "  · rw [rt_eq]; simp only [outside_cons, outside_append, outside_nil, and_true]; decide\n  · simp [Fv256.Amd64.Msa.Ready]",
                "  · have hgc : growCap 1 true 40 32 = 64 := by decide\n    simp [Fv256.Amd64.Msa.Ready, hgc, ok, grA, ut_eq]")
w2 = w2.replace('[growsliceSeg grA 0 16 8]', '[growsliceSeg grA 32 64 64]')
w2 = w2.replace('[], zV, dpV, 0, 32,', '[], zV, dpV, 32, 32,')
w2 = w2.replace('`MarshalSSZAppend(z, dp, 0, 32)`', '`MarshalSSZAppend(z, dp, 32, 32)` (one growslice request)')
w2 = w2.replace('theorem nonvacuous', 'theorem nonvacuous_grow')
sys.stdout.write(t[:j] + '\n\n' + w2 + t[j:])
