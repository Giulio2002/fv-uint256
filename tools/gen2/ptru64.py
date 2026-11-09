#!/usr/bin/env python3 -I
# ptru64.py isa Fn kind   -- kind in lt gt cmp : methods taking (z *Int, n uint64)
import os
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))) if '/gen2/' in os.path.abspath(__file__) else os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
import sys
isa, fn, kind = sys.argv[1:4]
D = isa[0].upper() + isa[1:]
arm = isa == 'arm64'
desc = {'lt': ('bool', 'Fv256.Spec.lt', 'the `bool` result is `Fv256.Spec.lt` of the number at the receiver and `n`'),
        'gt': ('bool', 'Fv256.Spec.gt', 'the `bool` result is `Fv256.Spec.gt` of the number at the receiver and `n`'),
        'cmp': ('int', 'Fv256.Spec.cmp', 'the `int` result (read as signed 64-bit) is `Fv256.Spec.cmp` of the number at the receiver and `n`')}[kind]
Z = 'val256 s.mem z.toNat' if arm else 'valueAt s z 32'
if kind == 'cmp':
    post = f"s'.regs 0 = BitVec.ofInt 64 (Spec.cmp ({Z}) n.toNat)"
    ret0 = "s'.regs 0 = 0#64" if False else None
else:
    post = f"(s'.regs 0).toNat % 256 = (Spec.{kind} ({Z}) n.toNat).toNat"
limbs = ''.join(f"(try have := Util.readLE8_lt s.mem (z.toNat{o})); " for o in ('', ' + 8', ' + 16', ' + 24'))
spec = {'lt': 'Spec.lt', 'gt': 'Spec.gt', 'cmp': ''}[kind]
if arm:
    pre = "Ptr32 s.mem z false"
    intro = "  intro ret hret s hs ⟨hz, hz'⟩\n  janus_intro hs\n  janus_run\n"
    opens = "open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec"
    regs = "if i = 0 then z else if i = 1 then n else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0"
    s0 = f"""def s0 : State :=
  {{ regs := fun i => {regs},
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }}

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl⟩

theorem hpre : Ptr32 s0.mem z false := ⟨by decide, by decide⟩
"""
    reach = "ABIReturn s0 s'"
else:
    pre = "StackWritable s 0 8 ∧ Buffer s z 32 false"
    intro = "  intro ret hret s hs ⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩⟩\n  janus64_intro hs\n  simp only [regSP, Nat.sub_zero, Nat.zero_add] at hacc hnw\n  simp only [valueAt]\n  janus64_run [Util.readLE_32]\n"
    opens = "open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic"
    s0 = """def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 3 then n else if i = 4 then BitVec.ofNat 64 wsp else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0, mem := wmem64 }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s0 :=
  ⟨rfl, by decide, rfl, by decide, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl, rfl⟩

theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 false :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩⟩
"""
    reach = "ABIReturn s0 s'"
ret_stmt = "(s'.regs 0).toNat % 256 = 0" if kind != 'cmp' else "s'.regs 0 = 0#64"
common = "(try simp only [Nat.or_eq_zero_iff, BitVec.toNat_or, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *)"
if kind == 'cmp':
    unf = "simp only [Util.cmp_ofInt]"
else:
    unf = f"simp only [{spec}]"
if arm:
    tac = f"all_goals ({limbs}(try simp only [janus_post] at *); (try simp only [Nat.or_eq_zero_iff] at *); simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *; {unf}; dec_facts; (repeat' split) <;> (try simp only [BitVec.reduceEq, BitVec.reduceNe, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]) <;> first | omega | rfl)"
else:
    tac = f"all_goals ({limbs}{common}; {unf}; (try simp only [BitVec.toNat_setWidth, Nat.zero_or, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceOr, not_true_eq_false] at *); dec_facts; (repeat' split) <;> (try simp only [BitVec.reduceEq, BitVec.reduceNe, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.false_eq_true, Bool.true_eq_false, Nat.reduceOr, not_true_eq_false] at *) <;> first | omega | rfl)"
reg = 'X0' if arm else 'RAX'
rets = "s'.regs 0 = 0#64" if kind == 'cmp' else "(s'.regs 0).toNat % 256 = 0"
out = f"""import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util

/-!
# `(*uint256.Int).{fn}(n uint64) {desc[0]}` ({isa})

**Guarantee.** For every pointer `z` (the receiver, `{'X0' if arm else 'RAX'}`) and every `n` (`{'X1' if arm else 'RBX'}`) such that {'the 32 bytes at `z` are readable (below `2^48`)' if arm else 'the return-address slot is writable and the 32 bytes at `z` are readable (below `2^48`)'}, the call returns (no fault, no panic), obeys the ABI, and {desc[2]} (`{reg}`).

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the precondition; `Witness.returns`: it returns the value for `z = 0`, `n = 0`.
-/

{opens}

namespace Fv256.{D}.{fn}

{'set_option maxHeartbeats 8000000 in' if not arm else ''}
theorem correctness (z n : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, n]
      (fun s => {pre})
      (fun s s' => {post}) := by
{intro}  {tac}

namespace Witness

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def n : BitVec 64 := 0#64

{s0}
theorem nonvacuous : ∃ (ret : Nat) (s : State) (z n : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, n] s ∧
    ({pre}) :=
  ⟨ret, s0, z, n, hret, setup, hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ {rets} := by
  refine (correctness z n ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  rw [h.2]
  {'simp only [valueAt]' if not arm else 'try simp only [val256]'}
  decide

end Witness

end Fv256.{D}.{fn}
"""
open((ROOT+f'/lean/Fv256/{D}/{fn}.lean'),'w').write(out)
