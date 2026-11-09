import Extracted
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Arm64.WtsCases.Case0
import Fv256.Proofs.Arm64.WtsCases.Case1
import Fv256.Proofs.Arm64.WtsCases.Case2
import Fv256.Proofs.Arm64.WtsCases.Case3
import Fv256.Proofs.Arm64.WtsCases.Case4
import Fv256.Proofs.Arm64.WtsCases.Case5
import Fv256.Proofs.Arm64.WtsCases.Case6
import Fv256.Proofs.Arm64.WtsCases.Case7
import Fv256.Proofs.Arm64.WtsCases.Case8
import Fv256.Proofs.Arm64.WtsCases.Case9
import Fv256.Proofs.Arm64.WtsCases.Case10
import Fv256.Proofs.Arm64.WtsCases.Case11
import Fv256.Proofs.Arm64.WtsCases.Case12
import Fv256.Proofs.Arm64.WtsCases.Case13
import Fv256.Proofs.Arm64.WtsCases.Case14
import Fv256.Proofs.Arm64.WtsCases.Case15
import Fv256.Proofs.Arm64.WtsCases.Case16
import Fv256.Proofs.Arm64.WtsCases.Case17
import Fv256.Proofs.Arm64.WtsCases.Case18
import Fv256.Proofs.Arm64.WtsCases.Case19
import Fv256.Proofs.Arm64.WtsCases.Case20
import Fv256.Proofs.Arm64.WtsCases.Case21
import Fv256.Proofs.Arm64.WtsCases.Case22
import Fv256.Proofs.Arm64.WtsCases.Case23
import Fv256.Proofs.Arm64.WtsCases.Case24
import Fv256.Proofs.Arm64.WtsCases.Case25
import Fv256.Proofs.Arm64.WtsCases.Case26
import Fv256.Proofs.Arm64.WtsCases.Case27
import Fv256.Proofs.Arm64.WtsCases.Case28
import Fv256.Proofs.Arm64.WtsCases.Case29
import Fv256.Proofs.Arm64.WtsCases.Case30
import Fv256.Proofs.Arm64.WtsCases.Case31
import Fv256.Proofs.Arm64.WtsCases.CaseBig

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.WriteToSlice

/-!
# `(*uint256.Int).WriteToSlice(dest []byte)` (arm64)

**Guarantee.** For every pointer `z` (the receiver, `X0`) and slice `dest = (d, len, cap)` (`X1`-`X3`), every Go call whose
stack-growth check falls through (`GuardOK s 0`) and whose stack window `[SP-24, SP+24)` is writable and aligned
(`StackOK s 24 24`): if the 32 bytes at `z` are readable, the `len` bytes at `d` writable, `len < 2^48`, `len ≤ cap` (a valid slice), and neither `z` nor `dest`
overlaps the other or the stack window, then the call returns (no fault, no panic), obeys the ABI, with `n = min len 32` the first `n`
bytes of `dest` read as the big-endian number `Fv256.Spec.fromBE` equal to the low `8n` bits of the number at `z` (the last
`n` bytes are written, i.e. `dest[n-1-j]` is byte `j` of `z`), and no byte changes outside `dest[0..n)` and the stack window
(`Fv256.Util.OnlyWrites2`). (`len = 0` writes nothing; bytes of `dest` beyond index 31 are not touched.)

**How.** The byte loop has a constant trip count for each `n`: the proof splits on `len` (33 cases, one module each under
`Fv256.Arm64.WtsCases`), and `janus_run` unrolls the loop.

**Non-vacuity.** `Witness.nonvacuous`: a concrete call satisfies the preconditions; `Witness.returns`: it returns.
-/

set_option maxHeartbeats 64000000 in
theorem correctness_proof (z d len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, d, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧ len.toNat < 2 ^ 48 ∧
        Ptr s.mem d len.toNat true ∧ Disjoint z.toNat 32 d.toNat len.toNat ∧
        Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat len.toNat (s.sp.toNat - 24) 48 ∧
        len.toNat ≤ cap.toNat)
      (fun s s' => Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min len.toNat 32) =
          val256 s.mem z.toNat % 2 ^ (8 * min len.toNat 32) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat (min len.toNat 32) (s.sp.toNat - 24) 48) := by
  intro ret hret s hs ⟨hg, hst, hz, hl, hd, hzd, hzs, hds, hcap⟩
  by_cases h32 : 32 ≤ len.toNat
  · have := caseBig z d len cap h32 hl ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, hcap⟩
    simpa [Nat.min_eq_right h32] using this
  · have e : len = BitVec.ofNat 64 len.toNat := by simp
    rcases (show len.toNat = 0 ∨ len.toNat = 1 ∨ len.toNat = 2 ∨ len.toNat = 3 ∨ len.toNat = 4 ∨ len.toNat = 5 ∨ len.toNat = 6 ∨ len.toNat = 7 ∨ len.toNat = 8 ∨ len.toNat = 9 ∨ len.toNat = 10 ∨ len.toNat = 11 ∨ len.toNat = 12 ∨ len.toNat = 13 ∨ len.toNat = 14 ∨ len.toNat = 15 ∨ len.toNat = 16 ∨ len.toNat = 17 ∨ len.toNat = 18 ∨ len.toNat = 19 ∨ len.toNat = 20 ∨ len.toNat = 21 ∨ len.toNat = 22 ∨ len.toNat = 23 ∨ len.toNat = 24 ∨ len.toNat = 25 ∨ len.toNat = 26 ∨ len.toNat = 27 ∨ len.toNat = 28 ∨ len.toNat = 29 ∨ len.toNat = 30 ∨ len.toNat = 31 by omega) with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31
    · have e0 : len = 0#64 := by rw [e, h0]
      subst e0
      have := case0 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e1 : len = 1#64 := by rw [e, h1]
      subst e1
      have := case1 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e2 : len = 2#64 := by rw [e, h2]
      subst e2
      have := case2 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e3 : len = 3#64 := by rw [e, h3]
      subst e3
      have := case3 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e4 : len = 4#64 := by rw [e, h4]
      subst e4
      have := case4 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e5 : len = 5#64 := by rw [e, h5]
      subst e5
      have := case5 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e6 : len = 6#64 := by rw [e, h6]
      subst e6
      have := case6 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e7 : len = 7#64 := by rw [e, h7]
      subst e7
      have := case7 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e8 : len = 8#64 := by rw [e, h8]
      subst e8
      have := case8 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e9 : len = 9#64 := by rw [e, h9]
      subst e9
      have := case9 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e10 : len = 10#64 := by rw [e, h10]
      subst e10
      have := case10 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e11 : len = 11#64 := by rw [e, h11]
      subst e11
      have := case11 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e12 : len = 12#64 := by rw [e, h12]
      subst e12
      have := case12 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e13 : len = 13#64 := by rw [e, h13]
      subst e13
      have := case13 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e14 : len = 14#64 := by rw [e, h14]
      subst e14
      have := case14 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e15 : len = 15#64 := by rw [e, h15]
      subst e15
      have := case15 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e16 : len = 16#64 := by rw [e, h16]
      subst e16
      have := case16 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e17 : len = 17#64 := by rw [e, h17]
      subst e17
      have := case17 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e18 : len = 18#64 := by rw [e, h18]
      subst e18
      have := case18 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e19 : len = 19#64 := by rw [e, h19]
      subst e19
      have := case19 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e20 : len = 20#64 := by rw [e, h20]
      subst e20
      have := case20 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e21 : len = 21#64 := by rw [e, h21]
      subst e21
      have := case21 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e22 : len = 22#64 := by rw [e, h22]
      subst e22
      have := case22 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e23 : len = 23#64 := by rw [e, h23]
      subst e23
      have := case23 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e24 : len = 24#64 := by rw [e, h24]
      subst e24
      have := case24 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e25 : len = 25#64 := by rw [e, h25]
      subst e25
      have := case25 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e26 : len = 26#64 := by rw [e, h26]
      subst e26
      have := case26 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e27 : len = 27#64 := by rw [e, h27]
      subst e27
      have := case27 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e28 : len = 28#64 := by rw [e, h28]
      subst e28
      have := case28 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e29 : len = 29#64 := by rw [e, h29]
      subst e29
      have := case29 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e30 : len = 30#64 := by rw [e, h30]
      subst e30
      have := case30 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this
    · have e31 : len = 31#64 := by rw [e, h31]
      subst e31
      have := case31 z d cap ret hret s hs ⟨hg, hst, hz, hd, hzd, hzs, hds, by simpa using hcap⟩
      simpa using this

namespace Wit

open Janus.Contracts.EqHashModel Janus.Contracts.IfaceModel

def ret : Nat := wret

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

def z : BitVec 64 := BitVec.ofNat 64 DST
def d : BitVec 64 := BitVec.ofNat 64 (DST + 32)

def s0 : State :=
  { regs := fun i => if i = 0 then z else if i = 1 then d else if i = 2 then 8 else if i = 3 then 8
      else if i = 28 then BitVec.ofNat 64 wg else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 wsp, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩, mem := Janus.Contracts.EqHashModel.wmem }

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s0 :=
  ⟨rfl, rfl, by
    intro i h; simp at h
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl | rfl <;> rfl⟩

theorem hpre : GuardOK s0 0 ∧ StackOK s0 24 24 ∧ Ptr32 s0.mem z false ∧ (8 : BitVec 64).toNat < 2 ^ 48 ∧
    Ptr s0.mem d (8 : BitVec 64).toNat true ∧ Disjoint z.toNat 32 d.toNat (8 : BitVec 64).toNat ∧
    Disjoint z.toNat 32 (s0.sp.toNat - 24) 48 ∧ Disjoint d.toNat (8 : BitVec 64).toNat (s0.sp.toNat - 24) 48 ∧
    (8 : BitVec 64).toNat ≤ (8 : BitVec 64).toNat := by
  refine ⟨by unfold GuardOK; decide, by unfold StackOK; decide, ⟨by decide, by decide⟩, by decide,
    ⟨by decide, by decide⟩, ?_, ?_, ?_, by decide⟩ <;> (try unfold Disjoint) <;> decide

theorem nonvacuous : ∃ (ret : Nat) (s : State) (z d : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, d, 8, 8] s ∧
    (GuardOK s 0 ∧ StackOK s 24 24 ∧ Ptr32 s.mem z false ∧ (8 : BitVec 64).toNat < 2 ^ 48 ∧
    Ptr s.mem d (8 : BitVec 64).toNat true ∧ Disjoint z.toNat 32 d.toNat (8 : BitVec 64).toNat ∧
    Disjoint z.toNat 32 (s.sp.toNat - 24) 48 ∧ Disjoint d.toNat (8 : BitVec 64).toNat (s.sp.toNat - 24) 48 ∧
    (8 : BitVec 64).toNat ≤ (8 : BitVec 64).toNat) ∧
    Returns (Extracted.program.withExit ret) s fun s' => ABIReturn s s' ∧ Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min (8 : BitVec 64).toNat 32) =
          val256 s.mem z.toNat % 2 ^ (8 * min (8 : BitVec 64).toNat 32) ∧
        Util.OnlyWrites2 s.mem s'.mem d.toNat (min (8 : BitVec 64).toNat 32) (s.sp.toNat - 24) 48 :=
  ⟨ret, s0, z, d, hret, setup, hpre,
    correctness_proof z d (8 : BitVec 64) (8 : BitVec 64) ret hret s0 setup hpre⟩

theorem returns : Returns (Extracted.program.withExit ret) s0 (fun s' => ABIReturn s0 s' ∧
    Spec.fromBE (fun i => s'.mem.readLE (d.toNat + i) 1) (min (8 : BitVec 64).toNat 32) =
      val256 s0.mem z.toNat % 2 ^ (8 * min (8 : BitVec 64).toNat 32) ∧
    Util.OnlyWrites2 s0.mem s'.mem d.toNat (min (8 : BitVec 64).toNat 32) (s0.sp.toNat - 24) 48) :=
  correctness_proof z d 8 8 ret hret s0 setup hpre

end Wit

end Fv256.Arm64.WriteToSlice
