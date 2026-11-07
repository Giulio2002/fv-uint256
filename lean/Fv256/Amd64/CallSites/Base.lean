import Fv256.InhabBase

/-!
# Call-site states (U-WITNESS-CALLSITE), amd64: shared construction

`callSt64At rip r0 r1 r3 r6 r7 m` is `Fv256.Inhab.callSt64` at the code address `rip`; `callSt64At_pre` is
`Fv256.Inhab.callSt64_pre` for an arbitrary runtime-range list `rt` (the call frame `[2^40, 2^40 + above)` is outside `rt`).
-/

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.ICall Fv256.Inhab

namespace Fv256.Inhab

/-- `callSt64` at the code address `rip` -/
def callSt64At (rip r0 r1 r3 r6 r7 : BitVec 64) (m : Janus.Arm64.Memory) : Janus.Amd64.State :=
  { callSt64 r0 r1 r3 r6 r7 m with rip := rip }

@[simp] theorem callSt64At_rip (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).rip = rip := rfl
@[simp] theorem callSt64At_r0 (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).regs 0 = a := by simp [callSt64At]
@[simp] theorem callSt64At_r1 (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).regs 1 = b := by simp [callSt64At]
@[simp] theorem callSt64At_r3 (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).regs 3 = c := by simp [callSt64At]
@[simp] theorem callSt64At_r6 (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).regs 6 = d := by simp [callSt64At]
@[simp] theorem callSt64At_r7 (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).regs 7 = e := by simp [callSt64At]
@[simp] theorem callSt64At_r4 (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).regs 4 = BitVec.ofNat 64 (2 ^ 40) := by simp [callSt64At]
@[simp] theorem callSt64At_mem (rip a b c d e : BitVec 64) (m : Janus.Arm64.Memory) : (callSt64At rip a b c d e m).mem = m := rfl

theorem callSt64At_pre {rip r0 r1 r3 r6 r7 : BitVec 64} {m : Janus.Arm64.Memory} (hm : m.regions = [⟨0, 2 ^ 48, true⟩])
    (hret : m.readLE (2 ^ 40) 8 < 2 ^ 47) {nargs stack above : Nat} {rt : List (Nat × Nat)}
    (hs : stack ≤ 2 ^ 40) (hn : nargs ≤ 64) (hab : 8 + 8 * nargs ≤ above) (hrt : Outside (2 ^ 40) above rt)
    {P : Janus.Amd64.State → Prop} (hP : P (callSt64At rip r0 r1 r3 r6 r7 m)) :
    ICallPre64 nargs stack above rt P (callSt64At rip r0 r1 r3 r6 r7 m) := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  refine ⟨⟨?_, ?_, ?_, ?_, accessible_flat _ hm _ _ _ ?_⟩, hab, ?_, hP⟩ <;>
    simp [callSt64At, callSt64, hsp] <;> first | omega | exact hret | exact hrt | skip

end Fv256.Inhab
