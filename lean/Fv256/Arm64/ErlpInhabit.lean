import Fv256.InhabBase
import Fv256.RlpSpec

/-!
# `EncodeRLP` (arm64): the `Write` call-site contract is inhabited (U-ICALL-INHABITED)

`ICallContract … 4 stack 96 rt (fun _ => []) R P` of `Fv256.Arm64.EncodeRLP.correctness` has the author-chosen call-site property
`P = fun sc => X0 = w ∧ StrOut mem X1 X2 (rlpBytes (rlpVal mem z)) ∧ X3 = X2`. This lemma exhibits a call state satisfying the
call precondition (`CallOK`, the frame window, `Outside`) and `P`: the contract is not vacuous.
-/

open Janus Janus.Arm64 Janus.Contracts Janus.Contracts.ICall Fv256.Rlp Fv256.Inhab

namespace Fv256.Arm64.EncodeRLP

theorem erlp_pre_inhabited : ∃ (z w : BitVec 64) (stack : Nat) (rt : List (Nat × Nat)) (s : State),
    ICallPre 4 stack 96 rt
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 3).toNat = (sc.regs 2).toNat) s := by
  have h0 : rlpBytes (rlpVal (strMem [0x80] 0x2000) (0 : BitVec 64).toNat) = [0x80] := by
    simp [rlpVal, rlpBytes]
  refine ⟨0, 0, 4104, [], callSt 0 0x2000 1 1 0 (strMem [0x80] 0x2000),
    callSt_pre (by rfl) (by omega) (by omega) (by omega) (by omega) ?_⟩
  refine ⟨rfl, ?_, rfl⟩
  simp only [callSt]
  rw [h0]
  exact strOut_strMem [0x80] (by simp) 0x2000 (by simp)

end Fv256.Arm64.EncodeRLP
