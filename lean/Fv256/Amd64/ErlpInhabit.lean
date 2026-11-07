import Fv256.InhabBase
import Fv256.RlpSpec

/-!
# `EncodeRLP` (amd64): the `Write` call-site contract is inhabited (U-ICALL-INHABITED)

`ICallContract64 … 4 stack 56 rt (fun _ => []) R P` of `Fv256.Amd64.EncodeRLP.correctness` has the author-chosen call-site property
`P = fun sc => RAX = w ∧ StrOut mem RDI RBX (rlpBytes (rlpVal mem z)) ∧ RSI... = RBX`. This lemma exhibits a call state satisfying
the call precondition (`CallOK64`, the frame window, `Outside`) and `P`: the contract is not vacuous.
-/

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.ICall Fv256.Rlp Fv256.Inhab

namespace Fv256.Amd64.EncodeRLP

theorem erlp_pre_inhabited : ∃ (z w : BitVec 64) (stack : Nat) (rt : List (Nat × Nat)) (s : State),
    ICallPre64 4 stack 56 rt
      (fun sc => sc.regs 0 = w ∧
        StrOut sc.mem (sc.regs 3).toNat (sc.regs 1).toNat (rlpBytes (rlpVal sc.mem z.toNat)) ∧
        (sc.regs 7).toNat = (sc.regs 1).toNat) s := by
  have h0 : rlpBytes (rlpVal (strMem [0x80] 0x2000) (0 : BitVec 64).toNat) = [0x80] := by
    simp [rlpVal, rlpBytes]
  have hret : (strMem [0x80] 0x2000).readLE (2 ^ 40) 8 < 2 ^ 47 := by
    rw [readLE_strMem_far _ _ _ _ (by simp)]; omega
  refine ⟨0, 0, 4104, [], callSt64 0 1 0x2000 0 1 (strMem [0x80] 0x2000),
    callSt64_pre (by rfl) hret (by omega) (by omega) (by omega) ?_⟩
  refine ⟨rfl, ?_, rfl⟩
  simp only [callSt64]
  rw [h0]
  exact strOut_strMem [0x80] (by simp) 0x2000 (by simp)

end Fv256.Amd64.EncodeRLP
