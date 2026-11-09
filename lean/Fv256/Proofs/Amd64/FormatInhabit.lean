import Fv256.Proofs.Common.InhabBase
import Fv256.Proofs.Common.SpecFormat
import Fv256.Proofs.Common.FormatFastDefs
import Fv256.Proofs.Common.IntoBigCommon

/-!
# `Format` (amd64): the call-site contracts with an author-chosen property are inhabited (U-ICALL-INHABITED)

`Fv256.Amd64.Format.correctness` has three `ICallContract64` hypotheses whose call-site property `P` is not `fun _ => True`:
the `Write` call (`FastWP`), `fmt.Fprint(w, "<nil>")` (`FpArg`, restated here as `FpArgG` over the three data addresses; the
`FormatInhabitNil` module instantiates it at the extraction's addresses) and `(*big.Int).Format` (the `BigObj` receiver).
Each lemma gives a concrete call state meeting the call precondition (`CallOK64`, `Outside`) and `P`.
-/

open Janus Janus.Amd64 Janus.Contracts Janus.Contracts.ICall Fv256.Inhab Fv256.FormatFast

namespace Fv256.Amd64.FormatInhabit

/-- the `Write` call: the slice holds the fast-path bytes -/
theorem wr_pre_inhabited : ∃ (stack : Nat) (rt : List (Nat × Nat)) (data : BitVec 64) (zv : Nat) (ch : BitVec 64) (s : State),
    ICallPre64 4 stack 80 rt (FastWP data (Fv256.FormatSpec.fastBytes zv (ch.toNat % 2 ^ 32))) s := by
  have hb : Fv256.FormatSpec.fastBytes 0 ((100 : BitVec 64).toNat % 2 ^ 32) = [48] := by
    simp [Fv256.FormatSpec.fastBytes, Fv256.E.decBytes]
  have hret : (strMem [48] 0x2000).readLE (2 ^ 40) 8 < 2 ^ 47 := by
    rw [readLE_strMem_far _ _ _ _ (by simp)]; omega
  refine ⟨4608, [], 0, 0, 100, callSt64 0 1 0x2000 0 1 (strMem [48] 0x2000),
    callSt64_pre (by rfl) hret (by omega) (by omega) (by omega) ?_⟩
  refine ⟨rfl, ?_, by simp⟩
  simp only [callSt64_r1, callSt64_r3, callSt64_mem]
  rw [hb]
  exact strOut_strMem [48] (by simp) 0x2000 (by simp)

/-- the property of `fmt.Fprint(w, "<nil>")` over the type descriptor `ty`, the string header `hdr` and the bytes `lit` -/
def FpArgG (ty hdr lit : Nat) (data : BitVec 64) (sc : State) : Prop :=
  sc.regs 3 = data ∧ sc.regs 7 = 1#64 ∧ sc.regs 6 = 1#64 ∧ (sc.regs 1).toNat = (sc.regs 4).toNat + 56 ∧
  sc.mem.readLE (sc.regs 1).toNat 8 = ty ∧ sc.mem.readLE ((sc.regs 1).toNat + 8) 8 = hdr ∧
  sc.mem.readLE hdr 8 = lit ∧ sc.mem.readLE (hdr + 8) 8 = 5 ∧ StrOut sc.mem lit 5 Fv256.FormatSpec.nilText

theorem fp_pre_inhabited_gen (ty hdr lit : Nat) (h1 : ty < 2 ^ 64) (h2 : hdr < 2 ^ 64) (h3 : lit < 2 ^ 64)
    (hd1 : lit + 5 ≤ 2 ^ 40) (hd2 : hdr + 16 ≤ 2 ^ 40) (hd3 : lit + 5 ≤ hdr ∨ hdr + 16 ≤ lit) :
    ∃ (stack : Nat) (rt : List (Nat × Nat)) (data : BitVec 64) (s : State),
      ICallPre64 5 stack 80 rt (FpArgG ty hdr lit data) s := by
  have hsp : (BitVec.ofNat 64 (2 ^ 40 + 56)).toNat = 2 ^ 40 + 56 := by simp
  have hsp' : (BitVec.ofNat 64 (2 ^ 40)).toNat = 2 ^ 40 := by decide
  let m : Janus.Arm64.Memory := ((((strMem Fv256.FormatSpec.nilText lit).writeLE (2 ^ 40 + 56) 8 ty).writeLE (2 ^ 40 + 64) 8 hdr).writeLE
    hdr 8 lit).writeLE (hdr + 8) 8 5
  have hm : m.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m, strMem]
  have hret : m.readLE (2 ^ 40) 8 < 2 ^ 47 := by
    simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint]
    rw [readLE_strMem_far _ _ _ _ (by simp [Fv256.FormatSpec.nilText]; omega)]; omega
  refine ⟨4608, [], 0, callSt64 0 (BitVec.ofNat 64 (2 ^ 40 + 56)) 0 1 1 m,
    callSt64_pre hm hret (by omega) (by omega) (by omega) ?_⟩
  simp only [FpArgG, callSt64_r1, callSt64_r3, callSt64_r4, callSt64_r6, callSt64_r7, callSt64_mem, hsp, hsp']
  refine ⟨trivial, rfl, rfl, trivial, ?_, ?_, ?_, ?_, ?_⟩
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h1)
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h2)
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
    exact Nat.mod_eq_of_lt (by simpa using h3)
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_self]
  · have := strOut_strMem Fv256.FormatSpec.nilText (by simp [Fv256.FormatSpec.nilText]) lit (by simp [Fv256.FormatSpec.nilText]; omega)
    simp only [m]
    refine strOut_writeLE (strOut_writeLE (strOut_writeLE (strOut_writeLE this _ _ _ ?_) _ _ _ ?_) _ _ _ ?_) _ _ _ ?_ <;>
      simp [Fv256.FormatSpec.nilText] <;> omega

/-- `(*big.Int).Format`: the receiver `P` holds `zv` (here `0`: `len = 0`, `cap = 4`) -/
theorem bf_pre_inhabited : ∃ (stack : Nat) (rt : List (Nat × Nat)) (zv : Nat) (tab data ch : BitVec 64) (s : State),
    ICallPre64 4 stack 80 rt (fun sc => ∃ P : BitVec 64, sc.regs 0 = P ∧ Fv256.IntoBig.BigObj sc.mem P.toNat zv ∧
      sc.regs 3 = tab ∧ sc.regs 1 = data ∧ (sc.regs 7).toNat % 2 ^ 32 = ch.toNat % 2 ^ 32) s := by
  let m : Janus.Arm64.Memory := flatMem.writeLE (0x2000 + 24) 8 4
  have hm : m.regions = [⟨0, 2 ^ 48, true⟩] := by simp [m, flatMem]
  have hret : m.readLE (2 ^ 40) 8 < 2 ^ 47 := by
    simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]; omega
  refine ⟨4608, [], 0, 0, 0, 0, callSt64 0x2000 0 0 0 0 m, callSt64_pre hm hret (by omega) (by omega) (by omega) ?_⟩
  refine ⟨0x2000, by simp, ?_, by simp, by simp, by simp⟩
  simp only [callSt64_mem]
  have h2k : (0x2000 : BitVec 64).toNat = 0x2000 := by decide
  rw [h2k]
  refine ⟨0, 0, 4, ?_, by omega, ?_, ?_, ?_, ?_, by omega, ?_, by omega, by omega, Or.inl rfl, rfl⟩
  · simp [m]; exact accessible_flat flatMem rfl _ _ _ (by omega)
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_of_disjoint, readLE_flatMem]
  · simp (disch := omega) only [m, Janus.Arm64.Memory.readLE_writeLE_self]
  · simp [m]; exact accessible_flat flatMem rfl _ _ _ (by omega)

end Fv256.Amd64.FormatInhabit
