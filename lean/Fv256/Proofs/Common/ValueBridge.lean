import Janus
import Fv256.Spec.E
import Fv256.Spec.RlpSpec
import Fv256.Spec.Core
import Fv256.Spec.Value
import Fv256.Spec.EncodeRLP
import Fv256.Proofs.Common.BytesBridge

/-!
# Bridge: the readable `Value` / `EncodeRLP` specifications (`Spec/Value.lean`, `Spec/EncodeRLP.lean`) versus the older shared definitions
the proofs use (`Fv256.E.decBytes`, `Fv256.E.decLen`, `Fv256.Rlp.rlpBytes`, `Fv256.Rlp.rlpVal`)
-/

namespace Fv256.Proofs.Value

/-- The readable decimal string is the older `decBytes` of the proofs. -/
theorem value_eq (n : Nat) : Fv256.Spec.value n = Fv256.E.decBytes n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [Fv256.Spec.value, Fv256.E.decBytes]
    split
    · rfl
    · rename_i h
      rw [ih (n / 10) (by omega)]

theorem decLen_eq (n : Nat) : Fv256.E.decLen n = (Fv256.Spec.value n).length := by
  rw [Fv256.E.decLen, value_eq]

end Fv256.Proofs.Value

namespace Fv256.Proofs.Rlp

open Fv256.Spec

/-- The readable RLP encoding is the older `rlpBytes`. -/
theorem encodeRLP_eq (v : Nat) : encodeRLP v = Fv256.Rlp.rlpBytes v := by
  unfold encodeRLP Fv256.Rlp.rlpBytes rlpLen beBytes
  by_cases h0 : v = 0
  · simp [h0]
  · have hb : Fv256.Spec.bitLen v = v.log2 + 1 := by simp [Fv256.Spec.bitLen, h0]
    by_cases h7 : v < 128
    · have : v.log2 + 1 ≤ 7 := by
        have : v.log2 < 7 := (Nat.log2_lt h0).2 (by simpa using h7)
        omega
      simp [h0, h7, hb, this]
    · have : ¬ (v.log2 + 1 ≤ 7) := by
        have : 7 ≤ v.log2 := (Nat.le_log2 h0).2 (by omega)
        omega
      simp only [h0, h7, hb, this, if_false]
      have e : (v.log2 + 1 + 7) / 8 = v.log2 / 8 + 1 := by omega
      rw [e]

/-- A nil receiver encodes as zero, otherwise the 32-byte number at the pointer. -/
theorem rlpBytes_rlpVal (m : Janus.Arm64.Memory) (z : Nat) :
    Fv256.Rlp.rlpBytes (Fv256.Rlp.rlpVal m z) = encodeRLP (if z = 0 then 0 else m.readLE z 32) := by
  rw [encodeRLP_eq]; rfl

end Fv256.Proofs.Rlp
