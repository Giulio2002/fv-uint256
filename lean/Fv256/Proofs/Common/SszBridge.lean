import Janus
import Fv256.Spec.UnmarshalSSZ
import Fv256.Proofs.Common.BytesBridge

/-!
# Bridge: little-endian decoding (`Spec.leValue`, used by `Spec.unmarshalSSZ`) versus `Memory.readLE`
-/

namespace Fv256.Proofs.Ssz

open Fv256.Spec

theorem leValue_map (m : Janus.Arm64.Memory) : ∀ (n a : Nat),
    leValue ((List.range n).map (fun i => m.readLE (a + i) 1)) = m.readLE a n
  | 0, a => by simp [leValue]
  | n + 1, a => by
    have ih := leValue_map m n (a + 1)
    have hadd : m.readLE a (n + 1) = m.readLE a 1 + 256 * m.readLE (a + 1) n := by
      rw [show n + 1 = 1 + n by omega, Janus.Arm64.Memory.readLE_add]
    have hmap : (List.map (fun i => m.readLE (a + i) 1) (List.range n.succ)) =
        m.readLE (a + 0) 1 :: List.map (fun i => m.readLE (a + 1 + i) 1) (List.range n) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one]
      congr 1
      omega
    rw [hadd, hmap, leValue, ih]
    rfl

/-- The decoded number of a 32-byte buffer in memory is its 32-byte little-endian read. -/
theorem unmarshal_iff (m : Janus.Arm64.Memory) (a v : Nat) :
    Fv256.Spec.unmarshalSSZ ((List.range 32).map (fun i => m.readLE (a + i) 1)) = some v ↔ m.readLE a 32 = v := by
  have hl : ((List.range 32).map (fun i => m.readLE (a + i) 1)).length = 32 := by simp
  rw [Fv256.Spec.unmarshalSSZ, ite_cond_eq_true _ _ (by simp [hl]), leValue_map]
  simp

/-- The form the proofs use: the number written to `z` (read from `m'`) equals the 32-byte read of the input buffer in `m`. -/
theorem unmarshal_iff' (m m' : Janus.Arm64.Memory) (a b : Nat) :
    Fv256.Spec.unmarshalSSZ ((List.range 32).map (fun i => m.readLE (a + i) 1)) = some (m'.readLE b 32) ↔
      m'.readLE b 32 = m.readLE a 32 := by
  rw [unmarshal_iff]; exact eq_comm

end Fv256.Proofs.Ssz
