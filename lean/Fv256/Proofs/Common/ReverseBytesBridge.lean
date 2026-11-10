import Janus
import Fv256.Spec.Core
import Fv256.Proofs.Legacy.FromBE
import Fv256.Spec.ReverseBytes

/-!
# Bridge: the implementation-shaped `ReverseBytes` result equals the readable `Spec.reverseBytes`

The compiled-code proofs state the result as `Spec.fromBE (fun i => mem.readLE (x + i) 1) 32` (the big-endian reading of the
32 bytes at `x` as they sit in memory). The readable specification `Fv256.Spec.reverseBytes` talks about the NUMBER at `x`. This module
proves them equal; the claim files use it to restate the result.
-/

namespace Fv256.ReverseBytesBridge

open Janus.Arm64

/-- Byte `i` of the little-endian number of `n` bytes at `a` is the byte at `a + i`. -/
theorem byte_eq (m : Memory) : ∀ (i n a : Nat), i < n → m.readLE (a + i) 1 = m.readLE a n / 256 ^ i % 256
  | 0, n + 1, a, _ => by
    have hb : (m.bytes a).toNat < 256 := (m.bytes a).isLt
    simp only [Nat.add_zero, Memory.readLE_succ, Memory.readLE_zero, Nat.pow_zero, Nat.div_one]
    omega
  | i + 1, n + 1, a, h => by
    have hb : (m.bytes a).toNat < 256 := (m.bytes a).isLt
    have ih := byte_eq m i n (a + 1) (by omega)
    have e : a + (i + 1) = a + 1 + i := by omega
    have h2 : (m.bytes a).toNat + 256 * m.readLE (a + 1) n = 256 * m.readLE (a + 1) n + (m.bytes a).toNat := by omega
    have h3 : ((m.bytes a).toNat + 256 * m.readLE (a + 1) n) / 256 ^ (i + 1) = m.readLE (a + 1) n / 256 ^ i := by
      rw [Nat.pow_succ', ← Nat.div_div_eq_div_mul]
      congr 1
      omega
    rw [e, ih, Memory.readLE_succ, h3]

/-- The big-endian reading of the first `n` of the bytes at `a` (inside an `N`-byte number) is `reverseLow` of that number. -/
theorem fromBE_eq (m : Memory) : ∀ (n N a : Nat), n ≤ N →
    Fv256.Spec.fromBE (fun i => m.readLE (a + i) 1) n = Fv256.Spec.reverseLow (m.readLE a N) n
  | 0, _, _, _ => rfl
  | n + 1, N + 1, a, h => by
    have hb : (m.bytes a).toNat < 256 := (m.bytes a).isLt
    have ih := fromBE_eq m n N (a + 1) (by omega)
    have hf : (fun i => m.readLE (a + (i + 1)) 1) = (fun i => m.readLE (a + 1 + i) 1) := by
      funext i; congr 1; omega
    have hV : m.readLE a (N + 1) = (m.bytes a).toNat + 256 * m.readLE (a + 1) N := Memory.readLE_succ m a N
    have h1 : m.readLE a (N + 1) % 256 = (m.bytes a).toNat := by omega
    have h2 : m.readLE a (N + 1) / 256 = m.readLE (a + 1) N := by omega
    rw [Fv256.Spec.reverseLow, h1, h2, ← ih, ← hf]
    show m.readLE (a + 0) 1 * 256 ^ n + _ = _
    rw [Nat.add_zero, Memory.readLE_one]
  | _ + 1, 0, _, h => by omega

/-- THE BRIDGE: the big-endian reading of the 32 bytes at `a` is `Spec.reverseBytes` of the 256-bit number at `a`. -/
theorem fromBE_32 (m : Memory) (a : Nat) :
    Fv256.Spec.fromBE (fun i => m.readLE (a + i) 1) 32 = Fv256.Spec.reverseBytes (m.readLE a 32) :=
  fromBE_eq m 32 32 a (Nat.le_refl _)

end Fv256.ReverseBytesBridge
