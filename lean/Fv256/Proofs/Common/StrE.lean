import Janus
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE

namespace Fv256.E

open Janus.Spec in
/-- The string of `decLen z` bytes ending at `p + n` whose digit at distance `k` from the end is `z / 10^k % 10` is `decBytes z`. -/
theorem strBytes_dec (m : Janus.Arm64.Memory) (p z : Nat)
    (h : ∀ k, k < decLen z → m.readLE (p + decLen z - 1 - k) 1 = 48 + z / 10 ^ k % 10) :
    strBytes m p (decLen z) = decBytes z := by
  apply List.ext_getElem
  · simp [strBytes, decLen]
  · intro i h1 h2
    have hi : i < decLen z := by simpa [strBytes] using h1
    have e := decBytes_getD_rev z (decLen z - 1 - i) (by omega)
    rw [show decLen z - 1 - (decLen z - 1 - i) = i by omega] at e
    simp only [strBytes, List.getElem_map, List.getElem_range]
    have := h (decLen z - 1 - i) (by omega)
    rw [show p + decLen z - 1 - (decLen z - 1 - i) = p + i by omega, Janus.Arm64.Memory.readLE_one] at this
    have e3 : ∀ hh : i < (decBytes z).length, (decBytes z)[i]'hh = 48 + z / 10 ^ (decLen z - 1 - i) % 10 := fun hh => by
      have := e
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hh] at this
      simpa using this
    rw [e3]; omega

end Fv256.E
