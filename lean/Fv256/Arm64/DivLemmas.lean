import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB
import Fv256.SpecB2
import Fv256.UtilB2

open Janus.Arm64

namespace Fv256.Arm64.DivLemmas

/-- Four consecutive zero word stores zero the four words. -/
theorem wv_zero4w (m : Memory) (a b c d : Nat) (hb : b = a + 8) (hc : c = a + 16) (hd : d = a + 24) :
    Fv256.B.wv ((((m.writeLE a 8 0).writeLE b 8 0).writeLE c 8 0).writeLE d 8 0) a 4 = 0 := by
  subst hb hc hd
  simp only [Fv256.B.wv]
  simp (disch := omega) only [Memory.readLE_writeLE_of_disjoint, Memory.readLE_writeLE_self, Nat.add_assoc, Nat.reduceAdd, Nat.mul_zero, Nat.add_zero]

end Fv256.Arm64.DivLemmas
