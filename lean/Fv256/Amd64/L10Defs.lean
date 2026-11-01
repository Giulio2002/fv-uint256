import Fv256.Util
import Janus

open Janus.Arm64

namespace Fv256.Amd64.Log10

/-- The Go global `pows64` (`[20]uint64`, powers of ten) at its address in the amd64 binary: readable and holding `10^i`. -/
def Tabs64 (m : Memory) : Prop :=
  m.accessible 5967168 160 false = true ∧ ∀ i, i < 20 → m.readLE (5967168 + 8 * i) 8 = 10 ^ i

/-- The Go global `pows` (`[60]Int`, `10^(20+i)` as four little-endian limbs; only `i < 58`, i.e. up to `10^77 < 2^256`, is claimed and ever read: the last two Go entries overflow 256 bits). -/
def TabsBig (m : Memory) : Prop :=
  m.accessible 5971840 1920 false = true ∧ ∀ i, i < 58 → m.readLE (5971840 + 32 * i) 32 = 10 ^ (20 + i)

end Fv256.Amd64.Log10
