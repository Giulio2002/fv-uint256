import Fv256.Util
import Janus

open Janus.Arm64

namespace Fv256.Arm64.Log10

/-- The Go global `pows64` (`[20]uint64`, powers of ten) at its address in the binary: readable and holding `10^i`. -/
def Tabs64 (m : Memory) : Prop :=
  m.accessible 1772992 160 false = true ∧ ∀ i, i < 20 → m.readLE (1772992 + 8 * i) 8 = 10 ^ i

/-- The Go global `pows` (`[60]Int`, `10^(20+i)` as four little-endian limbs; only `i < 58`, i.e. up to `10^77 < 2^256`, is claimed and ever read: the last two Go entries overflow 256 bits). -/
def TabsBig (m : Memory) : Prop :=
  m.accessible 1777472 1920 false = true ∧ ∀ i, i < 58 → m.readLE (1777472 + 32 * i) 32 = 10 ^ (20 + i)

end Fv256.Arm64.Log10
