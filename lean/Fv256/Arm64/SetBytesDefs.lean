import Extracted

namespace Fv256.Arm64.SetBytes

/-- number of bytes used: all of them up to 32, else the last 32 -/
def used (len : Nat) : Nat := if len < 32 then len else 32

end Fv256.Arm64.SetBytes
