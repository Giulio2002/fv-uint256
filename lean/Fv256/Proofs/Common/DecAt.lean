import Janus
import Fv256.Spec.DecAt

/-!
# Where `Dec`'s result string lives

`DecAt rt t1 t2 t3 p l`: the string `(p, l)` returned by `Dec` / `FormatUint` is inside the runtime-owned ranges `rt` (a
`slicebytetostring` allocation), or inside one of the three read-only tables `t1, t2, t3` of 256 bytes (the digits,
the two-digit pairs and the zero string: the code returns a pointer into them for short results).
-/

namespace Fv256.E

end Fv256.E
