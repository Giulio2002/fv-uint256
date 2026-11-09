import Fv256.Proofs.Common.SpecI
import Fv256.Spec.Scan

/-!
# `(*uint256.Int).Scan(src any) error` (master 48f3f44): the specification (Extracted-free)

Documented behaviour (conversion.go: "Scan implements the database/sql Scanner interface. It decodes a string, because that is what
postgres uses for its numeric type", and `TestScanScientific`): 

* `Scan(nil)` clears the receiver and returns nil;
* `Scan` of a `string` or `[]byte` decodes the decimal string `s`, with an optional scientific suffix: `s = mantissa "e" exponent`,
  where the split is at the FIRST `'e'`.  An empty `s` is `0`.  Without `'e'` it is `SetFromDecimal(s)`.  With it: the mantissa is parsed
  by `SetFromDecimal` (its error, if any, is returned); the exponent text `"0"` returns the mantissa; otherwise the exponent is parsed by
  `SetFromDecimal` (its error returned, the chunk reported relative to the exponent text), and the result is `mantissa * 10^exponent`,
  with `ErrBig256Range` for an exponent above 77 (`10^78 > 2^256`) or a product of `2^256` or more;
* any other dynamic type returns the error `unsupported type`, and the receiver is untouched.

`sciParse b n` is the outcome for the string whose bytes are `b 0, ..., b (n-1)`, in the `Res` encoding of `Fv256.I`
(`ok v` / `eof` / `range` / `syntax lo len`, `lo` relative to the whole string).  The value of the receiver on an error return is not
specified by the documentation (only the mantissa/product case `range` from the overflow leaves a wrapped product); the theorems
say nothing about it.
-/

open Fv256.I

namespace Fv256.ScanSpec

end Fv256.ScanSpec
