import Fv256.Proofs.Common.PrettyMath
import Fv256.Spec.Txt

/-!
# Specifications of `MarshalText`, `MarshalJSON`, `Value` (family E)

From the Go documentation (`conversion.go`, `sql.go`):

* `MarshalText() ([]byte, error)`: "marshals using the decimal representation (compatible with big.Int)": the bytes of `Dec(z)`, error nil.
* `MarshalJSON() ([]byte, error)`: "marshals using the 'decimal string' representation": a double quote, the decimal digits, a double quote;
  error nil.
* `Value() (driver.Value, error)`: the decimal string `Dec(z)` as a `driver.Value` (an interface holding a `string`), error nil.
* `PrettyDec(sep byte) string`: the decimal digits with `sep` between groups of three, counted from the right (`prettyBytes`, `PrettyMath`);
  "0" for zero.
-/

namespace Fv256.E

/-- `MarshalText`'s bytes of the number `v`. -/
def marshalTextBytes (v : Nat) : List Nat := decBytes v

/-- `Value`'s string of the number `v`. -/
def valueBytes (v : Nat) : List Nat := decBytes v

theorem marshalJSONBytes_length (v : Nat) : (marshalJSONBytes v).length = decLen v + 2 := by
  simp [marshalJSONBytes, decLen]

theorem marshalJSONBytes_head (v : Nat) : (marshalJSONBytes v).head? = some 34 := rfl

theorem prettyBytes_zero (sep : Nat) : prettyBytes sep 0 = [48] := by
  rw [prettyBytes_lt sep 0 (by omega)]; simp [decBytes_lt 0 (by omega)]

end Fv256.E
