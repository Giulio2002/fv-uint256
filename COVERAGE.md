# Coverage: every exported symbol of github.com/holiman/uint256 v1.3.2 (a17fcfb6f8b0245533928fa96aace2cd4c2e9b18)

Status values: `todo`, `verified-arm64`, `verified-amd64`, `verified` (both), `blocked` (see reason).

| Symbol | arm64 | amd64 | Notes |
|---|---|---|---|
| `uint256.Reciprocal` | todo | todo | |
| `uint256.FromBig` | todo | todo | |
| `uint256.FromDecimal` | todo | todo | |
| `uint256.FromHex` | todo | todo | |
| `uint256.MustFromBig` | todo | todo | |
| `uint256.MustFromDecimal` | todo | todo | |
| `uint256.MustFromHex` | todo | todo | |
| `uint256.NewInt` | todo | todo | |
| `(*uint256.Int).Abs` | todo | todo | |
| `(*uint256.Int).Add` | verified | verified | lean/Fv256/{Arm64,Amd64}/Add.lean |
| `(*uint256.Int).AddMod` | todo | todo | |
| `(*uint256.Int).AddOverflow` | todo | todo | |
| `(*uint256.Int).AddUint64` | todo | todo | |
| `(*uint256.Int).And` | verified | verified | lean/Fv256/{Arm64,Amd64}/And.lean |
| `(*uint256.Int).BitLen` | todo | todo | |
| `(*uint256.Int).Byte` | todo | todo | |
| `(*uint256.Int).ByteLen` | todo | todo | |
| `(*uint256.Int).Bytes` | todo | todo | |
| `(*uint256.Int).Bytes20` | todo | todo | |
| `(*uint256.Int).Bytes32` | todo | todo | |
| `(*uint256.Int).Clear` | todo | todo | |
| `(*uint256.Int).Clone` | todo | todo | |
| `(*uint256.Int).Cmp` | todo | todo | attempt in wip/: hypotheses with addWithCarry chains not normalised by simp at * |
| `(*uint256.Int).CmpBig` | todo | todo | |
| `(*uint256.Int).CmpUint64` | todo | todo | |
| `(*uint256.Int).Dec` | todo | todo | |
| `(*uint256.Int).Div` | todo | todo | |
| `(*uint256.Int).DivMod` | todo | todo | |
| `(*uint256.Int).EncodeRLP` | todo | todo | |
| `(*uint256.Int).Eq` | verified | verified | lean/Fv256/{Arm64,Amd64}/Eq.lean |
| `(*uint256.Int).Exp` | todo | todo | |
| `(*uint256.Int).ExtendSign` | todo | todo | |
| `(*uint256.Int).Float64` | todo | todo | |
| `(*uint256.Int).Format` | todo | todo | |
| `(*uint256.Int).Gt` | verified | verified | lean/Fv256/{Arm64,Amd64}/Gt.lean |
| `(*uint256.Int).GtUint64` | todo | todo | |
| `(*uint256.Int).HashTreeRoot` | todo | todo | |
| `(*uint256.Int).Hex` | todo | todo | |
| `(*uint256.Int).IntoBig` | todo | todo | |
| `(*uint256.Int).IsUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/IsUint64.lean |
| `(*uint256.Int).IsZero` | verified | verified | lean/Fv256/{Arm64,Amd64}/IsZero.lean |
| `(*uint256.Int).Log10` | todo | todo | |
| `(*uint256.Int).Lsh` | todo | todo | |
| `(*uint256.Int).Lt` | verified | verified | lean/Fv256/{Arm64,Amd64}/Lt.lean |
| `(*uint256.Int).LtUint64` | todo | todo | |
| `(*uint256.Int).MarshalJSON` | todo | todo | |
| `(*uint256.Int).MarshalSSZ` | todo | todo | |
| `(*uint256.Int).MarshalSSZAppend` | todo | todo | |
| `(*uint256.Int).MarshalSSZInto` | todo | todo | |
| `(*uint256.Int).MarshalText` | todo | todo | |
| `(*uint256.Int).Mod` | todo | todo | |
| `(*uint256.Int).Mul` | todo | todo | |
| `(*uint256.Int).MulDivOverflow` | todo | todo | |
| `(*uint256.Int).MulMod` | todo | todo | |
| `(*uint256.Int).MulModWithReciprocal` | todo | todo | |
| `(*uint256.Int).MulOverflow` | todo | todo | |
| `(*uint256.Int).Neg` | verified | verified | lean/Fv256/{Arm64,Amd64}/Neg.lean |
| `(*uint256.Int).Not` | verified | verified | lean/Fv256/{Arm64,Amd64}/Not.lean |
| `(*uint256.Int).Or` | verified | verified | lean/Fv256/{Arm64,Amd64}/Or.lean |
| `(*uint256.Int).PaddedBytes` | todo | todo | |
| `(*uint256.Int).PrettyDec` | todo | todo | |
| `(*uint256.Int).PutUint256` | todo | todo | |
| `(*uint256.Int).Rsh` | todo | todo | |
| `(*uint256.Int).SDiv` | todo | todo | |
| `(*uint256.Int).SMod` | todo | todo | |
| `(*uint256.Int).SRsh` | todo | todo | |
| `(*uint256.Int).Scan` | todo | todo | |
| `(*uint256.Int).Set` | todo | todo | |
| `(*uint256.Int).SetAllOne` | todo | todo | |
| `(*uint256.Int).SetBytes` | todo | todo | |
| `(*uint256.Int).SetBytes1` | todo | todo | |
| `(*uint256.Int).SetBytes10` | todo | todo | |
| `(*uint256.Int).SetBytes11` | todo | todo | |
| `(*uint256.Int).SetBytes12` | todo | todo | |
| `(*uint256.Int).SetBytes13` | todo | todo | |
| `(*uint256.Int).SetBytes14` | todo | todo | |
| `(*uint256.Int).SetBytes15` | todo | todo | |
| `(*uint256.Int).SetBytes16` | todo | todo | |
| `(*uint256.Int).SetBytes17` | todo | todo | |
| `(*uint256.Int).SetBytes18` | todo | todo | |
| `(*uint256.Int).SetBytes19` | todo | todo | |
| `(*uint256.Int).SetBytes2` | todo | todo | |
| `(*uint256.Int).SetBytes20` | todo | todo | |
| `(*uint256.Int).SetBytes21` | todo | todo | |
| `(*uint256.Int).SetBytes22` | todo | todo | |
| `(*uint256.Int).SetBytes23` | todo | todo | |
| `(*uint256.Int).SetBytes24` | todo | todo | |
| `(*uint256.Int).SetBytes25` | todo | todo | |
| `(*uint256.Int).SetBytes26` | todo | todo | |
| `(*uint256.Int).SetBytes27` | todo | todo | |
| `(*uint256.Int).SetBytes28` | todo | todo | |
| `(*uint256.Int).SetBytes29` | todo | todo | |
| `(*uint256.Int).SetBytes3` | todo | todo | |
| `(*uint256.Int).SetBytes30` | todo | todo | |
| `(*uint256.Int).SetBytes31` | todo | todo | |
| `(*uint256.Int).SetBytes32` | todo | todo | |
| `(*uint256.Int).SetBytes4` | todo | todo | |
| `(*uint256.Int).SetBytes5` | todo | todo | |
| `(*uint256.Int).SetBytes6` | todo | todo | |
| `(*uint256.Int).SetBytes7` | todo | todo | |
| `(*uint256.Int).SetBytes8` | todo | todo | |
| `(*uint256.Int).SetBytes9` | todo | todo | |
| `(*uint256.Int).SetFromBig` | todo | todo | |
| `(*uint256.Int).SetFromDecimal` | todo | todo | |
| `(*uint256.Int).SetFromHex` | todo | todo | |
| `(*uint256.Int).SetOne` | todo | todo | |
| `(*uint256.Int).SetUint64` | todo | todo | |
| `(*uint256.Int).Sgt` | verified | todo | arm64: lean/Fv256/Arm64/Sgt.lean; amd64: proof attempt in wip/ times out (30 branch cases, omega on 256-bit constants) |
| `(*uint256.Int).Sign` | verified | verified | lean/Fv256/{Arm64,Amd64}/Sign.lean |
| `(*uint256.Int).SizeSSZ` | todo | todo | |
| `(*uint256.Int).Slt` | verified | todo | arm64: lean/Fv256/Arm64/Slt.lean; amd64: proof attempt in wip/ times out (30 branch cases, omega on 256-bit constants) |
| `(*uint256.Int).Sqrt` | todo | todo | |
| `(*uint256.Int).String` | todo | todo | |
| `(*uint256.Int).Sub` | verified | verified | lean/Fv256/{Arm64,Amd64}/Sub.lean |
| `(*uint256.Int).SubOverflow` | todo | todo | |
| `(*uint256.Int).SubUint64` | todo | todo | |
| `(*uint256.Int).ToBig` | todo | todo | |
| `(*uint256.Int).Uint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/Uint64.lean |
| `(*uint256.Int).Uint64WithOverflow` | todo | todo | |
| `(*uint256.Int).UnmarshalJSON` | todo | todo | |
| `(*uint256.Int).UnmarshalSSZ` | todo | todo | |
| `(*uint256.Int).UnmarshalText` | todo | todo | |
| `(*uint256.Int).Value` | todo | todo | |
| `(*uint256.Int).WriteToArray20` | todo | todo | |
| `(*uint256.Int).WriteToArray32` | todo | todo | |
| `(*uint256.Int).WriteToSlice` | todo | todo | |
| `(*uint256.Int).Xor` | verified | verified | lean/Fv256/{Arm64,Amd64}/Xor.lean |

## Exported variables (data, no code to verify)

- `uint256.ErrBadBufferLength`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrBadEncodedLength`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrBig256Range`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrEmptyNumber`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrEmptyString`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrLeadingZero`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrMissingPrefix`: sentinel error value, n/a (no code); used by the functions that return it.
- `uint256.ErrSyntax`: sentinel error value, n/a (no code); used by the functions that return it.

Type `uint256.Int` is `[4]uint64` (little-endian limbs); no code.
