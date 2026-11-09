# Coverage

Every exported symbol of [holiman/uint256](https://github.com/holiman/uint256) at master `48f3f44`
(`v1.3.3-0.20261018174624-48f3f4483d41`): 146 functions and methods, each verified on arm64 and amd64, plus one extra
`GOAMD64=v3` row (`BitLen`, see the caveats). `scripts/verify-all.sh` reads this table: a row whose per-ISA status starts with `verified`
(or `partial`) is verified, anything else fails the run. The `Family` column only groups rows.

Status values: `verified` (the theorem has a runtime-checked non-vacuity witness where the row says `+ witness`), `partial`
(verified for the stated scope only; see the Notes and `docs/HUMAN-REVIEW.md`).

The binary under verification is built from the pinned sources in `go/` with Go 1.26.0
(`GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 go build -trimpath -buildvcs=false ./cmd/harness`, amd64v3 with `GOAMD64=v3`); the expected SHA-256 of
the three harness binaries is in `scripts/harness.sha256`. The library programs hold absolute addresses of that exact binary, so
`verify-all.sh` refuses (exit 3, `HARNESS MISMATCH`) to run on any other build.

The Notes column names the proof module and the runtime contracts passed to `janus extract` for the row (`scripts/contract-flags.sh`).
Timings of the release run are recorded with the release results, not here.

| Symbol | Family | arm64 | amd64 | Notes |
|---|---|---|---|---|
| `uint256.Reciprocal` | division | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Reciprocal.lean` |
| `uint256.FromBig` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/FromBig.lean`; runtime contracts: runtime.newobject |
| `uint256.FromDecimal` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/FromDecimalMain.lean`; runtime contracts: runtime.cmpstring, runtime.ifaceeq, runtime.mallocgc, runtime.memmove, runtime.newobject, runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.gcWriteBarrier3, runtime.growslice, runtime.slicebytetostring, runtime.concatstring2 |
| `uint256.FromHex` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/FromHex.lean`; runtime contracts: runtime.newobject |
| `uint256.MustFromBig` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/MustFromBig.lean`; runtime contracts: runtime.newobject |
| `uint256.MustFromDecimal` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MustFromDecimalMain.lean`; runtime contracts: runtime.cmpstring, runtime.ifaceeq, runtime.mallocgc, runtime.memmove, runtime.newobject, runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.gcWriteBarrier3, runtime.growslice, runtime.slicebytetostring, runtime.concatstring2 |
| `uint256.MustFromHex` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/MustFromHex.lean`; runtime contracts: runtime.newobject |
| `uint256.NewInt` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/NewInt.lean`; runtime contracts: runtime.newobject |
| `(*uint256.Int).Abs` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Abs.lean` |
| `(*uint256.Int).Add` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Add.lean` |
| `(*uint256.Int).AddMod` | modular / exp / sqrt | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64/AddModMain,Amd64/AddMod}.lean` |
| `(*uint256.Int).AddOverflow` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/AddOverflow.lean` |
| `(*uint256.Int).AddUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/AddUint64.lean` |
| `(*uint256.Int).And` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/And.lean` |
| `(*uint256.Int).BitLen` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/BitLen.lean` |
| `(*uint256.Int).Byte` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Byte.lean` |
| `(*uint256.Int).ByteLen` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/ByteLen.lean` |
| `(*uint256.Int).Bytes` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Bytes.lean`; runtime contracts: runtime.newobject |
| `(*uint256.Int).Bytes20` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Bytes20.lean` |
| `(*uint256.Int).Bytes32` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Bytes32.lean` |
| `(*uint256.Int).Clear` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Clear.lean` |
| `(*uint256.Int).Clone` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Clone.lean`; runtime contracts: runtime.newobject |
| `(*uint256.Int).Cmp` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Cmp.lean` |
| `(*uint256.Int).CmpBig` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/CmpBig.lean` |
| `(*uint256.Int).CmpUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/CmpUint64.lean` |
| `(*uint256.Int).Dec` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Dec.lean`; runtime contracts: runtime.slicebytetostring, runtime.growslice, runtime.gopanic |
| `(*uint256.Int).Div` | division | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Div.lean` |
| `(*uint256.Int).DivMod` | division | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/DivMod.lean`; runtime contracts: runtime.newobject |
| `(*uint256.Int).EncodeRLP` | other | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/EncodeRLP.lean`; runtime contracts: runtime.newobject |
| `(*uint256.Int).Eq` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Eq.lean` |
| `(*uint256.Int).Exp` | modular / exp / sqrt | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Exp.lean` |
| `(*uint256.Int).ExtendSign` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/ExtendSign.lean` |
| `(*uint256.Int).Float64` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Float64.lean` |
| `(*uint256.Int).Format` | decimal / text | verified (+ witnesses) | verified (+ witnesses) | proof: `Proofs/{Arm64,Amd64}/Format.lean`; runtime contracts: runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.newobject, runtime.slicebytetostring, runtime.growslice, runtime.gopanic, fmt.Fprint, math/big.(*Int).Format, runtime.stringtoslicebyte, runtime.typeAssert |
| `(*uint256.Int).Gt` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Gt.lean` |
| `(*uint256.Int).GtUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/GtUint64.lean` |
| `(*uint256.Int).HashTreeRoot` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/HashTreeRoot.lean` |
| `(*uint256.Int).Hex` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Hex.lean`; runtime contracts: runtime.slicebytetostring |
| `(*uint256.Int).IntoBig` | conversion / SSZ | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IntoBig.lean`; runtime contracts: runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.newobject |
| `(*uint256.Int).IsUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/IsUint64.lean` |
| `(*uint256.Int).IsZero` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/IsZero.lean` |
| `(*uint256.Int).Log10` | core | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Log10.lean` |
| `(*uint256.Int).Lsh` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Lsh.lean` |
| `(*uint256.Int).Lt` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Lt.lean` |
| `(*uint256.Int).LtUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/LtUint64.lean` |
| `(*uint256.Int).MarshalJSON` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MarshalJSON.lean`; runtime contracts: runtime.slicebytetostring, runtime.growslice, runtime.gopanic, runtime.concatbyte3 |
| `(*uint256.Int).MarshalSSZ` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/MarshalSSZ.lean`; runtime contracts: runtime.makeslice |
| `(*uint256.Int).MarshalSSZAppend` | conversion / SSZ | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MarshalSSZAppendMain.lean`; runtime contracts: runtime.growslice |
| `(*uint256.Int).MarshalSSZInto` | conversion / SSZ | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MarshalSSZIntoMain.lean`; runtime contracts: runtime.convT64, fmt.errorf, runtime.newobject |
| `(*uint256.Int).MarshalText` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MarshalText.lean`; runtime contracts: runtime.slicebytetostring, runtime.growslice, runtime.gopanic, runtime.stringtoslicebyte |
| `(*uint256.Int).Mod` | division | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Mod.lean` |
| `(*uint256.Int).Mul` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Mul.lean` |
| `(*uint256.Int).MulDivOverflow` | modular / exp / sqrt | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MulDivOverflow.lean` |
| `(*uint256.Int).MulMod` | modular / exp / sqrt | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MulMod.lean` |
| `(*uint256.Int).MulModWithReciprocal` | other | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MulModWithReciprocal.lean` |
| `(*uint256.Int).MulOverflow` | core | verified | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MulOverflow.lean` |
| `(*uint256.Int).Neg` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Neg.lean` |
| `(*uint256.Int).Not` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Not.lean` |
| `(*uint256.Int).Or` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Or.lean` |
| `(*uint256.Int).PaddedBytes` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/PaddedBytes.lean`; runtime contracts: runtime.makeslice |
| `(*uint256.Int).PrettyDec` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/PrettyDec.lean`; runtime contracts: runtime.slicebytetostring, runtime.growslice, runtime.gopanic |
| `(*uint256.Int).PutUint256` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/PutUint256.lean` |
| `(*uint256.Int).Rsh` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Rsh.lean` |
| `(*uint256.Int).SDiv` | division | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/SDiv.lean` |
| `(*uint256.Int).SMod` | division | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/SMod.lean` |
| `(*uint256.Int).SRsh` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SRsh.lean` |
| `(*uint256.Int).Scan` | decimal / text | verified (+ witnesses) | verified (+ witnesses) | proof: `Proofs/{Arm64,Amd64}/Scan.lean`; runtime contracts: runtime.cmpstring, runtime.ifaceeq, runtime.mallocgc, runtime.memmove, runtime.newobject, runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.gcWriteBarrier3, runtime.growslice, runtime.slicebytetostring, runtime.concatstring2 |
| `(*uint256.Int).Set` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Set.lean` |
| `(*uint256.Int).SetAllOne` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetAllOne.lean` |
| `(*uint256.Int).SetBytes` | core | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/SetBytes.lean` |
| `(*uint256.Int).SetBytes1` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes1.lean` |
| `(*uint256.Int).SetBytes10` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes10.lean` |
| `(*uint256.Int).SetBytes11` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes11.lean` |
| `(*uint256.Int).SetBytes12` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes12.lean` |
| `(*uint256.Int).SetBytes13` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes13.lean` |
| `(*uint256.Int).SetBytes14` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes14.lean` |
| `(*uint256.Int).SetBytes15` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes15.lean` |
| `(*uint256.Int).SetBytes16` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes16.lean` |
| `(*uint256.Int).SetBytes17` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes17.lean` |
| `(*uint256.Int).SetBytes18` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes18.lean` |
| `(*uint256.Int).SetBytes19` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes19.lean` |
| `(*uint256.Int).SetBytes2` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes2.lean` |
| `(*uint256.Int).SetBytes20` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes20.lean` |
| `(*uint256.Int).SetBytes21` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes21.lean` |
| `(*uint256.Int).SetBytes22` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes22.lean` |
| `(*uint256.Int).SetBytes23` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes23.lean` |
| `(*uint256.Int).SetBytes24` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes24.lean` |
| `(*uint256.Int).SetBytes25` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes25.lean` |
| `(*uint256.Int).SetBytes26` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes26.lean` |
| `(*uint256.Int).SetBytes27` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes27.lean` |
| `(*uint256.Int).SetBytes28` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes28.lean` |
| `(*uint256.Int).SetBytes29` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes29.lean` |
| `(*uint256.Int).SetBytes3` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes3.lean` |
| `(*uint256.Int).SetBytes30` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes30.lean` |
| `(*uint256.Int).SetBytes31` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes31.lean` |
| `(*uint256.Int).SetBytes32` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes32.lean` |
| `(*uint256.Int).SetBytes4` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes4.lean` |
| `(*uint256.Int).SetBytes5` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes5.lean` |
| `(*uint256.Int).SetBytes6` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes6.lean` |
| `(*uint256.Int).SetBytes7` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes7.lean` |
| `(*uint256.Int).SetBytes8` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes8.lean` |
| `(*uint256.Int).SetBytes9` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetBytes9.lean` |
| `(*uint256.Int).SetFromBig` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetFromBig.lean` |
| `(*uint256.Int).SetFromDecimal` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/SetFromDecimal.lean`; runtime contracts: runtime.cmpstring, runtime.ifaceeq, runtime.mallocgc, runtime.memmove, runtime.newobject, runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.gcWriteBarrier3, runtime.growslice, runtime.slicebytetostring, runtime.concatstring2 |
| `(*uint256.Int).SetFromHex` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetFromHex.lean`; runtime contracts: runtime.newobject |
| `(*uint256.Int).SetOne` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetOne.lean` |
| `(*uint256.Int).SetUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SetUint64.lean` |
| `(*uint256.Int).Sgt` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Sgt.lean` |
| `(*uint256.Int).Sign` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Sign.lean` |
| `(*uint256.Int).SizeSSZ` | conversion / SSZ | verified | verified | proof: `Proofs/{Arm64,Amd64}/SizeSSZ.lean` |
| `(*uint256.Int).Slt` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Slt.lean` |
| `(*uint256.Int).Sqrt` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Sqrt.lean` |
| `(*uint256.Int).String` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/String.lean`; runtime contracts: runtime.slicebytetostring, runtime.growslice, runtime.gopanic |
| `(*uint256.Int).Sub` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Sub.lean` |
| `(*uint256.Int).SubOverflow` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SubOverflow.lean` |
| `(*uint256.Int).SubUint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/SubUint64.lean` |
| `(*uint256.Int).ToBig` | conversion / SSZ | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/ToBig.lean`; runtime contracts: runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.newobject |
| `(*uint256.Int).Uint64` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Uint64.lean` |
| `(*uint256.Int).Uint64WithOverflow` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Uint64WithOverflow.lean` |
| `(*uint256.Int).UnmarshalJSON` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/UnmarshalJSONMain.lean`; runtime contracts: runtime.cmpstring, runtime.ifaceeq, runtime.mallocgc, runtime.memmove, runtime.newobject, runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.gcWriteBarrier3, runtime.growslice, runtime.slicebytetostring, runtime.concatstring2 |
| `(*uint256.Int).UnmarshalSSZ` | conversion / SSZ | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/UnmarshalSSZMain.lean`; runtime contracts: runtime.convT64, fmt.errorf, runtime.newobject |
| `(*uint256.Int).UnmarshalText` | decimal / text | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/UnmarshalTextMain.lean`; runtime contracts: runtime.cmpstring, runtime.ifaceeq, runtime.mallocgc, runtime.memmove, runtime.newobject, runtime.gcWriteBarrier1, runtime.gcWriteBarrier2, runtime.gcWriteBarrier3, runtime.growslice, runtime.slicebytetostring, runtime.concatstring2 |
| `(*uint256.Int).Value` | conversion / SSZ | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/Value.lean`; runtime contracts: runtime.convTstring, runtime.slicebytetostring, runtime.growslice, runtime.gopanic |
| `(*uint256.Int).WriteToArray20` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/WriteToArray20.lean` |
| `(*uint256.Int).WriteToArray32` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/WriteToArray32.lean` |
| `(*uint256.Int).WriteToSlice` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/WriteToSlice.lean` |
| `(*uint256.Int).Xor` | core | verified | verified | proof: `Proofs/{Arm64,Amd64}/Xor.lean` |
| `(*uint256.Int).MulDivOverflowRem` | modular / exp / sqrt | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/MulDivOverflowRem.lean` |
| `(*uint256.Int).ReverseBytes` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/ReverseBytes.lean` |
| `(*uint256.Int).IAdd` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/IAdd.lean` |
| `(*uint256.Int).IAddMod` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IAddMod.lean` |
| `(*uint256.Int).IAddUint64` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/IAddUint64.lean` |
| `(*uint256.Int).ISubUint64` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/ISubUint64.lean` |
| `(*uint256.Int).ISub` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/ISub.lean` |
| `(*uint256.Int).IMul` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/IMul.lean` |
| `(*uint256.Int).IDiv` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IDiv.lean` |
| `(*uint256.Int).IMod` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IMod.lean` |
| `(*uint256.Int).ISMod` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/ISMod.lean` |
| `(*uint256.Int).IMulModWithReciprocal` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IMulModWithReciprocal.lean` |
| `(*uint256.Int).IMulMod` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IMulMod.lean` |
| `(*uint256.Int).ISDiv` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/ISDiv.lean` |
| `(*uint256.Int).ILsh` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/ILsh.lean` |
| `(*uint256.Int).IRsh` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/IRsh.lean` |
| `(*uint256.Int).ISRsh` | in-place | verified + witness | verified + witness | proof: `Proofs/{Arm64,Amd64}/ISRsh.lean` |
| `(*uint256.Int).IExp` | other | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/IExp.lean` |
| `(*uint256.Int).ISqrt` | in-place | verified (+ witness) | verified (+ witness) | proof: `Proofs/{Arm64,Amd64}/ISqrt.lean` |

## Row-specific caveats

- `BitLen` on amd64: the default `GOAMD64=v1` code (`BSR`/`BSF` of a possibly zero limb) is verified in `Proofs/Amd64/BitLen.lean` against the Janus
  model of `BSR`/`BSF` on zero; the statement does not mention the undefined-value stream. `Proofs/Amd64v3/BitLen.lean` is the one extra row: it verifies
  the `GOAMD64=v3` build (`lzcnt`).
- `Log10` reads the writable Go globals `uint256.pows64` / `uint256.pows` (`.noptrdata`); the theorem assumes they still hold the powers of ten
  (`Tabs64`, `TabsBig`). A program that mutates them voids the result.
- `WriteToSlice`: the code panics when `cap < len`; the theorem assumes the Go slice invariant `len <= cap` (it excludes only ill-formed slices).
- Decimal/hex parsing and `Scan`/`UnmarshalText`/`UnmarshalJSON`: the error paths assume package-init facts (the sentinel error values are initialised).
- `MarshalSSZ*`/`UnmarshalSSZ`: theorems are complete for the stated scope (e.g. `len + 32 <= cap` success path); see `docs/HUMAN-REVIEW.md`.
- Allocation (`Clone`, `NewInt`, `FromBig`, ...): stated for every `runtime.newobject` satisfying the pinned Janus allocation contract.


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

## Spec note: WriteToSlice `len <= cap`
Both ISAs: master 48f3f44 slices `dest[off-8:off]` with a bounds check against `cap`, so the call panics when `cap < len`. The theorem therefore assumes the Go slice invariant `len <= cap` (`len.toNat <= cap.toNat`); it excludes only ill-formed slices and hides no behaviour. Witnesses use `cap = len = 8`.
