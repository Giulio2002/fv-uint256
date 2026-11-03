# Coverage: every exported symbol of github.com/holiman/uint256 v1.3.2 (a17fcfb6f8b0245533928fa96aace2cd4c2e9b18)

Status values (per ISA): `todo`, `verified`, `partial` (verified for the stated scope only, see Notes), `verified (conditional, no witness)`, `pending Janus pin` (verified against an unmerged Janus revision, see Notes), `blocked` (see Notes), `out of scope`.

| Symbol | arm64 | amd64 | Notes |
|---|---|---|---|
| `uint256.Reciprocal` | todo | todo | |
| `uint256.FromBig` | verified | verified | lean/Fv256/{Arm64,Amd64}/FromBig.lean; runtime.newobject contract + SetFromBig as callee summary; `Witness`: toy allocator + concrete call, `example := correctness ...` fires (hnew and precondition jointly satisfiable) |
| `uint256.FromDecimal` | todo | todo | |
| `uint256.FromHex` | verified | verified | lean/Fv256/{Arm64,Amd64}/FromHex.lean (FV-C; runtime.newobject contract); verify time arm64 209 s, amd64 114 s on Janus c7950624 |
| `uint256.MustFromBig` | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromBig.lean; EnsuresGo with PanicRuntime P: returns when x=nil or len<=4, else panics with the \"overflow\" eface; same Witness pattern |
| `uint256.MustFromDecimal` | todo | todo | |
| `uint256.MustFromHex` | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromHex.lean (FV-C; runtime.newobject contract); verify time arm64 208 s, amd64 113 s on Janus c7950624 |
| `uint256.NewInt` | verified | verified | lean/Fv256/{Arm64,Amd64}/NewInt.lean; uses the runtime.newobject allocation contract (hypothesis hnew); Witness with a toy allocator linked at runtime.newobject |
| `(*uint256.Int).Abs` | verified | verified | lean/Fv256/{Arm64,Amd64}/Abs.lean |
| `(*uint256.Int).Add` | verified | verified | lean/Fv256/{Arm64,Amd64}/Add.lean |
| `(*uint256.Int).AddMod` | todo | todo | |
| `(*uint256.Int).AddOverflow` | verified | verified | lean/Fv256/{Arm64,Amd64}/AddOverflow.lean |
| `(*uint256.Int).AddUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/AddUint64.lean |
| `(*uint256.Int).And` | verified | verified | lean/Fv256/{Arm64,Amd64}/And.lean |
| `(*uint256.Int).BitLen` | verified | verified | arm64: lean/Fv256/Arm64/BitLen.lean. amd64 (default GOAMD64=v1): lean/Fv256/Amd64/BitLen.lean, verified on Janus c7950624 (BSR/BSF of zero model); the statement does not mention the undefined-value stream. Extra: lean/Fv256/Amd64v3/BitLen.lean verifies the GOAMD64=v3 build (lzcnt) on the pinned Janus. |
| `(*uint256.Int).Byte` | verified | verified | lean/Fv256/{Arm64,Amd64}/Byte.lean |
| `(*uint256.Int).ByteLen` | verified | verified | arm64: lean/Fv256/Arm64/ByteLen.lean. amd64 (default GOAMD64=v1): lean/Fv256/Amd64/ByteLen.lean, verified on Janus c7950624 (same BSR model). |
| `(*uint256.Int).Bytes` | verified | todo | arm64: lean/Fv256/Arm64/Bytes.lean (allocation contract hypothesis, toy-allocator Witness); single runtime call (newobject) |
| `(*uint256.Int).Bytes20` | verified | verified | lean/Fv256/{Arm64,Amd64}/Bytes20.lean |
| `(*uint256.Int).Bytes32` | verified | verified | lean/Fv256/{Arm64,Amd64}/Bytes32.lean |
| `(*uint256.Int).Clear` | verified | verified | lean/Fv256/{Arm64,Amd64}/Clear.lean |
| `(*uint256.Int).Clone` | verified | verified | lean/Fv256/{Arm64,Amd64}/Clone.lean; uses the runtime.newobject allocation contract (hypothesis hnew); Witness with a toy allocator linked at runtime.newobject |
| `(*uint256.Int).Cmp` | verified | verified | lean/Fv256/{Arm64,Amd64}/Cmp.lean |
| `(*uint256.Int).CmpBig` | verified | verified | callees SetFromBig + Cmp extracted; z.Cmp(FromBig(b)) with overflow/sign handling; no runtime call |
| `(*uint256.Int).CmpUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/CmpUint64.lean |
| `(*uint256.Int).Dec` | todo | todo | |
| `(*uint256.Int).Div` | todo (needs bits.Div64 summary, U10) | on branch fv/wb: verified (pending merge) | proofs on branch fv/wb (family B, COVERAGE-B.md); not merged to main until the pin moves |
| `(*uint256.Int).DivMod` | todo | todo | |
| `(*uint256.Int).EncodeRLP` | todo | todo | |
| `(*uint256.Int).Eq` | verified | verified | lean/Fv256/{Arm64,Amd64}/Eq.lean |
| `(*uint256.Int).Exp` | todo | todo | |
| `(*uint256.Int).ExtendSign` | verified | verified | lean/Fv256/{Arm64,Amd64}/ExtendSign.lean |
| `(*uint256.Int).Float64` | on branch fv/wb: verified (pending merge) | on branch fv/wb: verified (pending merge) | branch fv/wb |
| `(*uint256.Int).Format` | out of scope | out of scope | math/big Format through a dynamic fmt.State (interface calls into fmt/strconv/big): not provable at reasonable cost (upstream analysis DESIGN-U5-U6) |
| `(*uint256.Int).Gt` | verified | verified | lean/Fv256/{Arm64,Amd64}/Gt.lean |
| `(*uint256.Int).GtUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/GtUint64.lean |
| `(*uint256.Int).HashTreeRoot` | verified | verified | arm64: no calls; amd64: memmove (MemmoveLive contract) |
| `(*uint256.Int).Hex` | blocked U16 (fv/wc) | todo | FV-C; see COVERAGE-C.md on fv/wc |
| `(*uint256.Int).IntoBig` | todo | todo | |
| `(*uint256.Int).IsUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/IsUint64.lean |
| `(*uint256.Int).IsZero` | verified | verified | lean/Fv256/{Arm64,Amd64}/IsZero.lean |
| `(*uint256.Int).Log10` | verified | verified | arm64: lean/Fv256/Arm64/Log10.lean (+ L10Cases/C<k>_<m>.lean, one per top nonzero limb k and its bit length m, + Zero); assumes the writable powers-of-ten tables (L10Defs.lean). amd64: lean/Fv256/Amd64/Log10.lean (same layout), verified on Janus c7950624 (the lowest limb's BSR may see zero); same table assumption. |
| `(*uint256.Int).Lsh` | verified | verified | arm64: lean/Fv256/Arm64/Lsh.lean; amd64: machine code uses mask/SHLD idioms (`&&& (if .. then -1 else 0)`), proof not yet done (probe in wip/) |
| `(*uint256.Int).Lt` | verified | verified | lean/Fv256/{Arm64,Amd64}/Lt.lean |
| `(*uint256.Int).LtUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/LtUint64.lean |
| `(*uint256.Int).MarshalJSON` | todo | todo | |
| `(*uint256.Int).MarshalSSZ` | verified | verified | lean/Fv256/{Arm64,Amd64}/MarshalSSZ.lean; runtime.makeslice contract (growslice calls are inlined away: capacity is known); allocator witness inside |
| `(*uint256.Int).MarshalSSZAppend` | partial | partial | lean/Fv256/{Arm64,Amd64}/MarshalSSZAppend.lean: PARTIAL, verified only for `len + 32 <= cap` (compiled code never calls growslice). The reallocating case calls runtime.growslice with a 1-byte element type; the pinned GrowsliceContract covers only 8-byte pointer-free elements, so that case is NOT verified (needs a growslice contract for 1-byte elements) |
| `(*uint256.Int).MarshalSSZInto` | partial | partial | lean/Fv256/{Arm64,Amd64}/MarshalSSZInto.lean: PARTIAL, success path only (`32 <= len <= cap`); error path (fmt.Errorf) not covered |
| `(*uint256.Int).MarshalText` | todo | todo | |
| `(*uint256.Int).Mod` | todo (needs bits.Div64 summary, U10) | on branch fv/wb: verified (pending merge) | branch fv/wb |
| `(*uint256.Int).Mul` | verified | verified | lean/Fv256/{Arm64,Amd64}/Mul.lean; amd64 post allows the 16-byte stack scratch slot (OnlyWrites2) |
| `(*uint256.Int).MulDivOverflow` | todo | todo | |
| `(*uint256.Int).MulMod` | todo | todo | |
| `(*uint256.Int).MulModWithReciprocal` | todo | todo | |
| `(*uint256.Int).MulOverflow` | verified | pending Janus integ/speed15 | arm64: lean/Fv256/Arm64/MulOverflow.lean (+ MoCases/A..E, one per aliasing pattern of z,x,y); verified on c7950624 (295 s). amd64: lean/Fv256/Amd64/MulOverflow.lean (+ MoCases/A..E; value via Util.mul_limbs + per-limb janus_carry, stores peeled by janus64_simp); needs the overlap fix of integ/speed15; verified on Janus 689b0f67 in 696 s full (cases on 8821a47f: A 331, B 84, C 85, D 76, E 70 s) |
| `(*uint256.Int).Neg` | verified | verified | lean/Fv256/{Arm64,Amd64}/Neg.lean |
| `(*uint256.Int).Not` | verified | verified | lean/Fv256/{Arm64,Amd64}/Not.lean |
| `(*uint256.Int).Or` | verified | verified | lean/Fv256/{Arm64,Amd64}/Or.lean |
| `(*uint256.Int).PaddedBytes` | verified | todo | arm64: lean/Fv256/Arm64/PaddedBytes.lean (+ PadCases/Case<k>.lean for n = 0..31 and CaseBig for n >= 32); makeslice contract hypothesis (n <= 2^48 precondition: the panic paths are excluded), toy-allocator Witness |
| `(*uint256.Int).PrettyDec` | todo | todo | |
| `(*uint256.Int).PutUint256` | verified | verified | lean/Fv256/{Arm64,Amd64}/PutUint256.lean |
| `(*uint256.Int).Rsh` | verified | verified | arm64: lean/Fv256/Arm64/Rsh.lean; amd64 not yet done (same idioms as Lsh) |
| `(*uint256.Int).SDiv` | todo (needs bits.Div64 summary, U10) | on branch fv/wb: verified (pending merge) | branch fv/wb |
| `(*uint256.Int).SMod` | todo (needs bits.Div64 summary, U10) | on branch fv/wb: verified (pending merge) | branch fv/wb |
| `(*uint256.Int).SRsh` | verified | verified | lean/Fv256/{Arm64,Amd64}/SRsh.lean |
| `(*uint256.Int).Scan` | todo | todo | |
| `(*uint256.Int).Set` | verified | verified | lean/Fv256/{Arm64,Amd64}/Set.lean |
| `(*uint256.Int).SetAllOne` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetAllOne.lean |
| `(*uint256.Int).SetBytes` | todo | todo | |
| `(*uint256.Int).SetBytes1` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes1.lean; verify time arm64 508s, amd64 35s on Janus c7950624 |
| `(*uint256.Int).SetBytes10` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes10.lean; verify time arm64 14s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes11` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes11.lean; verify time arm64 15s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes12` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes12.lean; verify time arm64 15s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes13` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes13.lean; verify time arm64 14s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes14` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes14.lean; verify time arm64 13s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes15` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes15.lean; verify time arm64 14s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes16` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes16.lean; verify time arm64 52s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes17` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes17.lean; verify time arm64 13s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes18` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes18.lean; verify time arm64 14s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes19` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes19.lean; verify time arm64 16s, amd64 18s on Janus c7950624 |
| `(*uint256.Int).SetBytes2` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes2.lean; verify time arm64 13s, amd64 258s on Janus c7950624 |
| `(*uint256.Int).SetBytes20` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes20.lean; verify time arm64 18s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes21` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes21.lean; verify time arm64 15s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes22` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes22.lean; verify time arm64 15s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes23` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes23.lean; verify time arm64 16s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes24` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes24.lean; verify time arm64 91s, amd64 15s on Janus c7950624 |
| `(*uint256.Int).SetBytes25` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes25.lean; verify time arm64 14s, amd64 16s on Janus c7950624 |
| `(*uint256.Int).SetBytes26` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes26.lean; verify time arm64 15s, amd64 16s on Janus c7950624 |
| `(*uint256.Int).SetBytes27` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes27.lean; verify time arm64 17s, amd64 24s on Janus c7950624 |
| `(*uint256.Int).SetBytes28` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes28.lean; verify time arm64 23s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes29` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes29.lean; verify time arm64 17s, amd64 16s on Janus c7950624 |
| `(*uint256.Int).SetBytes3` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes3.lean; verify time arm64 13s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes30` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes30.lean; verify time arm64 18s, amd64 15s on Janus c7950624 |
| `(*uint256.Int).SetBytes31` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes31.lean; verify time arm64 18s, amd64 15s on Janus c7950624 |
| `(*uint256.Int).SetBytes32` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes32.lean |
| `(*uint256.Int).SetBytes4` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes4.lean; verify time arm64 12s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes5` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes5.lean; verify time arm64 14s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes6` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes6.lean; verify time arm64 13s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes7` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes7.lean; verify time arm64 14s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes8` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes8.lean; verify time arm64 not timed (SetBytes8 arm64 predates the batch), amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes9` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes9.lean; verify time arm64 14s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetFromBig` | verified | verified | reads big.Int {neg, abs nat} layout; no runtime call |
| `(*uint256.Int).SetFromDecimal` | todo | todo | |
| `(*uint256.Int).SetFromHex` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetFromHex.lean (FV-C; runtime.newobject contract); verify time arm64 672 s, amd64 82 s uncached on Janus c7950624 |
| `(*uint256.Int).SetOne` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetOne.lean |
| `(*uint256.Int).SetUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/SetUint64.lean |
| `(*uint256.Int).Sgt` | verified | verified | lean/Fv256/{Arm64,Amd64}/Sgt.lean |
| `(*uint256.Int).Sign` | verified | verified | lean/Fv256/{Arm64,Amd64}/Sign.lean |
| `(*uint256.Int).SizeSSZ` | verified | verified | lean/Fv256/{Arm64,Amd64}/SizeSSZ.lean |
| `(*uint256.Int).Slt` | verified | verified | lean/Fv256/{Arm64,Amd64}/Slt.lean |
| `(*uint256.Int).Sqrt` | todo | todo | |
| `(*uint256.Int).String` | todo | todo | |
| `(*uint256.Int).Sub` | verified | verified | lean/Fv256/{Arm64,Amd64}/Sub.lean |
| `(*uint256.Int).SubOverflow` | verified | verified | lean/Fv256/{Arm64,Amd64}/SubOverflow.lean |
| `(*uint256.Int).SubUint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/SubUint64.lean |
| `(*uint256.Int).ToBig` | todo | todo | |
| `(*uint256.Int).Uint64` | verified | verified | lean/Fv256/{Arm64,Amd64}/Uint64.lean |
| `(*uint256.Int).Uint64WithOverflow` | verified | verified | lean/Fv256/{Arm64,Amd64}/Uint64WithOverflow.lean |
| `(*uint256.Int).UnmarshalJSON` | todo | todo | |
| `(*uint256.Int).UnmarshalSSZ` | partial | partial | lean/Fv256/{Arm64,Amd64}/UnmarshalSSZ.lean: PARTIAL, success path only (`len(buf) = 32`); extracted with `--contract fmt.errorf --contract runtime.convT64 --contract runtime.newobject` (the error path is not covered: no fmt.Errorf contract exists) |
| `(*uint256.Int).UnmarshalText` | todo | todo | |
| `(*uint256.Int).Value` | todo | todo | |
| `(*uint256.Int).WriteToArray20` | verified | verified | lean/Fv256/{Arm64,Amd64}/WriteToArray20.lean |
| `(*uint256.Int).WriteToArray32` | verified | verified | lean/Fv256/{Arm64,Amd64}/WriteToArray32.lean |
| `(*uint256.Int).WriteToSlice` | verified | verified | arm64: lean/Fv256/Arm64/WriteToSlice.lean (+ WtsCases/Case<k>.lean, one module per min(len,32); the byte loop is unrolled); amd64: same layout under Fv256/Amd64 |
| `(*uint256.Int).Xor` | verified | verified | lean/Fv256/{Arm64,Amd64}/Xor.lean |
| `(*uint256.Int).MulDivOverflowRem` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ReverseBytes` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IAdd` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IAddMod` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IAddUint64` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISubUint64` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISub` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IMul` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IDiv` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IMod` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISMod` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IMulModWithReciprocal` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IMulMod` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISDiv` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ILsh` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IRsh` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISRsh` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IExp` | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISqrt` | todo | todo | new in master 48f3f44 |

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

## Proof times (optimisation log)
Standing duty: every proof over ~5 min (or >2x its peers) gets a profile-and-fix pass. Times are `janus verify` wall seconds, base f65043ca vs head 9c4be184, as measured by main; "after" is filled in when a fix lands.

| item | before | after | status / plan |
|---|---|---|---|
| MulOverflow amd64 | > 3000 s (value closer `janus_arith` on stores not peeled) | 696 s full (cases 70-331 s) | FIXED: 16-byte stores split via janus64_simp + mul_limbs per-limb janus_carry |
| MulOverflow arm64 | > 3300 s (timeout, exit 124; case E alone OOM > 33 GB) | 295 s (closers ~20 s per aliasing case) | FIXED: cause was `refine mo_flag … <;> first \| omega \| …` running omega on the huge limb goals; now one bullet per goal |
| WriteToSlice arm64 | 429 s | - | profile pass pending |
| ExtendSign amd64 / arm64 | 262 / 238 s, 144 / 127 s | - | profile pass pending |
| SRsh amd64 | 175 s | - | profile pass pending |
| Slt, Sgt amd64 | ~80-104 s each | - | profile pass pending |
| SetBytes1 arm64 | 508 s (first item of its chunk) | 4 s elaboration | NOT a proof cost: one-time Janus framework build included in the chunk's first item (upstream profile on integ/speed15) |
| SetBytes2 amd64 | 258 s (first item of its chunk) | 2 s elaboration | NOT a proof cost: cold framework build artefact (upstream profile) |
| SetBytes24 arm64 | 91 s (79 s on integ/speed15) | - | REAL: ~75 s is one `(try omega)` in the closer (24 byte bounds + big sums); replace by a per-width fromBE byte-sum lemma. Low priority |
| SetBytes16 arm64 | 52 s (43 s on integ/speed15) | - | REAL: ~39 s one `(try omega)`; same fix as SetBytes24. Low priority |
| Abs arm64 | 64 s (base) / 508 s (head) | - | rerun cold and warm to separate a head-stack regression from a cold-build artefact |

## Pin bump to Janus c7950624 (2026-11-03)
`scripts/verify-all.sh` against Janus `c7950624d0f8d6cb1bb439ee343923be94a52fdc`, 11 parallel chunks: **122 PASS / 0 FAIL** (62 functions, both ISAs, plus the GOAMD64=v3 BitLen proof). Nothing that passed on the earlier pins fails here (no U18 dependency).
Chunk wall times (s, 6 functions each, 3 chunks at a time): 1338 (incl. framework build), 273, 509, 507, 1569, 266, 814, 225, 390, 139, 528.
