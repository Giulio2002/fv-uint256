# Coverage: every exported symbol of github.com/holiman/uint256 (target: master 48f3f44, branch fv/master; the 191 v1.3.2 pairs a17fcfb6 are re-verified on it)

Owner column: FV-A (Spec/Util/COVERAGE, family A), FV-B (division), FV-C (conversion/allocation/SSZ), FV-D (in-place I* ops, ReverseBytes), FV-E (decimal/text, EncodeRLP), FV-F (modular, Exp, Sqrt, Reciprocal, MulDivOverflow).

Status values (per ISA): `todo`, `verified`, `partial` (verified for the stated scope only, see Notes), `verified (conditional, no witness)`, `pending Janus pin` (verified against an unmerged Janus revision, see Notes), `blocked` (see Notes), `out of scope`.

| Symbol | Owner | arm64 | amd64 | Notes |
|---|---|---|---|---|
| `uint256.Reciprocal` | FV-F | todo | todo | |
| `uint256.FromBig` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/FromBig.lean; runtime.newobject contract + SetFromBig as callee summary; `Witness`: toy allocator + concrete call, `example := correctness ...` fires (hnew and precondition jointly satisfiable) |
| `uint256.FromDecimal` | FV-E | todo | todo | |
| `uint256.FromHex` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/FromHex.lean (FV-C; runtime.newobject contract); verify time arm64 209 s, amd64 114 s on Janus c7950624 |
| `uint256.MustFromBig` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromBig.lean; EnsuresGo with PanicRuntime P: returns when x=nil or len<=4, else panics with the \"overflow\" eface; same Witness pattern |
| `uint256.MustFromDecimal` | FV-E | todo | todo | |
| `uint256.MustFromHex` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromHex.lean (FV-C; runtime.newobject contract); verify time arm64 208 s, amd64 113 s on Janus c7950624 |
| `uint256.NewInt` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/NewInt.lean; uses the runtime.newobject allocation contract (hypothesis hnew); Witness with a toy allocator linked at runtime.newobject |
| `(*uint256.Int).Abs` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Abs.lean |
| `(*uint256.Int).Add` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Add.lean |
| `(*uint256.Int).AddMod` | FV-F | todo | todo | |
| `(*uint256.Int).AddOverflow` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/AddOverflow.lean |
| `(*uint256.Int).AddUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/AddUint64.lean |
| `(*uint256.Int).And` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/And.lean |
| `(*uint256.Int).BitLen` | FV-A | verified | verified | arm64: lean/Fv256/Arm64/BitLen.lean. amd64 (default GOAMD64=v1): lean/Fv256/Amd64/BitLen.lean, verified on Janus c7950624 (BSR/BSF of zero model); the statement does not mention the undefined-value stream. Extra: lean/Fv256/Amd64v3/BitLen.lean verifies the GOAMD64=v3 build (lzcnt) on the pinned Janus. |
| `(*uint256.Int).Byte` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Byte.lean |
| `(*uint256.Int).ByteLen` | FV-A | verified | verified | arm64: lean/Fv256/Arm64/ByteLen.lean. amd64 (default GOAMD64=v1): lean/Fv256/Amd64/ByteLen.lean, verified on Janus c7950624 (same BSR model). |
| `(*uint256.Int).Bytes` | FV-A | verified | verified | arm64: lean/Fv256/Arm64/Bytes.lean; amd64: lean/Fv256/Amd64/Bytes.lean (master 48f3f44, Janus f1d61dc1, 1085-1306 s depending on load; profile pending (a quick restructure into per-conjunct bullets with hypothesis clearing gained only ~10%, so the cost is in janus64_run and the four bsr-branch closers, to be profiled with --keep-workspace)). runtime.newobject contract (hnew); results are RAX,RBX,RCX = regs 0,3,1 (ptr, len, cap); Witness with a toy allocator (nonvacuous/returns), restatement as exists-with-contract pending the witness rule |
| `(*uint256.Int).Bytes20` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Bytes20.lean (master copies through a local array; Janus f1d61dc1) |
| `(*uint256.Int).Bytes32` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Bytes32.lean |
| `(*uint256.Int).Clear` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Clear.lean |
| `(*uint256.Int).Clone` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Clone.lean; uses the runtime.newobject allocation contract (hypothesis hnew); Witness with a toy allocator linked at runtime.newobject |
| `(*uint256.Int).Cmp` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Cmp.lean |
| `(*uint256.Int).CmpBig` | FV-C | verified | verified | callees SetFromBig + Cmp extracted; z.Cmp(FromBig(b)) with overflow/sign handling; no runtime call |
| `(*uint256.Int).CmpUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/CmpUint64.lean |
| `(*uint256.Int).Dec` | FV-E | verified (+ witness) | verified (+ witness) | fv/we 6d0c974 (merged), Janus dbd8224e, correctness + Witness.nonvacuous in one run per ISA (amd64 52m34s, arm64 41m15s); formatBits is real extracted code (call pruned by base 10), no formatBits contract; hypothesis contract: runtime slicebytetostring only (growslice, gopanic pinned stubs). Structure: dec_summary + generic Summary-to-Ensures bridge. Witness: toy slicebytetostring with z = 0 (zero path; a big-path witness is still to do) |
| `(*uint256.Int).Div` | FV-B | todo | verified (+ witness) | amd64 on master 48f3f44 (FV-B, fv/wb-master 69d4089, Janus 6365855c, correctness + Witness.nonvacuous in one run, 2519 s cold; shared DivProg/SDivProg/SModProg/ChainProg libraries, spec divSpec/modSpec/sdiv/smod, y = 0 gives 0). arm64: FV-G/FV-H in progress | ; arm64 (FV-G, fv/wg f8d44ba, Janus ffaae554, correctness + Witness.nonvacuous in one run): unconditional (calls udivrem_nil_L_final), summary body ~8 min cold, verify 14.5 s warm 
| `(*uint256.Int).DivMod` | FV-B | todo | verified (+ witness) | amd64 on master 48f3f44 (FV-B, fv/wb-master 69d4089, Janus 6365855c, correctness + Witness.nonvacuous in one run, 2625 s cold; shared DivProg/SDivProg/SModProg/ChainProg libraries, spec divSpec/modSpec/sdiv/smod, y = 0 gives 0). arm64: FV-G/FV-H in progress |
| `(*uint256.Int).EncodeRLP` | FV-E | todo | todo | |
| `(*uint256.Int).Eq` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Eq.lean |
| `(*uint256.Int).Exp` | FV-F | todo | todo | |
| `(*uint256.Int).ExtendSign` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/ExtendSign.lean |
| `(*uint256.Int).Float64` | FV-A | on branch fv/wb: verified (pending merge) | on branch fv/wb: verified (pending merge) | branch fv/wb |
| `(*uint256.Int).Format` | FV-E | out of scope | out of scope | math/big Format through a dynamic fmt.State (interface calls into fmt/strconv/big): not provable at reasonable cost (upstream analysis DESIGN-U5-U6) |
| `(*uint256.Int).Gt` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Gt.lean |
| `(*uint256.Int).GtUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/GtUint64.lean |
| `(*uint256.Int).HashTreeRoot` | FV-A | verified | verified | arm64: no calls; amd64: memmove (MemmoveLive contract) ; amd64 re-proved on master 48f3f44 (frameless leaf: no stack check, window [SP-40, SP+40), 9 s, Janus f1d61dc1) |
| `(*uint256.Int).Hex` | FV-E | blocked U16 (fv/wc) | todo | FV-C; see COVERAGE-C.md on fv/wc |
| `(*uint256.Int).IntoBig` | FV-C | verified (+ witness) | verified (+ witness) | arm64 (fv/wc, Janus ffaae554) and amd64 (Janus aab47543, correctness + Witness.nonvacuous in ONE run, 1997 s cold): lean/Fv256/{Arm64,Amd64}/IntoBig{Defs,FinF,Close,Loop,Tail,Slow3,Mid}.lean + IntoBig.lean (main) + IntoBigCommon. Contracts NewobjectLive(64)Contract@runtime.newobject and WbLive(64)Contract@runtime.gcWriteBarrier1/2. amd64 witness: stub runtime at the contract addresses, IntoBig(z, &b) with b == nil. Extraction flags in scripts/contract-flags.sh |
| `(*uint256.Int).IsUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/IsUint64.lean |
| `(*uint256.Int).IsZero` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/IsZero.lean |
| `(*uint256.Int).Log10` | FV-A | pending Janus datasym (07f71534) | pending Janus datasym (07f71534) | arm64/amd64: lean/Fv256/{Arm64,Amd64}/Log10.lean (+ L10Cases, 256 modules per ISA); table addresses come from `Extracted.dataAddr/dataSize` (no literals in statements); assumes the writable powers-of-ten tables (L10Defs.lean). Verified on master 48f3f44 with Janus 07f71534: arm64 785 s, amd64 851 s (first-of-cache excluded: framework already built) |
| `(*uint256.Int).Lsh` | FV-A | verified | verified | arm64: lean/Fv256/Arm64/Lsh.lean; amd64: machine code uses mask/SHLD idioms (`&&& (if .. then -1 else 0)`), proof not yet done (probe in wip/) |
| `(*uint256.Int).Lt` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Lt.lean |
| `(*uint256.Int).LtUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/LtUint64.lean |
| `(*uint256.Int).MarshalJSON` | FV-E | todo | todo | |
| `(*uint256.Int).MarshalSSZ` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/MarshalSSZ.lean; runtime.makeslice contract (growslice calls are inlined away: capacity is known); allocator witness inside |
| `(*uint256.Int).MarshalSSZAppend` | FV-C | partial | partial | lean/Fv256/{Arm64,Amd64}/MarshalSSZAppend.lean: PARTIAL, verified only for `len + 32 <= cap` (compiled code never calls growslice). The reallocating case calls runtime.growslice with a 1-byte element type; the pinned GrowsliceContract covers only 8-byte pointer-free elements, so that case is NOT verified (needs a growslice contract for 1-byte elements) |
| `(*uint256.Int).MarshalSSZInto` | FV-C | partial | partial | lean/Fv256/{Arm64,Amd64}/MarshalSSZInto.lean: PARTIAL, success path only (`32 <= len <= cap`); error path (fmt.Errorf) not covered |
| `(*uint256.Int).MarshalText` | FV-E | todo | todo | |
| `(*uint256.Int).Mod` | FV-B | todo | verified (+ witness) | amd64 on master 48f3f44 (FV-B, fv/wb-master 69d4089, Janus 6365855c, correctness + Witness.nonvacuous in one run, 2637 s cold; shared DivProg/SDivProg/SModProg/ChainProg libraries, spec divSpec/modSpec/sdiv/smod, y = 0 gives 0). arm64: FV-G/FV-H in progress |
| `(*uint256.Int).Mul` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Mul.lean; amd64 post allows the 16-byte stack scratch slot (OnlyWrites2) |
| `(*uint256.Int).MulDivOverflow` | FV-F | todo | verified (+ witness) | amd64 (fv/wf 32167a5, Janus 6365855c, correctness + Witness.nonvacuous in one run, 928 s; ChainProg library + UmulSum.umul_summary). Spec: value = (x*y/d) mod 2^256, flag = 1 iff x*y/d >= 2^256; x, y or d = 0 gives (0, false). Findings: d = 0 is doc-silent (spec = code); the doc's "overflow occurred in multiply process" is misleading, the flag means the quotient does not fit (doc-wording finding). arm64 todo (chain unblocked) |
| `(*uint256.Int).MulMod` | FV-F | todo | todo | |
| `(*uint256.Int).MulModWithReciprocal` | FV-F | todo | todo | |
| `(*uint256.Int).MulOverflow` | FV-A | verified | pending Janus integ/speed15 | arm64: lean/Fv256/Arm64/MulOverflow.lean (+ MoCases/A..E, one per aliasing pattern of z,x,y); verified on c7950624 (295 s). amd64: lean/Fv256/Amd64/MulOverflow.lean (+ MoCases/A..E; value via Util.mul_limbs + per-limb janus_carry, stores peeled by janus64_simp); needs the overlap fix of integ/speed15; verified on Janus 689b0f67 in 696 s full (cases on 8821a47f: A 331, B 84, C 85, D 76, E 70 s) |
| `(*uint256.Int).Neg` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Neg.lean |
| `(*uint256.Int).Not` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Not.lean |
| `(*uint256.Int).Or` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Or.lean |
| `(*uint256.Int).PaddedBytes` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/PaddedBytes.lean (+ PadCases, 33 modules per ISA) on master 48f3f44, Janus f1d61dc1 (arm64 256 s, amd64 250 s); makeslice contract hypothesis (hmk); Witness toy allocator (n = 5): nonvacuous + example fires; restatement as exists-with-contract pending repin |
| `(*uint256.Int).PrettyDec` | FV-E | todo | todo | |
| `(*uint256.Int).PutUint256` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/PutUint256.lean |
| `(*uint256.Int).Rsh` | FV-A | verified | verified | arm64: lean/Fv256/Arm64/Rsh.lean; amd64 not yet done (same idioms as Lsh) |
| `(*uint256.Int).SDiv` | FV-B | todo (needs bits.Div64 summary, U10) | verified (+ witness) | amd64 on master 48f3f44 (FV-B, fv/wb-master 69d4089, Janus 6365855c, correctness + Witness.nonvacuous in one run, 2611 s cold; shared DivProg/SDivProg/SModProg/ChainProg libraries, spec divSpec/modSpec/sdiv/smod, y = 0 gives 0). arm64: FV-G/FV-H in progress |
| `(*uint256.Int).SMod` | FV-B | todo (needs bits.Div64 summary, U10) | verified (+ witness) | amd64 on master 48f3f44 (FV-B, fv/wb-master 69d4089, Janus 6365855c, correctness + Witness.nonvacuous in one run, 2924 s cold; shared DivProg/SDivProg/SModProg/ChainProg libraries, spec divSpec/modSpec/sdiv/smod, y = 0 gives 0). arm64: FV-G/FV-H in progress |
| `(*uint256.Int).SRsh` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SRsh.lean |
| `(*uint256.Int).Scan` | FV-E | todo | todo | |
| `(*uint256.Int).Set` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Set.lean |
| `(*uint256.Int).SetAllOne` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetAllOne.lean |
| `(*uint256.Int).SetBytes` | FV-A | todo | todo | |
| `(*uint256.Int).SetBytes1` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes1.lean; verify time arm64 508s, amd64 35s on Janus c7950624 |
| `(*uint256.Int).SetBytes10` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes10.lean; verify time arm64 14s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes11` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes11.lean; verify time arm64 15s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes12` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes12.lean; verify time arm64 15s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes13` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes13.lean; verify time arm64 14s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes14` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes14.lean; verify time arm64 13s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes15` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes15.lean; verify time arm64 14s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes16` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes16.lean; verify time arm64 52s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes17` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes17.lean; verify time arm64 13s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes18` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes18.lean; verify time arm64 14s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes19` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes19.lean; verify time arm64 16s, amd64 18s on Janus c7950624 |
| `(*uint256.Int).SetBytes2` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes2.lean; verify time arm64 13s, amd64 258s on Janus c7950624 |
| `(*uint256.Int).SetBytes20` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes20.lean; verify time arm64 18s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes21` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes21.lean; verify time arm64 15s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes22` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes22.lean; verify time arm64 15s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes23` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes23.lean; verify time arm64 16s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes24` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes24.lean; verify time arm64 91s, amd64 15s on Janus c7950624 |
| `(*uint256.Int).SetBytes25` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes25.lean; verify time arm64 14s, amd64 16s on Janus c7950624 |
| `(*uint256.Int).SetBytes26` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes26.lean; verify time arm64 15s, amd64 16s on Janus c7950624 |
| `(*uint256.Int).SetBytes27` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes27.lean; verify time arm64 17s, amd64 24s on Janus c7950624 |
| `(*uint256.Int).SetBytes28` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes28.lean; verify time arm64 23s, amd64 14s on Janus c7950624 |
| `(*uint256.Int).SetBytes29` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes29.lean; verify time arm64 17s, amd64 16s on Janus c7950624 |
| `(*uint256.Int).SetBytes3` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes3.lean; verify time arm64 13s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes30` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes30.lean; verify time arm64 18s, amd64 15s on Janus c7950624 |
| `(*uint256.Int).SetBytes31` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes31.lean; verify time arm64 18s, amd64 15s on Janus c7950624 |
| `(*uint256.Int).SetBytes32` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes32.lean |
| `(*uint256.Int).SetBytes4` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes4.lean; verify time arm64 12s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes5` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes5.lean; verify time arm64 14s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes6` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes6.lean; verify time arm64 13s, amd64 12s on Janus c7950624 |
| `(*uint256.Int).SetBytes7` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes7.lean; verify time arm64 14s, amd64 13s on Janus c7950624 |
| `(*uint256.Int).SetBytes8` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes8.lean; verify time arm64 not timed (SetBytes8 arm64 predates the batch), amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetBytes9` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetBytes9.lean; verify time arm64 14s, amd64 11s on Janus c7950624 |
| `(*uint256.Int).SetFromBig` | FV-C | verified | verified | reads big.Int {neg, abs nat} layout; no runtime call |
| `(*uint256.Int).SetFromDecimal` | FV-E | todo | todo | |
| `(*uint256.Int).SetFromHex` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/SetFromHex.lean (FV-C; runtime.newobject contract); verify time arm64 672 s, amd64 82 s uncached on Janus c7950624 |
| `(*uint256.Int).SetOne` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetOne.lean |
| `(*uint256.Int).SetUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SetUint64.lean |
| `(*uint256.Int).Sgt` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Sgt.lean |
| `(*uint256.Int).Sign` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Sign.lean |
| `(*uint256.Int).SizeSSZ` | FV-C | verified | verified | lean/Fv256/{Arm64,Amd64}/SizeSSZ.lean |
| `(*uint256.Int).Slt` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Slt.lean |
| `(*uint256.Int).Sqrt` | FV-F | todo | todo | |
| `(*uint256.Int).String` | FV-E | todo | todo | |
| `(*uint256.Int).Sub` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Sub.lean |
| `(*uint256.Int).SubOverflow` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SubOverflow.lean |
| `(*uint256.Int).SubUint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/SubUint64.lean |
| `(*uint256.Int).ToBig` | FV-C | verified (+ witness) | todo | arm64 (fv/wc cfef22a, merged; Janus ffaae554, correctness + Witness.nonvacuous in one run each): ToBig arm64: premise `ImplApart Extracted.program impl`; the internal call to IntoBig goes through ofImpl / Ensures.toSummaryIn (first fully verified internal-call proof); shared lemmas IntoBigCommon. amd64 in progress |
| `(*uint256.Int).Uint64` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Uint64.lean |
| `(*uint256.Int).Uint64WithOverflow` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Uint64WithOverflow.lean |
| `(*uint256.Int).UnmarshalJSON` | FV-E | todo | todo | |
| `(*uint256.Int).UnmarshalSSZ` | FV-C | partial | partial | lean/Fv256/{Arm64,Amd64}/UnmarshalSSZ.lean: PARTIAL, success path only (`len(buf) = 32`); extracted with `--contract fmt.errorf --contract runtime.convT64 --contract runtime.newobject` (the error path is not covered: no fmt.Errorf contract exists) |
| `(*uint256.Int).UnmarshalText` | FV-E | todo | todo | |
| `(*uint256.Int).Value` | FV-C | todo | todo | |
| `(*uint256.Int).WriteToArray20` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/WriteToArray20.lean |
| `(*uint256.Int).WriteToArray32` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/WriteToArray32.lean |
| `(*uint256.Int).WriteToSlice` | FV-A | verified | verified | arm64/amd64: lean/Fv256/{Arm64,Amd64}/WriteToSlice.lean (+ WtsCases, one module per min(len,32)); master 48f3f44, Janus f1d61dc1; precondition `len <= cap` (valid slice; master slices with a cap bounds check) |
| `(*uint256.Int).Xor` | FV-A | verified | verified | lean/Fv256/{Arm64,Amd64}/Xor.lean |
| `(*uint256.Int).MulDivOverflowRem` | FV-F | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ReverseBytes` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/ReverseBytes.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 91 s / amd64 154 s) |
| `(*uint256.Int).IAdd` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/IAdd.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 358 s / amd64 157 s) |
| `(*uint256.Int).IAddMod` | FV-D | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IAddUint64` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/IAddUint64.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 143 s / amd64 151 s) |
| `(*uint256.Int).ISubUint64` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/ISubUint64.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 155 s / amd64 152 s) |
| `(*uint256.Int).ISub` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/ISub.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 61 s / amd64 161 s) |
| `(*uint256.Int).IMul` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/IMul.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 116 s / amd64 159 s) |
| `(*uint256.Int).IDiv` | FV-D | todo | verified (+ witness) | amd64 on master 48f3f44 (FV-D, fv/wd 1c20bf1, on the shared ChainProg/ModProg library; correctness + Witness.nonvacuous in one run; 2097 s cold, 8 s warm): lean/Fv256/Amd64/IDiv.lean calling DivSum/ModSum summaries; spec z' = divSpec z x, x = 0 gives 0; z and x may overlap. arm64 todo |
| `(*uint256.Int).IMod` | FV-D | todo | verified (+ witness) | amd64 on master 48f3f44 (FV-D, fv/wd 1c20bf1, on the shared ModProg library; correctness + Witness.nonvacuous in one run; 1785 s cold): lean/Fv256/Amd64/IMod.lean calling DivSum/ModSum summaries; spec z' = modSpec z x, x = 0 gives 0; z and x may overlap. arm64 todo |
| `(*uint256.Int).ISMod` | FV-D | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IMulModWithReciprocal` | FV-D | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).IMulMod` | FV-D | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISDiv` | FV-D | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ILsh` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/ILsh.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 97 s / amd64 128 s) |
| `(*uint256.Int).IRsh` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/IRsh.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 98 s / amd64 146 s) |
| `(*uint256.Int).ISRsh` | FV-D | verified + witness | verified + witness | lean/Fv256/{Arm64,Amd64}/ISRsh.lean (FV-D, fv/wd, master 48f3f44, Janus 6365855c, correctness + Witness.nonvacuous in one run; arm64 97 s / amd64 261 s) |
| `(*uint256.Int).IExp` | FV-D | todo | todo | new in master 48f3f44 |
| `(*uint256.Int).ISqrt` | FV-D | todo | todo | new in master 48f3f44 |

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

## Proof times (optimisation log)
Standing duty: every proof over ~5 min (or >2x its peers) gets a profile-and-fix pass. Times are `janus verify` wall seconds, base f65043ca vs head 9c4be184, as measured by main; "after" is filled in when a fix lands.

| item | before | after | status / plan |
|---|---|---|---|
| DivMod amd64 | 2579 s (FV-B, Janus 50db36a6) | 1884 s end to end (Janus 4d43ed7e; DivModB 926 s, dominated by janus64_run) | TOP optimisation item (heaviest proof; target < 300 s); engine work on DivModB ongoing |
| MulOverflow amd64 | > 3000 s (value closer `janus_arith` on stores not peeled) | 696 s full (cases 70-331 s) | FIXED: 16-byte stores split via janus64_simp + mul_limbs per-limb janus_carry |
| MulOverflow arm64 | > 3300 s (timeout, exit 124; case E alone OOM > 33 GB) | 295 s (closers ~20 s per aliasing case) | FIXED: cause was `refine mo_flag … <;> first \| omega \| …` running omega on the huge limb goals; now one bullet per goal |
| WriteToSlice arm64 | 429 s (old byte-store code) | 115 s on master 48f3f44 (f1d61dc1) | FIXED by the master rewrite plus closers: per-byte `Util.wbN` lemmas (clean context, no big omega), `Util.rc8_mem_byte`/`rev_byte` for the BSWAP stores. Precondition gained `len <= cap` (master's slice-bounds check panics otherwise) |
| WriteToSlice amd64 | not measured | 93 s on master | same closers (`rb8_mem_byte`); the len>=32 case now takes the generic per-byte path (master stores 4 x 8 bytes) |
| PaddedBytes arm64 | not measured | 256 s on master (cases ~100-250 s) | master's 8-byte stores: `Util.pad_big2`; makeslice clamp needs `BitVec.sub_self`/`add_sub_cancel`/`bv_add_sub_left` in `janus_run` |
| Bytes20 arm64 / amd64 | - | 37 s / 35 s | master copies through a local array; arm64 needs `Util.b20_locC`, amd64 reads are resolved by `janus64_run` |
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

## Witness audit (contract-assuming theorems), 2026-11-04
Light check by grep on every branch (`namespace Witness`, `nonvacuous`, `returns`). Janus will require a kernel-checked non-vacuity witness for each theorem that assumes runtime contracts.
* **fv/master (main):** every contract-assuming proof (Clone, NewInt, FromBig, MustFromBig, Bytes, PaddedBytes, MarshalSSZ, MarshalSSZAppend, MarshalSSZInto, UnmarshalSSZ, HashTreeRoot, SetFromBig, FromHex, MustFromHex, SetFromHex, both ISAs) has a `Witness` namespace with a firing theorem. NAMING: FromBig, MustFromBig, FromHex, MustFromHex and MarshalSSZ (both ISAs) prove the firing as `theorem returns`/`example := correctness …` and have no theorem literally named `nonvacuous`; rename or add one if Janus matches by name.
* **witness missing:** amd64 Bytes and amd64 PaddedBytes (not yet proved, so no witness yet); fv/wb `Amd64/DivMod` (WIP, no Witness); fv/wc `Arm64/IntoBigT` (WIP, no Witness); fv/wb `Clone` and `NewInt` (older copies on the branch without witnesses; main has them). Owners: FV-A (Bytes, PaddedBytes amd64), FV-B (DivMod), FV-C (IntoBig).

### Witness rule readiness (agent/speed-witness, not merged), 2026-11-04
* `tools/v.sh` and `scripts/verify-all.sh` accept `WITNESS=1`: they then also pass `--theorem Fv256.<ISA>.<Fn>.Witness.nonvacuous` for every proof that has such a theorem. Off by default until Janus accepts repeated `--theorem`.
* 180 proofs have a theorem named `Witness.nonvacuous`; 10 do not (FromBig, MustFromBig, FromHex, MustFromHex, MarshalSSZ on both ISAs): FV-C owns the conversion.
* Shape not yet checked against the final rule (statement must be `∃ …` with a conjunct for every hypothesis, contract hypotheses included): the allocation-contract proofs Clone, NewInt, Bytes, PaddedBytes (both ISAs where present) state `nonvacuous` as `CallSetup … ∧ pre` with no `∃` and without the `hnew`/`hmk` contract as a conjunct. FV-A will restate these four once the rule lands.

## Internal summaries (non-exported callees, master 48f3f44)
Not exported symbols: rows deliberately do not start with a backtick, so scripts/verify-all.sh (which reads rows starting with `| \``) skips them.
| Internal | ISA | Owner | Status | Notes |
|---|---|---|---|---|
| math/bits.Div64 | arm64 | FV-G | verified | fv/wg 38fe41e, Arm64/Div64.lean, Janus ffaae554 |
| udivremBy1 | arm64 | FV-G | verified | fv/wg 76882db, Arm64/By1.lean |
| udivremKnuth | arm64 | FV-H | verified | fv/wh 0aa9a06, Arm64/KnuthSummary.lean (16 min wall cold) |
| udivrem entry | arm64 | FV-G | conditional on hKn | fv/wg 409c8d8, Arm64/UdivremE.lean; FV-G re-verifying unconditionally. Exported arm64 Div/Mod (FV-G) and DivMod/SDiv/SMod (FV-H) in progress |

## Pending rows reported by workers (not yet merged into fv/master)
* FV-E: `Dec` amd64 (53 min) and arm64 (41 min) verified with witnesses; interim: formatBits stubbed, branch proved unreachable (base 10); re-verify without the stub after the repin to dbd8224e.
* FV-D: `ISDiv` 2501 s and `ISMod` 2898 s amd64 verified on the per-extraction chain; re-verify on the library form pending.
