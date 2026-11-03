# Coverage (family C: conversion, parsing, formatting, encoding, math/big and allocation)

Classes: (a) no runtime call, verify now; (b) needs allocator/memmove/string runtime contracts already pinned in Janus; (c) needs the dynamic-call (interface) machinery; (d) needs more than the pinned contracts (fmt/strconv/map/interface runtime) or a long chain of callees; first classification from `janus extract` on the v1.3.2 harness (Janus 83049110).

Status values: `todo`, `verified-arm64`, `verified-amd64`, `verified` (both), `blocked` (see reason).

Update (main, upstream design report DESIGN-U4-PARSE-CONTRACTS): SetFromDecimal, FromDecimal, MustFromDecimal, Scan, UnmarshalText, UnmarshalJSON need NO new contract: extract with --contract for newobject, mallocgc, memmove, memclrNoHeapPointers, gcWriteBarrier1/2/3, convTstring and ifaceeq (class (b)); full correctness incl. NumError paths is ~8-12 worker-days for SetFromDecimal, so a PARTIAL (valid-input precondition) theorem comes first and is labelled as such. U5 (UnmarshalSSZ/MarshalSSZInto) and U6 (Dec/String/Value/...) analysis pending upstream.

| Symbol | class | arm64 | amd64 | Notes |
|---|---|---|---|---|
| `uint256.FromBig` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/FromBig.lean; runtime.newobject contract + SetFromBig as callee summary; `Witness`: toy allocator + concrete call, `example := correctness ...` fires (hnew and precondition jointly satisfiable) |
| `uint256.FromDecimal` | (b) | todo | todo | fromDecimal loop + mapaccess/ifaceeq, not extractable without contracts for runtime.mapaccess2_fast32/ifaceeq |
| `uint256.FromHex` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/FromHex.lean; runtime.newobject contract + the fromHex callee summary (`SetFromHexLoops.fromHex_sum`, spec `parseHex`); preconditions: the package error variables are non-nil, outside `rt`, disjoint from the stack; `Witness`: toy allocator + concrete call on `"0x1f"`, `example := correctness ...` fires |
| `uint256.MustFromBig` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromBig.lean; EnsuresGo with PanicRuntime P: returns when x=nil or len<=4, else panics with the \"overflow\" eface; same Witness pattern |
| `uint256.MustFromDecimal` | (b) | todo | todo | as FromDecimal |
| `uint256.MustFromHex` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromHex.lean; EnsuresGo with PanicRuntime P: returns exactly when `parseHex` succeeds, otherwise panics with the eface `(itab.Type, data)` of the sentinel error (`itab+8` read from the error variable's itab: the itabs must be readable, outside `rt` and the stack); same Witness pattern as FromHex |
| `(*uint256.Int).CmpBig` | (a) | verified | verified | callees SetFromBig + Cmp extracted; z.Cmp(FromBig(b)) with overflow/sign handling; no runtime call |
| `(*uint256.Int).Dec` | (d) | todo | todo | strconv.FormatUint/AppendUint/formatBits + udivrem(Knuth) loops + slicebytetostring (String contract exists); ~15 functions |
| `(*uint256.Int).PrettyDec` | (d) | todo | todo | as Dec |
| `(*uint256.Int).Hex` | (b) | blocked U16 | todo | arm64: loop lemma (hexstep) and string/postcondition lemmas done (wip/ArmHex.lean.wip), but the base-case theorem fails the kernel check (deep recursion in the symbolic nibble-count/pointer prefix, also on Janus f65043ca); repro /srv/janus-ops/repros/U16-hex-deeprec/. No Live variant of slicebytetostring exists. |
| `(*uint256.Int).String` | (d) | todo | todo | = Dec |
| `(*uint256.Int).Format` | (d) | out of scope | out of scope | math/big Format through a dynamic fmt.State (interface calls into fmt/strconv/big): not provable at reasonable cost (upstream analysis DESIGN-U5-U6) |
| `(*uint256.Int).IntoBig` | (b) | blocked | blocked | newobject, write barrier, big.Int.Bits/SetBits layout; needs a big.Int memory model BLOCKED (U14): newobject then gcWriteBarrier2 on the same path; the second contract call needs readiness at a memory view that does not exist at entry. Provable partial paths (z == nil; *b != nil and cap >= 4) planned last. |
| `(*uint256.Int).ToBig` | (b) | blocked | blocked | IntoBig + newobject BLOCKED (U14): newobject then gcWriteBarrier2 on the same path; the second contract call needs readiness at a memory view that does not exist at entry. Provable partial paths (z == nil; *b != nil and cap >= 4) planned last. |
| `(*uint256.Int).Scan` | (b) | todo | todo | type switch on interface{}, mapaccess2_fast32, ifaceeq, Exp, MulOverflow, SetFromDecimal |
| `(*uint256.Int).SetFromBig` | (a) | verified | verified | reads big.Int {neg, abs nat} layout; no runtime call |
| `(*uint256.Int).SetFromDecimal` | (b) | todo | todo | as FromDecimal |
| `(*uint256.Int).SetFromHex` | (a) | verified | verified | lean/Fv256/{Arm64,Amd64}/{SetFromHexLoops,SetFromHex}.lean; fromHex proved as a callee summary (`fromHex_sum`: digit loop invariant over the 4 limbs, specification `parseHex` in SpecC); preconditions beyond the usual pointers: the six package error variables are non-nil and disjoint from z and the stack, enough stack for the callee (`GuardOK s 48`); Witness: `"0x1f"` parses to 31 |
| `(*uint256.Int).MarshalJSON` | (d) | todo | todo | Dec + concatbyte3 + string/slice runtime |
| `(*uint256.Int).MarshalSSZ` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/MarshalSSZ.lean; runtime.makeslice contract (growslice calls are inlined away: capacity is known); allocator witness inside |
| `(*uint256.Int).MarshalSSZAppend` | (b) | partial | partial | lean/Fv256/{Arm64,Amd64}/MarshalSSZAppend.lean: PARTIAL, verified only for `len + 32 <= cap` (compiled code never calls growslice). The reallocating case calls runtime.growslice with a 1-byte element type; the pinned GrowsliceContract covers only 8-byte pointer-free elements, so that case is NOT verified (needs a growslice contract for 1-byte elements) |
| `(*uint256.Int).MarshalSSZInto` | (d) | partial | partial | lean/Fv256/{Arm64,Amd64}/MarshalSSZInto.lean: PARTIAL, success path only (`32 <= len <= cap`); error path (fmt.Errorf) not covered |
| `(*uint256.Int).MarshalText` | (d) | todo | todo | Dec + stringtoslicebyte |
| `(*uint256.Int).UnmarshalJSON` | (b) | todo | todo | SetFromDecimal / UnmarshalText |
| `(*uint256.Int).UnmarshalSSZ` | (d) | partial | partial | lean/Fv256/{Arm64,Amd64}/UnmarshalSSZ.lean: PARTIAL, success path only (`len(buf) = 32`); extracted with `--contract fmt.errorf --contract runtime.convT64 --contract runtime.newobject` (the error path is not covered: no fmt.Errorf contract exists) |
| `(*uint256.Int).UnmarshalText` | (b) | todo | todo | fromHex/SetFromDecimal + string(input) copies |
| `(*uint256.Int).EncodeRLP` | (c) | todo | todo | dynamic call io.Writer.Write (ItabIs / interface model), []byte literals on stack |
| `(*uint256.Int).HashTreeRoot` | (a) | verified | verified | arm64: no calls; amd64: memmove (MemmoveLive contract) |
| `(*uint256.Int).Value` | (d) | todo | todo | Dec + convTstring (interface boxing) |

## IntoBig arm64: `PreX` conjuncts (precondition added to `correctness`; audit list)

`correctness` assumes `Pre R b z bp s ∧ PreX z bp s`. Every conjunct of `PreX` is a Go runtime/ABI invariant that holds for every real call, not a proof convenience. `g` = the goroutine struct in x28; `g+16` = `stackguard0`, the slot the prologue reads.

| conjunct | why it holds on every real call |
|---|---|
| `Apart bp 8 (g+16) 8` | `bp` is the address of the caller's `*big.Int` variable (stack slot or heap object). `g+16` is a field of the runtime `g` struct, a different object. `Pre` only says both are outside `R.rt`, which does not give apartness. |
| `*P.cap < 2^63` (when `z ≠ 0`, `*bp ≠ 0`) | `cap` of a Go slice is an `int`, so it is below 2^63. The machine compares it signed (`cap_slt`), so without this the `cap < 4` branch would also take negative values. |
| `Apart P 32 (g+16) 8` (same guard) | `P = *bp` is a live `big.Int` heap object (32 bytes) and the `g` struct is a different object. |
| `4 ≤ cap → Apart ap 32 (g+16) 8` | `ap` is the backing array of the `big.Int` words (heap), disjoint from `g`. |

When `*bp == 0` the freshly allocated object is separated from `g+16` by the newobject contract (`ApartAll`), so no extra assumption is needed there.
No conjunct is false for a real caller, so none needs to be proved instead.

Witness: the nonvacuous witness must instantiate `PreX` concretely, i.e. a `g` placed away from `bp`, `P` and `ap`, and `cap` as a small natural number. This is still to do and is tracked with the IntoBig Witness; the proof is `pending Janus pin 689b0f67`.

## Spec-completeness review (user clarification 2026-11-03: bug finding comes from the spec)

- `FromBig`, `MustFromBig`, `SetFromBig`, `CmpBig`: the NEGATIVE case is stated, not excluded. The sign byte is read from memory (`< 2`, not assumed 0), the value is `Fv256.C.fromBig neg abs` (negative: two's complement of `abs mod 2^256`), the overflow flag / panic depends only on the word count (`4 < len`), never on the sign. Boundary facts are kernel-checked in `SpecChecks.lean`: `fromBig true 1 = 2^256-1`, `fromBigOv 1 = false` (so `FromBig(-1)` returns `(2^256-1, false)` and `MustFromBig(-1)` does not panic: bug-hunter H-1, logged in UINT256-FINDINGS), `fromBig true (2^256-1) = 1`. Status: spec complete for the sign question.
- `SetFromHex` / `FromHex` / `MustFromHex`: SPEC INCOMPLETE. The success value is `parseHex`; on the error path the theorems give only the error value and a MemFrame, they do not say what `z` holds after a failed `SetFromHex` (the library's doc says nothing either; to be stated from the code once the intended behaviour is decided). Same for the other parsers (`SetFromDecimal`, `Scan`, `UnmarshalText`, `UnmarshalJSON` incl. `null`).
- `MarshalSSZAppend` (`len + 32 <= cap` only), `MarshalSSZInto`, `UnmarshalSSZ`: PARTIAL, spec incomplete (realloc, error paths, receiver state on error).
