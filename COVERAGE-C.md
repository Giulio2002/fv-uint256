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
| `(*uint256.Int).IntoBig` | (b) | verified + witness verified | todo | lean/Fv256/Arm64/IntoBig{Defs,Close,Loop,Tail,Slow3,FinF,Mid,T}.lean: `correctness` (Pre ∧ PreX → Post: BigOut value `val256 z`, normalized, cap ≥ 4, MemFrame) with the live newobject / gcWriteBarrier1/2 contracts; all paths (z nil, *b nil, cap ≥ 4 fast path, cap < 4 allocating path); no sorry; real heartbeat limits (Slow3 1M, Mid/T 4M); builds 31 s / 100 s / 124 s on speed15. PreX justified below. Witness BLOCKED on Janus: needs the live contracts (newobject, gcWriteBarrier1/2) satisfiable at the Extracted contract addresses; Janus' LiveSat only provides them for `toy.link (at0 ...)` at A0 (needs a transport lemma, cf. `Summary.of_codeIn`). pending Janus pin 689b0f67 |
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

- `FromBig`, `MustFromBig`, `SetFromBig`: documented spec (upstream issue #115, maintainer; PR #233 writes it into the doc comments): a negative `b` wraps to `b mod 2^256` (two's complement), overflow iff `|b| >= 2^256`, `MustFromBig` panics iff overflow. Stated independently of the code in `lean/Fv256/SpecBigDoc.lean` (`fromBigDoc`, `fromBigDocOv`); proved there: `fromBig_eq_doc` (the value the code computes, `Fv256.C.fromBig neg abs`, equals `b mod 2^256`, negatives included) and `fromBigOv_eq_doc` (for a normalized `big.Int`, words below 2^64 and top word non-zero, the code's "more than 4 words" flag equals `|b| >= 2^256`). The compiled-code theorems do not exclude negatives (the sign byte is read from memory, only `< 2` is assumed) and mention `fromBig`/`fromBigOv`; these two lemmas rewrite them into the documented form. Boundary checks (kernel-decided) in `SpecChecks.lean`: `FromBig(-1) = 2^256-1`, no overflow, `MustFromBig(-1)` does not panic. Status: spec complete for the sign question. TODO: restate the FromBig/MustFromBig theorems themselves in `fromBigDoc`/`fromBigDocOv` form with the normalization hypothesis.
- `SetFromHex` / `FromHex` / `MustFromHex`: SPEC INCOMPLETE. The success value is `parseHex`; on the error path the theorems give only the error value and a MemFrame, they do not say what `z` holds after a failed `SetFromHex` (the library's doc says nothing either; to be stated from the code once the intended behaviour is decided). Same for the other parsers (`SetFromDecimal`, `Scan`, `UnmarshalText`, `UnmarshalJSON` incl. `null`).
- `MarshalSSZAppend` (`len + 32 <= cap` only), `MarshalSSZInto`, `UnmarshalSSZ`: PARTIAL, spec incomplete (realloc, error paths, receiver state on error).

## IntoBig arm64 status (2026-11-03)
`IntoBigSlow3.slowHead3` (31 s), `IntoBigMid.mid` (no sorry, 92 s) and `IntoBigT.correctness` (117 s) compile on speed15 with no sorry. They still carry the diagnostic `maxHeartbeats 0` (to be replaced by a measured limit), and the Witness is not yet written. Before/after for the slow head: > 1700 s (10 leaves of omega/assumption over the post-call context) -> 31 s (leaf-free `normloop` induction plus clean-context lemmas). pending Janus pin 689b0f67.

IntoBig arm64 re-checked on the MASTER extraction (uint256 48f3f44, harness built from fv/master, contracts newobject + gcWriteBarrier1/2; only the ADRP/LDR immediates of the type descriptors and the write-barrier flag moved): the whole chain Defs, FinF, Close, Loop, Tail (498 s), Slow3 (36 s), Mid (101 s), T (123 s) compiles with rc=0, no sorry, on Janus 50db36a6 (speed15), pending 689b0f67.

## `janus verify` verdicts (private Janus 74d371be = agent/speed-livesat, workspace /srv/fv-uint256-wC-v with lake-manifest regenerated by `lake update janus` against rev 74d371be, binary built from the same rev; fv/wc rebased on fv/master 48f3f44; sandbox bubblewrap, kernel replay leanchecker, axioms Classical.choice/Quot.sound/propext)
- `(*Int).HashTreeRoot` amd64: **Verified** (`Fv256.Amd64.HashTreeRoot.correctness`, master extraction, no runtime contracts). Fix for master: the code is now a straight-line SSE copy without the memmove call, the value conjunct is plain arithmetic on the four limbs.
- `(*Int).IntoBig` arm64: **verified, witness pending** (janus verify accepts it without any non-vacuity statement; see FINDINGS/Janus policy question) (`Fv256.Arm64.IntoBig.correctness`, master extraction; runtime contracts assumed: NewobjectLiveContract@runtime.newobject, WbLiveContract@runtime.gcWriteBarrier1/2). Witness still pending (live-contract stubs of 74d371be to be used).
pending: the Janus pin used by main (the verdicts are for 74d371be).

IntoBig arm64 on Janus integ/speed15 4d43ed7e (private binary and lake rev matched, regenerated manifest, new extraction `ex-arm64-IntoBig-n` with named data constants): **Verified** `Fv256.Arm64.IntoBig.correctness` (role main theorem) and **Verified** `Fv256.Arm64.IntoBig.Witness.nonvacuous` (role WITNESS: `∃ impl R b z bp ret s`, conjuncts for the three live contracts, RetAddr, CallSetup, Pre and PreX; stubs `LiveStub.newobjectSeg/wbSeg` at the program's own contract addresses, contracts closed by `janus_live_newobject` / `janus_live_wb`; the call is `IntoBig(z, &b)` with `b == nil`). pending Janus integ/speed15.

## Master re-verification with named witnesses (Janus integ/speed15 52c7e53a, master extractions, 2026-11-04)
`janus verify` Verified for BOTH `correctness` and the named `Witness.nonvacuous` (`∃ impl rt H ... ret s`, conjuncts for the contract hypothesis, RetAddr, CallSetup and the precondition; generated by scripts/mk-witness.py) on arm64 AND amd64 for: FromBig, MustFromBig, FromHex, MustFromHex, MarshalSSZ (20/20). Hex/MustFromBig now use the extraction's named data constants in the statements: `errBase = dataAddr.«uint256.ErrEmptyString»` (the six error variables are consecutive 16-byte slots, `errVars_layout` proves the spacing and that `errAddrOf` indexes them in the tag order of `parseHex`), `tabBase = dataAddr.«.rodata#23145917»`, and MustFromBig's sentinel is `⟨dataAddr.«type:string#f88732b8», dataAddr.«.rodata#ee30ac37»⟩` (the sentinel data word is exactly the start of the "overflow" rodata object, no offset; the proof checks it). The error variables are writable `.data`, so the precondition keeps saying what memory holds there. The proof bodies still contain absolute code addresses (migrated by scripts/shift-addrs.py); TODO: express them as `Extracted.entry + k`. pending Janus integ/speed15.
