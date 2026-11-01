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
| `(*uint256.Int).Hex` | (b) | todo | todo | makeslice(66) + slicebytetostring (RtLive string contracts) + 64-nibble table lookups |
| `(*uint256.Int).String` | (d) | todo | todo | = Dec |
| `(*uint256.Int).Format` | (d) | out of scope | out of scope | math/big Format through a dynamic fmt.State (interface calls into fmt/strconv/big): not provable at reasonable cost (upstream analysis DESIGN-U5-U6) |
| `(*uint256.Int).IntoBig` | (b) | todo | todo | newobject, write barrier, big.Int.Bits/SetBits layout; needs a big.Int memory model |
| `(*uint256.Int).ToBig` | (b) | todo | todo | IntoBig + newobject |
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
