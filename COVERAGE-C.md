# Coverage (family C: conversion, parsing, formatting, encoding, math/big and allocation)

Classes: (a) no runtime call, verify now; (b) needs allocator/memmove/string runtime contracts already pinned in Janus; (c) needs the dynamic-call (interface) machinery; (d) needs more than the pinned contracts (fmt/strconv/map/interface runtime) or a long chain of callees; first classification from `janus extract` on the v1.3.2 harness (Janus 83049110).

Status values: `todo`, `verified-arm64`, `verified-amd64`, `verified` (both), `blocked` (see reason).

Update (main, upstream design report DESIGN-U4-PARSE-CONTRACTS): SetFromDecimal, FromDecimal, MustFromDecimal, Scan, UnmarshalText, UnmarshalJSON need NO new contract: extract with --contract for newobject, mallocgc, memmove, memclrNoHeapPointers, gcWriteBarrier1/2/3, convTstring and ifaceeq (class (b)); full correctness incl. NumError paths is ~8-12 worker-days for SetFromDecimal, so a PARTIAL (valid-input precondition) theorem comes first and is labelled as such. U5 (UnmarshalSSZ/MarshalSSZInto) and U6 (Dec/String/Value/...) analysis pending upstream.

| Symbol | class | arm64 | amd64 | Notes |
|---|---|---|---|---|
| `uint256.FromBig` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/FromBig.lean; runtime.newobject contract + SetFromBig as callee summary; `Witness`: toy allocator + concrete call, `example := correctness ...` fires (hnew and precondition jointly satisfiable) |
| `uint256.FromDecimal` | (b) | todo | todo | fromDecimal loop + mapaccess/ifaceeq, not extractable without contracts for runtime.mapaccess2_fast32/ifaceeq |
| `uint256.FromHex` | (b) | todo | todo | newobject (z escapes) + fromHex loop; error values are globals (ErrSyntax...) in .data |
| `uint256.MustFromBig` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/MustFromBig.lean; EnsuresGo with PanicRuntime P: returns when x=nil or len<=4, else panics with the \"overflow\" eface; same Witness pattern |
| `uint256.MustFromDecimal` | (b) | todo | todo | as FromDecimal |
| `uint256.MustFromHex` | (b) | todo | todo | newobject + fromHex + gopanic(err) |
| `(*uint256.Int).CmpBig` | (a) | verified | verified | callees SetFromBig + Cmp extracted; z.Cmp(FromBig(b)) with overflow/sign handling; no runtime call |
| `(*uint256.Int).Dec` | (d) | todo | todo | strconv.FormatUint/AppendUint/formatBits + udivrem(Knuth) loops + slicebytetostring (String contract exists); ~15 functions |
| `(*uint256.Int).PrettyDec` | (d) | todo | todo | as Dec |
| `(*uint256.Int).Hex` | (b) | todo | todo | makeslice(66) + slicebytetostring (RtLive string contracts) + 64-nibble table lookups |
| `(*uint256.Int).String` | (d) | todo | todo | = Dec |
| `(*uint256.Int).Format` | (d) | todo | todo | fmt.State interface + big.Int.Format (fmt machinery); not extractable: needs convT32, sync.Pool contracts |
| `(*uint256.Int).IntoBig` | (b) | todo | todo | newobject, write barrier, big.Int.Bits/SetBits layout; needs a big.Int memory model |
| `(*uint256.Int).ToBig` | (b) | todo | todo | IntoBig + newobject |
| `(*uint256.Int).Scan` | (b) | todo | todo | type switch on interface{}, mapaccess2_fast32, ifaceeq, Exp, MulOverflow, SetFromDecimal |
| `(*uint256.Int).SetFromBig` | (a) | verified | verified | reads big.Int {neg, abs nat} layout; no runtime call |
| `(*uint256.Int).SetFromDecimal` | (b) | todo | todo | as FromDecimal |
| `(*uint256.Int).SetFromHex` | (a) | todo | todo | fromHex loop; error returns are interface values loaded from globals ErrXxx (writable .data: precondition must supply) |
| `(*uint256.Int).MarshalJSON` | (d) | todo | todo | Dec + concatbyte3 + string/slice runtime |
| `(*uint256.Int).MarshalSSZ` | (b) | verified | verified | lean/Fv256/{Arm64,Amd64}/MarshalSSZ.lean; runtime.makeslice contract (growslice calls are inlined away: capacity is known); allocator witness inside |
| `(*uint256.Int).MarshalSSZAppend` | (b) | blocked | blocked | the code calls runtime.growslice with et=uint8 (element size 1, num=8); the pinned GrowsliceContract covers only 8-byte pointer-free elements (growCap8). Needs a growslice contract for 1-byte elements (roundupsize(nextslicecap*1)); asked main |
| `(*uint256.Int).MarshalSSZInto` | (d) | todo | todo | error path calls fmt.Errorf (not extractable: sync.Pool, interfaces); success path only provable if a contract for fmt.Errorf is permitted |
| `(*uint256.Int).MarshalText` | (d) | todo | todo | Dec + stringtoslicebyte |
| `(*uint256.Int).UnmarshalJSON` | (b) | todo | todo | SetFromDecimal / UnmarshalText |
| `(*uint256.Int).UnmarshalSSZ` | (d) | todo | todo | error path fmt.Errorf; success path pure |
| `(*uint256.Int).UnmarshalText` | (b) | todo | todo | fromHex/SetFromDecimal + string(input) copies |
| `(*uint256.Int).EncodeRLP` | (c) | todo | todo | dynamic call io.Writer.Write (ItabIs / interface model), []byte literals on stack |
| `(*uint256.Int).HashTreeRoot` | (a) | verified | verified | arm64: no calls; amd64: memmove (MemmoveLive contract) |
| `(*uint256.Int).Value` | (d) | todo | todo | Dec + convTstring (interface boxing) |
