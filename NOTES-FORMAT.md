# (*uint256.Int).Format on the icall line (fv/wgf) -- structure and interface for the three paths

Target: master 48f3f44 (conversion.go:310), NOT the v1.3.2 one-liner. Janus head: d52a1656 (static `contractAddr` callees and variable-`fn` itab callees). Spec: lean/Fv256/SpecFormat.lean (fv/wg a90074d): `Answers`/`Case` are plain defs, `fastBytes z ch` (decimal digits for d/v/s, lowercase hex without 0x for x), `nilText`, `hexBytes_digits` glue to the verified Hex spec; decimal bytes are Dec's `decBytes`.
Extraction: scripts/contract-flags.sh `Format`; amd64 13 fns / 7962 B, arm64 14 fns / 1805 words. Contracts: gcWriteBarrier1/2, newobject, slicebytetostring, growslice, gopanic, fmt.Fprint, math/big.(*Int).Format, mallocgc, memclrNoHeapPointers, memmove, typeAssert.

## Segmentation (amd64 offsets from Format's entry 0x4b1fc0; arm64 entry 0xb6030, same shape, addresses in the comments)
| seg | from -> to | content |
|---|---|---|
| prefix | +0x00 -> +0x20 | stack check, `push rbp`, `sub rsp,0x40`, spill rax,rbx,rcx,edi |
| split | +0x20 | `test rax,rax`: nil (z == 0) or not |
| (i) nil | +0x20 -> ret | nil iface check (panic if s.itab == 0), inline typeAssert cache probe (loop, miss calls runtime.typeAssert at +0x265), static call fmt.Fprint at +0x233 (arm64 0xb6290, typeAssert 0xb62c8) |
| width/prec/flags | +0x45 -> +0x114 | spills (rax->0x50, edi->0x68, rbx->0x58 rsp), Width icall (+0x5a, itab+0x28), `test bl; jne +0x1cc`, Precision icall (+0x76, itab+0x20), then Flag icalls (itab+0x18) at +0x98 (c=0x2b '+'), +0xb5 (0x20), +0xd2, +0xf2, +0x10f (c = '-', '0', '#'), each followed by a test; any true flag or hasWidth/hasPrec goes to +0x1cc |
| (ii) fast | +0x114 -> ret | `ch` switch: 'd','v','s' -> Dec (+0x140), runtime.stringtoslicebyte, Write icall (+0x169, itab+0x30) -> epilogue -> ret (+0x170); 'x' (0x78) -> Hex (+0x180), slice `[2:]` (bounds check, panicBounds if len < 2), stringtoslicebyte, Write icall (+0x1c0) -> ret (+0x1c7); other verbs -> +0x1cc |
| (iii) big | +0x1cc -> ret | zero a 8-byte slot (the big.Int result), IntoBig(z, &b) (+0x1e0, verified library), reload s and ch, static call math/big.(*Int).Format (+0x1f8), epilogue, ret |
Rule: one file per path, each a `Reaches`-style lemma from the segment's entry state with its own tiny precondition; the assembly file composes them with `seg_trans` (as for AddMod: Fv256.SegCompose / Arm64.SegCompose).

## Interface for (ii) (FV-R2): file lean/Fv256/Amd64/FormatFast.lean (arm64 twin FormatFastA64.lean)
Statement shape (a proposal, adjust to what the EncodeRLP machinery needs):
```
theorem fast (impl : List Segment) (fW fP fF fWr : Nat) (rt : List (Nat × Nat)) (z tab data ch ...)
  (hW  : ICallContract64 (Extracted.program.link impl) fW  1 stack above rt (fun _ => []) RW  PW)   -- Width()
  (hP  : ICallContract64 ... fP  1 ... RP  PP)                                                      -- Precision()
  (hF  : ICallContract64 ... fF  2 ... RF  PF)                                                      -- Flag(c)  (one contract for all five)
  (hWr : ICallContract64 ... fWr 4 ... RWr PWr)                                                     -- Write(p []byte)
  : Reaches ((Extracted.program.link impl).withExit ret) S Q
```
* S: the state at the split `+0x45` (z != 0), with the spills present, `z` readable as 32 bytes, the itab words `Fun[0..3]` equal `fF, fP, fW, fWr` (hypotheses `s.mem.readLE (tab+24+8k) 8 = fn_k` as in CountThenWrite), `CodePtrOK` of the four, `Outside` of the itab words w.r.t. `rt`, the usual stack/guard facts.
* PWr (the Write call-site obligation, proved in the lemma, not assumed): the slice (ptr,len,cap) is a fresh heap block whose bytes are `fastBytes z ch` (len = its length; ptr readable; cap >= len), receiver = `data`. This is the 'exactly these bytes' claim.
* Q: the lemma has TWO exits and must not decide the case from the existential results:
  Q S' := (S'.rip = ret ∧ FastPost) ∨ (S'.rip = bigEntry (+0x1cc) ∧ BigPre S'),
  where BigPre carries z, s (tab,data) and ch unchanged and the memory frame so far; FastPost: returned, `*z` unchanged (MemFrame), memory changed only in the stack frame and the allocator ranges and whatever the four callees may write (`rt`).
  The branch on Width/Precision/Flag results is then proved inside, for every result value, as in CountThenWrite.
  Fast-exit side conditions that the lemma has to prove: no Width/Precision/Flag result says width/prec/flag AND ch in {d,v,s,x} <-> reaches Write; else reaches bigEntry. State the iff as an extra conjunct on the final registers (e.g. record `ch` and the four booleans via the existential results `RW`,`RP`,`RF` relations).
* Dec/Hex/stringtoslicebyte: use the verified Dec/Hex summaries as library summaries (lib_summary with CodeIn), and contracts runtime.mallocgc/memmove for stringtoslicebyte (same pattern as the Dec proofs).
Open points for the engine side: the final `Q` with two exits needs `Reaches` with a disjunctive stop; if that is not expressible, split into two lemmas that share the prefix (`prefix -> Write call` under the plain-hypothesis, and `prefix -> bigEntry` under the not-plain hypothesis, each a Reaches with hypotheses on the existential results as side conditions that the lemma threads through `R`).

## Owners
(i) nil path with typeAssert, (iii) IntoBig + big.Format, final assembly: FV-G. (ii): FV-R2.
## Verdicts
Statement audit, sorry-proof `janus verify` with /srv/janus-wr-pin2/bin/janus (d52a1656 build; the /srv/janus-icall/bin/janus binary is stale, built 23:06 before 38396fec, and fails the framework identity check): amd64 Format.correctness with hypotheses typeAssert (TypeAssert at contractAddr "runtime.typeAssert"), four variable-fn ICallContract64 (Width, Precision, Flag, Write), and static ICallContract64 at contractAddr "fmt.Fprint" and contractAddr "math/big.(*Int).Format", P := True: the build and the audit stages passed; the only rejection is the axiom audit (sorryAx), as expected. So the statement shape is accepted by the auditor. (Pitfall: open only Janus.Contracts.IfaceAmd64, not Iface as well, and use Janus.Spec.Type.IfaceModel.)

## Recipes from the EncodeRLP worker (FV-R2), for whoever writes (ii)
1. Prefer two plain lemmas over one disjunctive Q: `plain` (Width/Precision/Flag results all false and ch in {d,v,s,x}) -> Write -> ret, and `notplain` -> ReachesRet to +0x1cc. The branch conditions are proved per result value by `by_cases` on the stepper's exact test form.
2. Cut every lemma at a callee return (one icall each) and pass the mid state as an abstract S1 with its facts as hypotheses; this keeps each declaration under about 200k heartbeats. Models: /srv/fv-uint256-wr/lean/Fv256/Amd64/ErlpP1b.lean, ErlpCall.lean, ErlpS1m.lean; recipes in /srv/fv-uint256-wr/NOTES-R.md (HANDOVER section at its end).
3. The Write P pin: give the engine length / strBytes / bound / accessible as separate facts, oriented `(len expr) = n`.
STATUS: (ii) is NOT started by anyone (FV-R2's context ran out before writing code). It needs a new owner.

## Plan for (iii) (FV-G): follow ToBig, do not write a library IntoBig
Machine code of the big path (amd64, from +0x1cc): `movq $0,0x28(rsp)`; `rax = 0x50(rsp)` (z), `rbx = &slot (0x28(rsp))`; `call IntoBig` (extracted at +0x1760 relative to the binary, a second function of the same extraction); then `rax = slot (the *big.Int)`, `rbx, rcx = s (itab, data)`, `edi = ch`; `call math/big.(*Int).Format` (static contract); epilogue; ret.
IntoBig has no Extracted-free library form (only the Extracted-bound proofs and their mechanical retargetings). ToBig (amd64/arm64) already does exactly this call: IntoBig is "a second function of the same extraction", proved about its own code ((Extracted.program.onlySegments [IntoBig]).link impl) by modules `Fv256.Amd64.TB.IntoBig*` that scripts/gen-tb-intobig-amd64.sh retargets mechanically at ToBig's extraction, and used as a callee summary with `Ensures.toSummaryIn`; premises are ImplApart, NewobjectLiveContract64 / WbLiveContract64 over (Extracted.program.ofImpl impl), RtInv R, blocks budget. (iii) therefore = generate `FM.IntoBig*` the same way for Format's extraction (cold compile of the IntoBig proofs is about 20 min, one-off), then a ToBig-style proof of the path with the static big.Format `ICallContract64` whose P is `BigObj mem b (val256 z)` (the verified ToBig post), and `Ensures`-level premises as in Fv256/Amd64/ToBig.lean. Re-verification of the IntoBig modules is part of every full Format verify (cost ~20 min cold).
Open design point: the premise shape (ImplApart / live contracts / RtInv R) of the whole Format theorem is then the union of ToBig's, the typeAssert contract's and the icall hypotheses; the interface model R (IfaceModel) and the RtInv R (allocator) are two different runtime models. Check early that the audit accepts both in one statement (my statement probe so far has only the IfaceModel part).
