# NOTES-C (FV-C worker)
- Build dir: /srv/fv-uint256-wC (own copy of lean/.lake). Janus binary: /srv/janus-fv-uint256-janus2/bin/janus (83049110).
- Extraction of allocating functions: `--contract runtime.mallocgc --contract runtime.newobject --contract runtime.makeslice --contract runtime.growslice --contract runtime.memmove ...` as needed.
- math/big is NOT called: big.Int.Bits/SetBits/Sign are inlined; the layout of big.Int {neg bool@0, abs nat{ptr@8,len@16,cap@24}} is the only interface.
- README sentence for FV-A: the "Runtime contracts assumed" line printed by `janus verify` also lists omitted UNPINNED callees (e.g. `fmt.errorf` passed with `--contract`); those are not assumptions: no code is copied for them, the statement carries no hypothesis about them, and reaching one is a `noCode` fault, so a proof that closes shows the precondition excludes that path (UnmarshalSSZ / MarshalSSZInto / MarshalSSZAppend are PARTIAL for this reason).

## Optimization duty (2026-11-02, from main)
After IntoBig arm64: profile-and-fix FromBig / MustFromBig / CmpBig arm64 (verify times base f65043ca -> head 9c4be184:
FromBig 1416 -> 735 s, MustFromBig 435 -> 276 s, CmpBig 358 -> 306 s; amd64 37-96 s). Method: `set_option profiler true` /
`trace.profiler`, fix the cause (closing lemma in post-run shape, assumptions over huge contexts, segmentation at the limb
loop), record before/after in COVERAGE-C.md. IntoBig: removed a type-mismatched closing refine retried 10x (~290 s);
Hidden-wrapper workaround costs ~143 s of failed Outside discharges (engine fix on agent/speed-s1, unmerged).
