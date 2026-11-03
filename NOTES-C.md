# NOTES-C (FV-C worker)
- Build dir: /srv/fv-uint256-wC (own copy of lean/.lake). Janus binary: /srv/janus-fv-uint256-janus2/bin/janus (83049110).
- Extraction of allocating functions: `--contract runtime.mallocgc --contract runtime.newobject --contract runtime.makeslice --contract runtime.growslice --contract runtime.memmove ...` as needed.
- math/big is NOT called: big.Int.Bits/SetBits/Sign are inlined; the layout of big.Int {neg bool@0, abs nat{ptr@8,len@16,cap@24}} is the only interface.
- README sentence for FV-A: the "Runtime contracts assumed" line printed by `janus verify` also lists omitted UNPINNED callees (e.g. `fmt.errorf` passed with `--contract`); those are not assumptions: no code is copied for them, the statement carries no hypothesis about them, and reaching one is a `noCode` fault, so a proof that closes shows the precondition excludes that path (UnmarshalSSZ / MarshalSSZInto / MarshalSSZAppend are PARTIAL for this reason).
