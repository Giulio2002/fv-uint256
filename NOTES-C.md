# NOTES-C (FV-C worker)
- Build dir: /srv/fv-uint256-wC (own copy of lean/.lake). Janus binary: /srv/janus-fv-uint256-janus2/bin/janus (83049110).
- Extraction of allocating functions: `--contract runtime.mallocgc --contract runtime.newobject --contract runtime.makeslice --contract runtime.growslice --contract runtime.memmove ...` as needed.
- math/big is NOT called: big.Int.Bits/SetBits/Sign are inlined; the layout of big.Int {neg bool@0, abs nat{ptr@8,len@16,cap@24}} is the only interface.
