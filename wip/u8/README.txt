U8 repro: amd64 `div r9` (DIVQ, 128/64) step in udivremBy1: kernel deep recursion in the theorem by1_summary
(DivStep.lean; needs By1Loop.lean as module Fv256.Amd64.By1Loop and the extraction of
github.com/holiman/uint256.(*Int).Div for amd64, entry 'github.com/holiman/uint256.udivremBy1').
With `janus64_run [...] until [by1 + 0x46]` (stop at the div) it passes; `until [by1 + 0x49]` (execute the div) -> (kernel) deep recursion.
Fails on pinned 83049110 and on deeprec 35083b3f.
