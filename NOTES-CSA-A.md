# NOTES-CSA-A (fork A of FV-CSA2): arm64 call-site conjuncts, Rt/RtLive/Makeslice/ConvT64/Errorf/ICall families

Generators (idempotent: each does `git checkout fv/wrun -- file` first, writes CallSites/<File>[.thm].lean, splices with callsite-splice.py):
- scripts/cs_rt1_a64.py   Hex (K=112,N=3), PrettyDec (K=400,N=5): slicebytetostring, H1 shape, args [0,HEAP,N]
- scripts/cs_marsh_a64.py MarshalJSON, MarshalText (nonvacuous + big): slicebytetostring + concatbyte3 | stringtoslicebyte; ptr = zp
- scripts/cs_value_a64.py Value: RtLivePre (L=[], b=0x100000) for slicebytetostring + convTstring (toy runtime RW)
- scripts/cs_ssza_a64.py  MarshalSSZAppendMain: growslice RtLivePre in BOTH witnesses; the FIRST witness runtime changed (ok = Grow's ok, implAt = growsliceSeg grA 32 64 64) since `ok = False` cannot host a call-site state
- scripts/cs_mk_a64.py    MarshalSSZ, PaddedBytes: MakesliceSite
- scripts/cs_erlp_a64.py  EncodeRLP: NewobjectSite + ICallPre (Write at A0; memory = s0.mem with 83 01 12 34 written at heap)
- scripts/cs_ssz_a64.py   MarshalSSZIntoMain, UnmarshalSSZMain: ConvT64Site + ErrorfLiveSite ([]any at sp0-56, box at BOX)
New Base.lean wrappers appended: strsIn_of, MakesliceSite, ConvT64Site, ErrorfLiveSite.
Audit: scripts/csa-q.sh arm64 ROW audit -> /srv/fv-uint256-csa-aud/q/arm64-ROW-audit.out (VERDICT line).
Rows: Hex PrettyDec MarshalJSON MarshalText Value MarshalSSZAppend MarshalSSZ PaddedBytes EncodeRLP MarshalSSZInto UnmarshalSSZ.
Verdicts: see the end of this file (updated by the final report).

## Status (FV-CSA2 fork A, handing over to FV-CSA2)
Auditor: private janus /srv/janus-csa (dba0069d), shared fwstore, 3-slot csa-q.sh queue.

| Row | Verdict |
|---|---|
| Hex | AUDIT-PASS (106 s) |
| PrettyDec | AUDIT-PASS (226 s) |
| MarshalJSON | COMPILE-ERR from fv/wrun bug, fixed 4c46a787; requeued (batchA5.sh) |
| MarshalText | COMPILE-ERR (my Or.inl bug + fv/wrun bug), fixed d1c29866; requeued (batchA6.sh) |
| Value | running in batchA4.sh, has the fv/wrun fix |
| MarshalSSZAppend, MarshalSSZ, PaddedBytes, EncodeRLP, MarshalSSZInto, UnmarshalSSZ | queued in batchA4.sh (uncompiled so far) |

Batch chain (nohup, /srv/fv-uint256-csa-aud/): batchA4.sh (PrettyDec..UnmarshalSSZ) -> q/A4.done; batchA5.sh MarshalJSON waits A4 -> q/A5.done;
batchA6.sh MarshalText waits A5 -> q/A6.done. Verdicts: q/arm64-ROW-audit.out (last line VERDICT); errors: q/arm64-ROW-audit.out.log.

Fixes found:
- fv/wrun upgrade bug (pre-existing, also check amd64 + other rows): `correctness ... ?w3 ⟨pre8, ?w5⟩` passes the separate witness conjunct
  `100 ≤ val` into correctness' pre. Fixed to `... ?w3 pre8` (MarshalJSON big, MarshalText big, Value nonvacuous; also the `⟨pre, ?w5⟩` forms).
  Done by a re.sub in cs_marsh_a64.py and cs_value_a64.py after the fv/wrun checkout.
- cs_marsh_a64.py: MarshalText's Hw has no disjunction; the sbts readiness is `⟨⟨p, _⟩, acc, acc⟩` (Or.inl/Or.inr only for MarshalJSON's two-shape Hw).
Likely spots for remaining errors: decide on StrOut/ArgsOK over big memories (EncodeRLP, SSZInto/UnmarshalSSZ), the csEr_frame/csEr_view
MemFrame chain (cs_ssz_a64.py), cost bounds by decide (Value, growslice). Rerun the generator, then scripts/csa-q.sh arm64 ROW audit.
