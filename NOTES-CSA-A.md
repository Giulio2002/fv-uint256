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

## Status at fork end
- Audited: Hex AUDIT-PASS (106 s incl. extraction+compile); Bytes (not mine) pass.
- Queued (nohup, flock queue shared with forks B/C1/C2; verdicts appear in /srv/fv-uint256-csa-aud/q/arm64-ROW-audit.out):
  batchA1.sh (Hex PrettyDec; done marker q/A1.done), batchA2.sh (MarshalJSON MarshalText Value MarshalSSZAppend MarshalSSZ PaddedBytes EncodeRLP; q/A2.done),
  batchA3.sh (MarshalSSZInto UnmarshalSSZ; q/A3.done). They start in order.
- Everything except Hex is uncompiled: expect COMPILE-ERR rounds (likely spots: decide on StrOut/ArgsOK with big memories in EncodeRLP/SSZInto, `simp only` shapes in the concat/ReadsOutside bullets
  of MarshalJSON, cost bounds `by decide` in Value/growslice). Fix = edit the generator, rerun it, requeue with scripts/csa-q.sh.
