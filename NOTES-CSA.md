# NOTES-CSA (FV-CSA) HANDOVER — arm64 call-site conjuncts (U-WITNESS-CALLSITE)

Branch fv/csa (worktree /srv/fv-uint256-csa) off fv/wrun e99fa921. Janus pin: /srv/janus-up3 @ 8615b09c (scratch tree /srv/fv-uint256-csa-aud,
cache /srv/janus-ops/jcache-csa — DELETE at end). From now on export JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore for every run
(do NOT edit scripts/csa-row.sh while a run is live; add the export when the pilot run has ended).

## Status
- Pilot: IntoBig arm64 audit-only (STUB=1 KEEP=1) running; log /srv/fv-uint256-csa-aud/run-IntoBig-1.log (ENDMARK line at end). Cold framework build.
- Draft: lean/Fv256/Arm64/CallSites/NewInt.lean (wsNew / wsNew_pre), untested. Tools: scripts/csa-row.sh, scripts/callsite-splice.py (untested).
- Nothing spliced into witness files yet; nothing reported to main / FV-A2 yet.

## Findings
- 167 arm64 conjuncts / 41 witnesses. Families: WbLive 34, ICall 19, Rt 18, NewobjectLive 17, RtLive 13, MallocgcLive 12, MemmoveLive 12,
  Cmpstring 12, Ifaceeq 12, Newobject 9, TypeAssert 3, ErrorfLive 2, ConvT64 2, Makeslice 2.
- CORES: Format(3 witnesses), FromDecimal, MustFromDecimal, SetFromDecimal, Scan(x5), UnmarshalJSON(x2), UnmarshalText(x2) build their witness in
  *Wit*.lean `nonvacuous_core`/`nil_core` and re-pack with `obtain`; values are opaque afterwards. The conjunct must be added to the CORE's ∃ statement
  (proved there where s0/R/mem0 are concrete) and passed through the re-pack in the thin witness. Scan x5 share R/implA: one set of 8 states reused.
- Simple files (Bytes, Clone, DivMod, FromBig, FromHex, MustFromBig, MustFromHex, NewInt, EncodeRLP, Dec, Hex, String, PrettyDec, MarshalJSON/Text, Value,
  MarshalSSZ*, PaddedBytes, IntoBig, ToBig) have s0, hH/pre, inv0 in-file.
- States: s_c := { s0 with pc := ofNat <entry>, sp := sp0 - K, regs := args/X28/X30 } keeping s0.mem and X28, so `hH` / `inv0` transfer
  (Ready H rt [typ] s_c = hH with sp - K, K from hH in each file: 48 mostly, Bytes 80, DivMod 160, EncodeRLP 64). Window needs: callee stack
  [sp-4096, sp+8+8n) inside the s0 stack region; sp0-16 fits n<=4.
- Live families: ∃ L b s_c; take L := [] b := 0x400 (inv0). `R.ok addr args` restricts args to the witness's own `ok` list: use its typ/args.
  cost <= b by decide (blockSize), LiveSep [] win trivial, LiveSep win R.rt by outside_cons simp + decide.
- ICall: reuse FV-INH flat memory (Fv256/InhabBase callSt/callSt_pre/strMem, ErlpInhabit/FormatInhabit as templates), tied to the witness's z/w/rt;
  rlpVal of strMem far from z reads 0.
- Rt Dec/Hex/String/PrettyDec: H0 = all args 0 -> state with zero args. MarshalJSON/Text: Hw shapes [0,p,2] / [0,1007400,1,p,2,1007400,1].
- Ifaceeq: pick X0 = 0 makes the second conjunct vacuous; RTPre R2 3 needs R2.Env s.mem g (from the witness's pre).
- Do not `decide`-test whole windows blindly; use hH-style lemmas.

## Plan
1. Read auditor's printed conjunct from pilot; fix NewInt draft; generate Newobject blocks for the 9 uniform files by script; splice; audit.
2. Rt, Makeslice, ConvT64/ErrorfLive, RtLive(Value, MarshalSSZAppend), ICall (EncodeRLP, Format), IntoBig/ToBig, then cores.
3. After FV-WRUN says compile fixes committed: rebase onto fv/wrun, splice into witness files.
4. Audit all arm64 rows (JANUS_STOP_AFTER_AUDIT=1), full verifies: IntoBig, Format, SetFromDecimal, Scan, UnmarshalJSON. Record timings. Report to main + FV-A2.
