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

# HANDOVER UPDATE (FV-CSA -> FV-CSA2), end of session 1

## KEY FINDING (auditor @ 8615b09c)
The auditor flattens the witness conjuncts (withConjs) but matches the contract's WHOLE `pre s_c` against ONE conjunct (findConj, reducible-first isDefEq).
So a multi-part pre `A ∧ B ∧ C` written inline is REJECTED (even with the exact printed text). Fix that WORKS (verified on IntoBig + NewInt, audit passes):
write the pre through a single-conjunct `@[reducible] def ...Site` (lean/Fv256/Arm64/CallSites/Base.lean: NewobjectSite, NewobjectLiveSite, MallocgcLiveSite,
MemmoveLiveSite, WbLiveSite, IfaceeqSite). Pres that are already one def application (ICallPre, RtPre, CmpstringPre n, RtLivePre) need no wrapper.
Live families: closed `L := []`, `b := 0x400` inside the pre works (no `∃ L b`; with `∃ L b` and a clashing name `b` untested/not needed).
Two-field struct update `{ s0 with a := .., b := ..}` split over lines => parse error in these files; use two-step defs (csX0, then `{ csX0 with sp := .., pc := .. }`).
Auditor's expected conjunct (IntoBig, Live shape): `pc ?s = BitVec.ofNat 64 (contractAddr "runtime.newobject") ∧ NewobjectPre 4096 ?s ∧ StackRoom ?s 4096 1 ∧ LiveAt R addr [(?s.regs 0).toNat] ?L ?b (newobjectRound ?s) (?s.regs 28).toNat ?s.mem (calleeStack ?s 4096 1)`.
Bare (NewInt): `pc ?s = ofNat 64 addr ∧ NewobjectPre 4096 ?s ∧ Ready H rt [(?s.regs 0).toNat] ?s`.

## AUDIT RESULT: arm64 IntoBig PASSES the audit stage with the call-site conjuncts (NewobjectLive + WbLive x2, STUB=1): the only remaining
errors are `depends on disallowed axioms: sorryAx` from the stubbed correctness (axiom stage, after theorem audit). Same for NewInt. FULL (non-stub) IntoBig verify was
started (log /srv/fv-uint256-csa-aud/run-IntoBig-full.log, ENDMARK line at end; result unknown at handover). Audit-only run = ~25 s with fwstore; cold pin build was 1251 s.

## Wired rows (committed on fv/csa; compile verified only where stated)
- IntoBig (3 conj): CallSites/IntoBig.lean; scripts/cs-apply-intobig.sh; compiles stubbed (lake env lean in kept workspace) and audit passes.
- NewInt (1): CallSites/NewInt.lean; audit passes (stub).
- Generated, NOT yet compiled/audited: Bytes Clone FromBig FromHex MustFromBig MustFromHex DivMod (scripts/cs_newobj_a64.py FILE..); Dec String (scripts/cs_rt0_a64.py).
  A batch audit of the 8 newobject files (STUB audit) was queued: /srv/fv-uint256-csa-aud/batch1.sh -> batch1.log (prints each ENDMARK). Dec/String not in that batch.
- TODO: Hex PrettyDec (H1: args [0,p,3] / [..] shapes), MarshalJSON MarshalText (Hw shapes), MarshalSSZ PaddedBytes (Makeslice: add MakesliceSite), Value, MarshalSSZAppendMain x2 (RtLive: RtLivePre single),
  MarshalSSZInto/UnmarshalSSZ (ConvT64 wrapper + ErrorfLive), ToBig (copy IntoBig), EncodeRLP (Newobject H [tyBig]/[tyOne] + ICall: use InhabBase callSt/strMem, see ErlpInhabit),
  and the CORES: SfdWit*/FdWit*/MFdWit*/ScanWit*/UnmarshalJSONWit*/UnmarshalTextWit* (Live block: port /srv/fv-uint256-csb/scripts/cs_live_gen.py -> arm64: pc, X28, calleeStack, *Site wrappers,
  ok-positions from each WitA `ok`; args: new numErrT(or intT/errT), mg [1,0,0], mv [zW,src,1] (k=1), cmp zero lens, ifaceeq X0=0, sb from ok), Format cores (FormatWitA/B/G/N; 12 conj each incl. ICall x6).
  Cores: add the conjunct to the core's ∃ statement (`nonvacuous_core`) AND to the thin witness's obtain/exact re-pack.

## Scripts and exact commands
- scripts/csa-row.sh ISA FN [audit|full]  (exports JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore, cache /srv/janus-ops/jcache-csa, janus-up3 pin; STUB=1 sorries correctness in the scratch tree; KEEP=1 keeps workspace)
  Run: `cd /srv/fv-uint256-csa && STUB=1 HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 3000 scripts/csa-row.sh arm64 NewInt audit`  (last line `ENDMARK ... rc=`; details in /srv/fv-uint256-csa-aud/build/log-arm64-NewInt,
  the log is APPENDED, read the tail). rc=1 with only `sorryAx` for correctness/nonvacuous in the STUB run == audit stage passed.
- scripts/callsite-splice.py FILE THEOREM --block F --conj T --proof P (inserts block before the theorem, conjunct before `Returns (`, proof term before the last `correctness `).
- Fast compile loop: kept workspace /srv/janus-ops/jcache-csa/v1/consumer/66e17e2b7775209259a6f554/5888395ee5a76d2ccb9d7c6d/root (IntoBig extraction): copy a stubbed witness to Scratch.lean, `lake env lean Scratch.lean` (~25 s).
  Base.lean compiled there to .lake/build/lib/lean/Fv256/Arm64/CallSites/Base.olean (recompile after edits: `lake env lean -o <olean> Fv256/Arm64/CallSites/Base.lean`).
- cs-apply-*.sh check out the pristine witness from `fv/wrun` (git checkout fv/wrun -- file) before splicing (idempotent). Do NOT run them on a file after committing without that checkout.
- IntoBig timings: audit cold pin framework build 1251 s; audit warm ~25 s. Full verify timings: pending.
- Open items: FV-WRUN compile fixes (rebase onto fv/wrun when told); report to main + FV-A2 (a66f673964e9e7ef5) with rows/timings; delete /srv/janus-ops/jcache-csa at the end; never push.
- FV-CSB (amd64, /srv/fv-uint256-csb) already told about the Site-wrapper finding.
