# NOTES-CSB (FV-CSB) handover, amd64 call-site conjuncts (U-WITNESS-CALLSITE)

Branch fv/csb (worktree /srv/fv-uint256-csb) off fv/wrun e99fa921. Janus pin: /srv/janus-csb (detached 8615b09c, bin/janus + janus-audit built).
Scratch audit tree /srv/fv-uint256-csb-aud (lean/ synced by crow2.sh from the worktree), cache /srv/janus-ops/jcache-csb (DELETE at end),
JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore (crow2.sh). Row runner: `HEAVY_PRIORITY=1 heavy-run -- timeout 3000 ./crow2.sh FN [audit|full]`.
Rule learned: complex rows take state from core modules; the cs conjunct goes in each core's exists-statement AND the wrapper's (obtain/exact).

## Done in the worktree (written, NOT yet compiled/audited)
- Extracted-free helpers: lean/Fv256/Amd64/CallSites/{Base,Live}.lean (compile clean with plain lean).
- scripts/cs-newobject.py applied: Bytes Clone NewInt FromBig FromHex MustFromBig MustFromHex (csNew); DivMod (csNewW in DivModW); EncodeRLP (csNew + csW via callSt64At).
- IntoBig, ToBig: csNew/csW1/csW2 (rsp = s0.rsp-32).
- scripts/cs_live_gen.py + cs-live-apply.py (`--core T.. --wrap W..`): Live family block (new, mallocgc, memmove, wb1, wb2, cmpstring, ifaceeq, [sbts]); applied to SetFromDecimal (cfg sfd).
## TODO
Wire: FromDecimal/MustFromDecimal (afd cfg, core AFdWitC/AMFdWitC + wrapper), UnmarshalText/JSON (ut/uj; core + wrapper), Scan (shared ScanWitC), Format (12 contracts, ICall states via callSt64At), RtContract64 rows (Dec Hex MarshalJSON MarshalText PrettyDec String), RtLive (MarshalSSZAppend, Value), ConvT64/ErrorfLive (MarshalSSZInto, UnmarshalSSZ), Makeslice (MarshalSSZ, PaddedBytes), TypeAssert (Format).
Then rebase onto fv/wrun, audit all rows, full verifies (IntoBig Format SetFromDecimal Scan UnmarshalJSON), timings, report to main + FV-A2.

## Status update (handover complete as of this commit)
Wired (written, UNCOMPILED, UNAUDITED): Bytes Clone NewInt FromBig FromHex MustFromBig MustFromHex DivMod(+DivModW) EncodeRLP IntoBig ToBig SetFromDecimal.
Pending: FromDecimalMain/MustFromDecimalMain (cores AFdWitC/AMFdWitC + wrapper; cfg 'afd' R2=(R3 TW), b=0x400), UnmarshalTextMain (cores AUtWitC nonvacuous_core/hex_core; cfg 'ut', b=bW),
UnmarshalJSONMain (AUjWitC nonvacuous_core/unq_core; needs cfg 'uj' like 'ut' with sb p=0x301000 or pQ+1), Scan (ScanWitC shared; 5 witnesses in Scan.lean; sb cfg without the p-disjunct; mv ok args order q p sl),
Format (big/nil/nonvacuous; 12 contracts: NewobjLive, Wb1/2, RtContract64 x2, TypeAssert, ICall x6; ICall states via Fv256.Inhab.callSt64At + callSt64At_pre, see EncodeRLP.lean csW),
RtContract64 rows Dec Hex MarshalJSON MarshalText PrettyDec String, RtLive (MarshalSSZAppend x2, Value), ConvT64/ErrorfLive (MarshalSSZInto, UnmarshalSSZ), Makeslice64 (MarshalSSZ, PaddedBytes).
Wiring pattern: add `--core` theorems (statement conjuncts before `RetAddr`; proof terms before first `hret` after `:=`); wrappers via `--wrap` (adds cs1..csN before `hret, hsetup` in the obtain and the exact).
Known fragile spots in generated proofs (expect compile errors): `by decide` on goals containing Outside/StackGuardOK (need `simp only [outside_cons, outside_nil]` or `unfold stackguard0 stackguard0Offset regG regSP`), RTPre/EqPre in csIf/csMv, csSb_pre (RtLivePre64 unfolds), csMv LiveDest component order.
## Run commands
cd /srv/fv-uint256-csb-aud; HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout 3000 ./crow2.sh IntoBig audit > run-X.out 2>&1   (log: build/log-amd64-X; wait for the ENDMARK you echo yourself)
crow2.sh syncs lean/Fv256 from /srv/fv-uint256-csb, extracts with build/harness-amd64, and runs janus verify with --janus-root /srv/janus-csb. Use crow.sh->crow2.sh (fwstore). A baseline IntoBig audit (no conjunct) launched 00:00 on the old crow.sh was still running (cold framework); its log build/log-amd64-IntoBig shows the auditor's exact expected conjunct texts: compare with ours.
Extracted-free lean check: LEAN_PATH=/srv/janus-csb/.lake/build/lib/lean:/srv/fv-uint256-csb-aud/scratch/olean lean FILE -o scratch/olean/<mod>.olean.
Delete /srv/janus-ops/jcache-csb at the end. Never push.

## Baseline IntoBig audit result (crow.sh, cold, 00:00-00:23): rc=1 after 1384 s, but build/log-amd64-IntoBig holds ONLY the extraction output (no verify/auditor text was captured). Cause unknown (verify stderr lost, or heavy-run/memcap exit). The successor must rerun with crow2.sh and capture output (e.g. add `2>&1 | tee`) and check `dmesg`/memcap for an OOM kill. The cold framework build (~20 min) is now in jcache-csb; fwstore not populated by this run.

## IMPORTANT audit finding from FV-CSA (on 8615b09c), UNVERIFIED by me
A call-site conjunct whose pre is a multi-part `A ∧ B ∧ C` is rejected even with the exact text: the auditor flattens the witness into [pc, A, B, C] but calls `findConj (And A B)` on the WHOLE pre, so only a pre that is ONE conjunct matches (WriteTo's single ICallPre works).
Proposed workaround (FV-CSA is testing it; confirm with them): wrap each multi-part pre in an `@[reducible] def` (e.g. `NewSite R addr stack L b s := NewobjectPre64 stack s ∧ StackRoom64 s stack 1 ∧ LiveAt ...`) and write the conjunct as `∃ Lc bc s_c, s_c.rip = ofNat addr ∧ NewSite ...`.
My generated conjuncts (Live block, csNew-type ones with two-part pre such as `NewobjectPre64 ∧ Ready64`, ifaceeq, memmove, IntoBig/ToBig, EncodeRLP newobject) use the multi-part form, so they must be changed to the wrapped-def form if the workaround is confirmed. Audit-only takes ~25 s once fwstore is warm.

## CONFIRMED by FV-CSA (arm64 IntoBig/NewInt audit pass): the `@[reducible] def ...Site` wrapper is REQUIRED for multi-part pres.
Also: closed `L := []`, `b := 0x400` inside the pre works (no `∃ L b` needed). Their wrappers: lean/Fv256/Arm64/CallSites/Base.lean on branch fv/csa (NewobjectSite, NewobjectLiveSite, MallocgcLiveSite, MemmoveLiveSite, WbLiveSite, IfaceeqSite) and scripts/cs-apply-*.sh: port to amd64 (rip, R14, calleeStack64) into lean/Fv256/Amd64/CallSites/Base.lean, then change cs_live_gen.py / cs-newobject.py / IntoBig / ToBig / EncodeRLP conjuncts to `∃ s_c, s_c.rip = ofNat addr ∧ XSite ... s_c`.
Lean gotcha (FV-CSA): `{ s0 with a := .., b := .. }` over two fields on separate lines gave a parse error; use two-step defs.
