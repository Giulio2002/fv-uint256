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
