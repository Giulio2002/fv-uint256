# Format arm64 assembly -- FV-FM (branch fv/wfm, worktree /srv/fv-uint256-wfm) -- STATE 2026-11-07

Pin: n10 51d592da (lakefile + private binary /srv/janus-wfm-n10/bin/janus). Extraction: build/ex3-arm64-Format (n10 extractor, 26 data objects, harness build/harness-arm64).
Kept workspace: build/ws-Arm64.txt; fast loop: `PRE="mods" build/lrm.sh Fv256/Arm64/File.lean` (syncs lean/Fv256 into the workspace, lake-builds PRE modules, then lean's the file).
Verify: build/vwm.sh File Theorem [extra]  (log build/vwm.log).  Do not use --keep-workspace for the final run.

## Done (lake/lean-checked in the kept workspace)
* Arm64/FormatPrefix.lean: prefix_nz (to Format+0x44) / prefix_z (to Format+0x20).
* Preserves plumbing: RPres (FormatFastDefsA64), w_call/p_call/f*_call export `RPres R2 S S'`, B/Sw big exits export `S'.mem = S.mem`,
  sites/pre_fast/fast_arm64 carry RPres to the 0x204 exit, hwR = Outside (S0.sp-stack) (stack+0x78) R2.rt.  GrabRetA64.lean = fv_ret_names_a64.
* FormatNil.lean (FV-N) repaired for n10 (fv_ret_names_a64).  FormatNilRodata.lean: "<nil>" literal facts from DataLoaded (n10 extractor).
* FormatTransfer.lean: PreF, PFL, PreCommon/PreFastE/PreFastX(HypsH)/PreBig/PreNilE, fpre_of, fx_of, nilpre_of, posts NilPost/FastPost/BigPost (BigFL).
* Format.lean: correctness (full Ensures) + Witness.nonvacuous / Witness.nil / Witness.big.  STUB: it currently imports Arm64/StubFast.lean
  (sorry'd copies of the statements of fast_arm64 and big_path) -- final step: replace the import by FormatFastAll + FormatFastBig + FormatFastHexSum
  and DELETE StubFast.lean.
* Witnesses: FormatWitA (toy ss/st runtime for lengths 2,4; zero callees; toy allocator R2; typeAssert model), FormatWitB (fast, z=16 ch='d'),
  FormatWitN (z=0), FormatWitG (big: Width callee answers X1=1).
* IntoBig FM chain regenerated (scripts/gen-fm-intobig-arm64.sh): precondition over `Pib` (the two data objects IntoBig reads), because Format's
  n10 extraction has 26 data objects and IntoBigMid timed out with fm_clear_ddisj; FormatFastBigA.call_pre takes `Pib_dataLoaded hdl`.
  Hex FM (scripts/gen-fm-hex-arm64.sh) keeps data object index 7 + fm_clear_ddisj 7.

## RESULT 2026-11-07: VERIFIED (one run, no --keep-workspace, n10 51d592da, jcache-shared, 3:06 wall after warm chain)
build/vfinal.sh -> Fv256.Arm64.Format.correctness + Witness.nonvacuous + Witness.nil + Witness.big all `verified` (log build/vfinal.log).
StubFast.lean deleted; no sorry in the arm64 Format dependency tree (scripts/no-sorry.sh still fails only on amd64 FormatFastT3.lean, from the fv/wgf merge, not in this tree).
Witnesses restated with 14 binders (fa/Rc/Rd merged, stack=4608, b0=0x400, zv literal) and a two-group conjunction: the 26-binder form exceeded pp depth and failed the audit round-trip.
Cold chain (Dec 1059 s, Hex 134 s, IntoBig FM ~750 s) is built in the kept workspace; a fresh cache needs these once.
