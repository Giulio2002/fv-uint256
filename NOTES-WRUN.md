# NOTES-WRUN (FV-WRUN) FULL HANDOVER, written at ~320k context, 2026-11-08 ~03:15. Successor: FV-WRUN2.

Task: upgrade every fv-uint256 final-theorem witness to the Janus returning-run shape (U-WITNESS-RUN) and integrate the call-site conjunct
(U-WITNESS-CALLSITE, written by FV-CSA = arm64, branch fv/csa; FV-CSB = amd64, branch fv/csb). Worktree /srv/fv-uint256-wrun, branch fv/wrun (off fv/master b3b89b7a, lakefile pin untouched).

## Commits on fv/wrun (newest first)
- 0db3fcb1 skip witness-only pin conjuncts in correctness's pre argument (script fix; 8 files FromBig/MustFromBig/MustFromDecimalMain/MustFromHex x ISAs)
- 8a77140b parenthesize numeral substitutions `(2 : BitVec 64).toNat` (CmpBig, SetFromBig, WriteToSlice)
- 86887ba5 the Returns/GoReturns conjunct in 314 witnesses (311 by script, 2 PaddedBytes by hand, amd64 DivMod already in shape)
Re-generating from scratch (the script is idempotent only on already-upgraded text, so to re-run after a script fix do):
  for f in $(cat files.txt); do git show 86887ba5~1:$f > $f; done; python3 scripts/upgrade-witness-run.py $(cat files.txt); git checkout HEAD -- lean/Fv256/{Arm64,Amd64}/PaddedBytes.lean
  (files.txt = scratchpad list of the 292 row-files, scratchpad = /tmp/claude-0/-root/b301f400-a150-4f15-8f32-0b73b1894423/scratchpad; rows.txt has isa fn file nwit witnesses).
  NOTE: do this BEFORE merging fv/csa/fv/csb (it overwrites witness text). After they add call-site conjuncts, only hand-fix.

## Compile sweep state (stub-correctness, pin 29ff3727; pin independent)
Method: scratch trees /srv/fv-uint256-wrun-aud{,2,3,4} (own lean/Fv256 rsynced from the wrun worktree per row, `correctness` proofs replaced by `sorry` via scripts/stub-correctness.py);
row = scratchpad/arow.sh ISA FN full (STUB=1, AUD=<tree>) under heavy-run; 4 workers `sweep2.sh W LIST OUT` over scratchpad/chunk{1..4}.txt, results scratchpad/sw2-res-{1..4}.txt, per-row logs
scratchpad/sw-<isa>-<fn>.log. A row is COMPILE-OK iff the log reaches "Stage: axiom audit" (a module with a Lean error cannot; the sorryAx failures are expected). Never edit a running script (replace by mv).
Snapshot (scratchpad/res-now.txt, 226/292 classified when written; sweep still running, workers 1-4 not finished): 219 COMPILE-OK, 7 COMPILE-FAIL:
 1 arm64 SetFromBig: `2.toNat` parse error (numeral hint substituted bare) -> FIXED 8a77140b
 2 arm64 FromBig, 3 amd64 FromBig, 4 arm64 MustFromBig: Application type mismatch: `?w3` pre group starts with `pinBitVec64 pw ∧ pinBitVec64 2 ∧ ...` -> FIXED 0db3fcb1 (projection `(?w3).2.2`)
 5 arm64 MustFromDecimal: same class at MustFromDecimalMain.lean:97 (probable; recheck) -> FIXED 0db3fcb1 (unconfirmed)
 6 amd64 UnmarshalText (2787 s) and 7 amd64 MustFromDecimal (2955 s): per-row timeout (3000 s) with NO Lean error. SUSPICIOUS (coordinator flag): real verify of amd64 UnmarshalText was ~243 s,
   and `correctness` is stubbed here. The rewritten witness may force something heavy (the `correctness ...` application with `?w` holes, an `obtain` on a `*Wit*` core, a `decide`).
   Settle by timing the witness module before/after the rewrite on that one file (git show 86887ba5~1:lean/Fv256/Amd64/UnmarshalTextMain.lean vs HEAD), same stub, same cache.
   Suspects: core-mode witnesses (`obtain ⟨...⟩ := Fv256.Amd64.UtWit.nonvacuous_core` then `exact ⟨..., correctness ...⟩`): elaborating the `correctness` application against the huge
   unfolded pre may unify expensively; try passing hypotheses/pre via `(by exact h..)` or `refine`, or give `correctness` explicit named args; or the stubbed `sorry` makes decide-heavy `Witness`
   defs unavailable... also compare with old time to rule out cache/contention (load ~40 at the time, 4 parallel compiles).
RERUN LIST after the sweep ends (files changed after the sweep read them, plus failures):
 arm64+amd64: SetFromBig FromBig MustFromBig MustFromDecimal MustFromHex CmpBig WriteToSlice UnmarshalText ; (scratchpad/redo1.txt has the first six for both ISAs; add the rest)
 Command: `printf 'arm64 FromBig\n...' > redo.txt; scratchpad/sweep2.sh 1 scratchpad/redo-res.txt redo.txt` (one worker; or 4 chunks as above). Also re-verify any row whose line in sw2-res says COMPILE-FAIL.

## Environment (mine; delete at the end)
- /srv/janus-wrun (pin 29ff3727, used by the running sweep; do NOT rebuild while the sweep runs), /srv/janus-wrun2 (8615b09c), /srv/janus-wrun3 = dba0069d (UP3 auditor for the integration audit, bin/janus built:
  `cp -a .lake`, `LEAN_NUM_THREADS=8 memcap -m 24G lake build Janus.Tools.Audit janus-audit`, `CGO_ENABLED=0 /usr/local/go/bin/go build -o bin/janus ./cmd/janus`). All are detached worktrees of /srv/janus-up3's repo.
- Scratch lakefile pin of the aud trees: lean/lakefile.toml git=/srv/janus-up3 rev=<full hash> then `lake update janus` in lean/. For dba0069d use the full hash from `git -C /srv/janus-up3 rev-parse dba0069d`.
- Cache /srv/janus-ops/jcache-wrun (DELETE at end; each new pin = cold framework ~10 min + first leanchecker ~8 min); shared framework store JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore (arow.sh exports it).
- extraction uses build/harness-* copied into /srv/fv-uint256-wrun/build (hash-matched to scripts/harness.sha256); flags from scripts/contract-flags.sh.
- Newer auditor guidance: UP3b/UP3c accept both wrapper and separate call-site conjuncts (dba0069d); fv arm64 IntoBig verified there. SetFromDecimal thin-witness size-walk reject fixed at 056c9381 (included in dba0069d).

## Integration plan (next, after the redo is green)
1. FV-CSA (fv/csa, arm64) and FV-CSB (fv/csb, amd64) wrote CallSites/*.lean + conjunct insertion text on top of fv/wrun commit 8a77140b-era; they rebase onto fv/wrun after the compile fixes (0db3fcb1 or later: tell them the final hash once the redo is green).
2. Merge fv/csa then fv/csb into fv/wrun (files overlap only in the witness theorems; take theirs for call-site text, keep my Returns text); never regenerate with the script after that.
3. Switch the scratch trees to dba0069d (arow.sh: JANUS=/srv/janus-wrun3/bin/janus and `--janus-root /srv/janus-wrun3`; replace the file by mv). Audit sweep: arow.sh ISA FN audit, NO STUB (full real verify = proof check + audit),
   4 parallel workers with the same admission rule (load<40, MemAvailable>80G, 24G memcap), start with the subset (Add, Format, SetFromDecimal, Scan, UnmarshalJSON, IntoBig both ISAs), record times.
4. Timing before/after on the subset: before = fv/master files + old pin (/srv/janus-fvA-pin51d/bin/janus or the janus built from 51d592da), after = the integrated files at dba0069d; same warm cache.
5. Report to main + FV-A2 (a66f673964e9e7ef5): rows upgraded 311 script + 3 hand, audit results, timings; tell UP3b/UP3c the tree is ready for the false-reject audit; delete jcache-wrun, the janus-wrun* and fv-uint256-wrun-aud* worktrees.

## Tools in the repo
- scripts/upgrade-witness-run.py (see header; HINTS table for main binders the witness replaces by literals: CmpBig/SetFromBig len=2, Format arm64/amd64 fW fP ... stack b0 zv RW...;
  positional renames from CallSetup args; `_` for data binders only fixed by unification; pins skipped; EXTRA_CONJUNCTS hook unused), scripts/stub-correctness.py (scratch only).

## Work list (generated by the snippet in this file's history; 82 contract-bearing witnesses, 334 contract hypotheses)

Family -> witnesses. Each line = one contract hypothesis = one `(∃ s_c, s_c.pc = ofNat <entry> ∧ <family pre> s_c)` conjunct to add. Callee `runtime.x` = `Extracted.program.contractAddr "runtime.x"`.

### WbLiveContract (34)
- arm64 Format.lean `big` -- runtime.gcWriteBarrier1
- arm64 Format.lean `big` -- runtime.gcWriteBarrier2
- arm64 Format.lean `nil` -- runtime.gcWriteBarrier1
- arm64 Format.lean `nil` -- runtime.gcWriteBarrier2
- arm64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier1
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier2
- arm64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier1
- arm64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier2
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier2

### WbLiveContract64 (34)
- amd64 Format.lean `big` -- runtime.gcWriteBarrier1
- amd64 Format.lean `big` -- runtime.gcWriteBarrier2
- amd64 Format.lean `nil` -- runtime.gcWriteBarrier1
- amd64 Format.lean `nil` -- runtime.gcWriteBarrier2
- amd64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier1
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier2
- amd64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier1
- amd64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier2
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier2

### Ifaceeq (24)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.ifaceeq
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.ifaceeq
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.ifaceeq
- amd64 UnmarshalTextMain.lean `hex` -- runtime.ifaceeq
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.ifaceeq
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.ifaceeq
- arm64 UnmarshalTextMain.lean `hex` -- runtime.ifaceeq
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.ifaceeq

### ICallContract (19)
- arm64 EncodeRLP.lean `nonvacuous` -- addr: ICallContract P fn 4 stack 96 rt (fun _ => []) R (fun sc => sc.regs 0 = w ∧ StrOut sc.mem 
- arm64 Format.lean `big` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `big` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `big` -- addr: ICallContract P fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `big` -- addr: ICallContract P fa 4 4608 120 rt (fun _ => []) Rc (FastWP data (Fv256.FormatSpec.fastBytes
- arm64 Format.lean `big` -- fmt.Fprint
- arm64 Format.lean `big` -- math/big.(*Int).Format
- arm64 Format.lean `nil` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nil` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nil` -- addr: ICallContract P fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nil` -- addr: ICallContract P fa 4 4608 120 rt (fun _ => []) Rc (FastWP data (Fv256.FormatSpec.fastBytes
- arm64 Format.lean `nil` -- fmt.Fprint
- arm64 Format.lean `nil` -- math/big.(*Int).Format
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 4 4608 120 rt (fun _ => []) Rc (FastWP data (Fv256.FormatSpec.fastBytes
- arm64 Format.lean `nonvacuous` -- fmt.Fprint
- arm64 Format.lean `nonvacuous` -- math/big.(*Int).Format

### ICallContract64 (19)
- amd64 EncodeRLP.lean `nonvacuous` -- addr: ICallContract64 P fn 4 stack 56 rt (fun _ => []) R (fun sc => sc.regs 0 = w ∧ StrOut sc.me
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 2 4608 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 4 4608 80 rt (fun _ => []) RWr (FastWP data (Fv256.FormatSpec.fa
- amd64 Format.lean `big` -- fmt.Fprint
- amd64 Format.lean `big` -- math/big.(*Int).Format
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 2 4608 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 4 4608 80 rt (fun _ => []) RWr (FastWP data (Fv256.FormatSpec.fa
- amd64 Format.lean `nil` -- fmt.Fprint
- amd64 Format.lean `nil` -- math/big.(*Int).Format
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 2 4608 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 4 4608 80 rt (fun _ => []) RWr (FastWP data (Fv256.FormatSpec.fa
- amd64 Format.lean `nonvacuous` -- fmt.Fprint
- amd64 Format.lean `nonvacuous` -- math/big.(*Int).Format

### RtContract (18)
- arm64 Dec.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 Format.lean `big` -- runtime.slicebytetostring
- arm64 Format.lean `big` -- runtime.stringtoslicebyte
- arm64 Format.lean `nil` -- runtime.slicebytetostring
- arm64 Format.lean `nil` -- runtime.stringtoslicebyte
- arm64 Format.lean `nonvacuous` -- runtime.slicebytetostring
- arm64 Format.lean `nonvacuous` -- runtime.stringtoslicebyte
- arm64 Hex.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalJSON.lean `big` -- addr: RtContract P cbAddr rt 4096 H (concatbyteSpec 3)
- arm64 MarshalJSON.lean `big` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalJSON.lean `nonvacuous` -- addr: RtContract P cbAddr rt 4096 H (concatbyteSpec 3)
- arm64 MarshalJSON.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalText.lean `big` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalText.lean `big` -- addr: RtContract P stAddr rt 4096 H stringtoslicebyteSpec
- arm64 MarshalText.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalText.lean `nonvacuous` -- addr: RtContract P stAddr rt 4096 H stringtoslicebyteSpec
- arm64 PrettyDec.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 String.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin

### RtContract64 (18)
- amd64 Dec.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 Format.lean `big` -- runtime.slicebytetostring
- amd64 Format.lean `big` -- runtime.stringtoslicebyte
- amd64 Format.lean `nil` -- runtime.slicebytetostring
- amd64 Format.lean `nil` -- runtime.stringtoslicebyte
- amd64 Format.lean `nonvacuous` -- runtime.slicebytetostring
- amd64 Format.lean `nonvacuous` -- runtime.stringtoslicebyte
- amd64 Hex.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalJSON.lean `big` -- addr: RtContract64 P cbAddr rt 4096 H (concatbyteSpec 3)
- amd64 MarshalJSON.lean `big` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalJSON.lean `nonvacuous` -- addr: RtContract64 P cbAddr rt 4096 H (concatbyteSpec 3)
- amd64 MarshalJSON.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalText.lean `big` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalText.lean `big` -- addr: RtContract64 P stAddr rt 4096 H stringtoslicebyteSpec
- amd64 MarshalText.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalText.lean `nonvacuous` -- addr: RtContract64 P stAddr rt 4096 H stringtoslicebyteSpec
- amd64 PrettyDec.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 String.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu

### NewobjectLiveContract (17)
- arm64 Format.lean `big` -- runtime.newobject
- arm64 Format.lean `nil` -- runtime.newobject
- arm64 Format.lean `nonvacuous` -- runtime.newobject
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.newobject
- arm64 IntoBig.lean `nonvacuous` -- runtime.newobject
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.newobject
- arm64 ToBig.lean `nonvacuous` -- runtime.newobject
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.newobject
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.newobject
- arm64 UnmarshalTextMain.lean `hex` -- runtime.newobject
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.newobject

### NewobjectLiveContract64 (17)
- amd64 Format.lean `big` -- runtime.newobject
- amd64 Format.lean `nil` -- runtime.newobject
- amd64 Format.lean `nonvacuous` -- runtime.newobject
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.newobject
- amd64 IntoBig.lean `nonvacuous` -- runtime.newobject
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.newobject
- amd64 ToBig.lean `nonvacuous` -- runtime.newobject
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.newobject
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.newobject
- amd64 UnmarshalTextMain.lean `hex` -- runtime.newobject
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.newobject

### RtLiveContract (13)
- arm64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- arm64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 UnmarshalJSONMain.lean `unquoted` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 UnmarshalTextMain.lean `hex` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalText.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 UnmarshalTextMain.lean `nonvacuous` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalText.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 Value.lean `nonvacuous` -- addr: RtLiveContract P cvAddr 4096 R convTstringSpec convTstringLive
- arm64 Value.lean `nonvacuous` -- addr: RtLiveContract P ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticui

### RtLiveContract64 (13)
- amd64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- amd64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 UnmarshalJSONMain.lean `unquoted` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 UnmarshalTextMain.lean `hex` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 UnmarshalTextMain.lean `nonvacuous` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 Value.lean `nonvacuous` -- addr: RtLiveContract64 P cvAddr 4096 R convTstringSpec convTstringLive
- amd64 Value.lean `nonvacuous` -- addr: RtLiveContract64 P ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.static

### MallocgcLiveContract (12)
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.mallocgc
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.mallocgc
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.mallocgc
- arm64 UnmarshalTextMain.lean `hex` -- runtime.mallocgc
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.mallocgc

### MemmoveLive (12)
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.memmove
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.memmove
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.memmove
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.memmove
- arm64 UnmarshalTextMain.lean `hex` -- runtime.memmove
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.memmove

### CmpstringContract (12)
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.cmpstring
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.cmpstring
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.cmpstring
- arm64 UnmarshalTextMain.lean `hex` -- runtime.cmpstring
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.cmpstring

### MallocgcLiveContract64 (12)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.mallocgc
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.mallocgc
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.mallocgc
- amd64 UnmarshalTextMain.lean `hex` -- runtime.mallocgc
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.mallocgc

### MemmoveLive64 (12)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.memmove
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.memmove
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.memmove
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.memmove
- amd64 UnmarshalTextMain.lean `hex` -- runtime.memmove
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.memmove

### CmpstringContract64 (12)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.cmpstring
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.cmpstring
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.cmpstring
- amd64 UnmarshalTextMain.lean `hex` -- runtime.cmpstring
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.cmpstring

### NewobjectContract (9)
- arm64 Bytes.lean `nonvacuous` -- runtime.newobject
- arm64 Clone.lean `nonvacuous` -- runtime.newobject
- arm64 DivMod.lean `nonvacuous` -- runtime.newobject
- arm64 EncodeRLP.lean `nonvacuous` -- runtime.newobject
- arm64 FromBig.lean `nonvacuous` -- runtime.newobject
- arm64 FromHex.lean `nonvacuous` -- runtime.newobject
- arm64 MustFromBig.lean `nonvacuous` -- runtime.newobject
- arm64 MustFromHex.lean `nonvacuous` -- runtime.newobject
- arm64 NewInt.lean `nonvacuous` -- runtime.newobject

### NewobjectContract64 (9)
- amd64 Bytes.lean `nonvacuous` -- runtime.newobject
- amd64 Clone.lean `nonvacuous` -- runtime.newobject
- amd64 DivMod.lean `nonvacuous` -- runtime.newobject
- amd64 EncodeRLP.lean `nonvacuous` -- runtime.newobject
- amd64 FromBig.lean `nonvacuous` -- runtime.newobject
- amd64 FromHex.lean `nonvacuous` -- runtime.newobject
- amd64 MustFromBig.lean `nonvacuous` -- runtime.newobject
- amd64 MustFromHex.lean `nonvacuous` -- runtime.newobject
- amd64 NewInt.lean `nonvacuous` -- runtime.newobject

### TypeAssert (6)
- amd64 Format.lean `big` -- runtime.typeAssert
- amd64 Format.lean `nil` -- runtime.typeAssert
- amd64 Format.lean `nonvacuous` -- runtime.typeAssert
- arm64 Format.lean `big` -- runtime.typeAssert
- arm64 Format.lean `nil` -- runtime.typeAssert
- arm64 Format.lean `nonvacuous` -- runtime.typeAssert

### ErrorfLive (4)
- amd64 MarshalSSZIntoMain.lean `nonvacuous` -- fmt.errorf
- amd64 UnmarshalSSZMain.lean `nonvacuous` -- fmt.errorf
- arm64 MarshalSSZIntoMain.lean `nonvacuous` -- fmt.errorf
- arm64 UnmarshalSSZMain.lean `nonvacuous` -- fmt.errorf

### ConvT64 (4)
- amd64 MarshalSSZIntoMain.lean `nonvacuous` -- runtime.convT64
- amd64 UnmarshalSSZMain.lean `nonvacuous` -- runtime.convT64
- arm64 MarshalSSZIntoMain.lean `nonvacuous` -- runtime.convT64
- arm64 UnmarshalSSZMain.lean `nonvacuous` -- runtime.convT64

### MakesliceContract (2)
- arm64 MarshalSSZ.lean `nonvacuous` -- runtime.makeslice
- arm64 PaddedBytes.lean `nonvacuous` -- runtime.makeslice

### MakesliceContract64 (2)
- amd64 MarshalSSZ.lean `nonvacuous` -- runtime.makeslice
- amd64 PaddedBytes.lean `nonvacuous` -- runtime.makeslice

## Per witness: reusable in-file material (state s0, invariant lemmas, setup, pre, models)

- **amd64 Bytes.lean** `Amd64.Bytes.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 Clone.lean** `Amd64.Clone.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 Dec.lean** `Amd64.Dec.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 DivMod.lean** `Amd64.DivMod.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 EncodeRLP.lean** `Amd64.EncodeRLP.Witness.nonvacuous`: 2 contracts [ICallContract64, NewobjectContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Format.lean** `Amd64.Format.Witness.big`: 12 contracts [ICallContract64, NewobjectLiveContract64, RtContract64, TypeAssert, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Format.lean** `Amd64.Format.Witness.nil`: 12 contracts [ICallContract64, NewobjectLiveContract64, RtContract64, TypeAssert, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Format.lean** `Amd64.Format.Witness.nonvacuous`: 12 contracts [ICallContract64, NewobjectLiveContract64, RtContract64, TypeAssert, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 FromBig.lean** `Amd64.FromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 FromDecimalMain.lean** `Amd64.FromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 FromHex.lean** `Amd64.FromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 Hex.lean** `Amd64.Hex.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 IntoBig.lean** `Amd64.IntoBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: hret, inv0, model_new, model_wb1, model_wb2, pre, preX, rt_eq, setup
- **amd64 MarshalJSON.lean** `Amd64.MarshalJSON.Witness.big`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MarshalJSON.lean** `Amd64.MarshalJSON.Witness.nonvacuous`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MarshalSSZ.lean** `Amd64.MarshalSSZ.Witness.nonvacuous`: 1 contracts [MakesliceContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 MarshalSSZAppendMain.lean** `Amd64.MarshalSSZAppendMain.Grow.Witness.nonvacuous`: 1 contracts [RtLiveContract64]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **amd64 MarshalSSZAppendMain.lean** `Amd64.MarshalSSZAppendMain.Witness.nonvacuous`: 1 contracts [RtLiveContract64]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **amd64 MarshalSSZIntoMain.lean** `Amd64.MarshalSSZIntoMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, s0_g, s0_sp, setup
- **amd64 MarshalText.lean** `Amd64.MarshalText.Witness.big`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MarshalText.lean** `Amd64.MarshalText.Witness.nonvacuous`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MustFromBig.lean** `Amd64.MustFromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 MustFromDecimalMain.lean** `Amd64.MustFromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 MustFromHex.lean** `Amd64.MustFromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 NewInt.lean** `Amd64.NewInt.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 PaddedBytes.lean** `Amd64.PaddedBytes.Witness.nonvacuous`: 1 contracts [MakesliceContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 PrettyDec.lean** `Amd64.PrettyDec.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 Scan.lean** `Amd64.Scan.Byt.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.Nil.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.NoE.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.Other.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 SetFromDecimal.lean** `Amd64.SetFromDecimal.Witness.nonvacuous`: 7 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 String.lean** `Amd64.String.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 ToBig.lean** `Amd64.ToBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: hret, implOK, inv0, model_new, model_wb1, model_wb2, pre, rt_eq, setup
- **amd64 UnmarshalJSONMain.lean** `Amd64.UnmarshalJSONMain.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 UnmarshalJSONMain.lean** `Amd64.UnmarshalJSONMain.Witness.unquoted`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 UnmarshalSSZMain.lean** `Amd64.UnmarshalSSZMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, s0_g, s0_sp, setup
- **amd64 UnmarshalTextMain.lean** `Amd64.UnmarshalTextMain.Witness.hex`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 UnmarshalTextMain.lean** `Amd64.UnmarshalTextMain.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Value.lean** `Amd64.Value.Witness.nonvacuous`: 2 contracts [RtLiveContract64]; proof `by`; reusable: hret, pre, s0_inv, setup
- **arm64 Bytes.lean** `Arm64.Bytes.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 Clone.lean** `Arm64.Clone.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 Dec.lean** `Arm64.Dec.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 DivMod.lean** `Arm64.DivMod.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨implW,`; reusable: preW
- **arm64 EncodeRLP.lean** `Arm64.EncodeRLP.Witness.nonvacuous`: 2 contracts [ICallContract, NewobjectContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Format.lean** `Arm64.Format.Witness.big`: 12 contracts [ICallContract, NewobjectLiveContract, RtContract, TypeAssert, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Format.lean** `Arm64.Format.Witness.nil`: 12 contracts [ICallContract, NewobjectLiveContract, RtContract, TypeAssert, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Format.lean** `Arm64.Format.Witness.nonvacuous`: 12 contracts [ICallContract, NewobjectLiveContract, RtContract, TypeAssert, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 FromBig.lean** `Arm64.FromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `by`; reusable: hret, pre, setup
- **arm64 FromDecimalMain.lean** `Arm64.FromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 FromHex.lean** `Arm64.FromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 Hex.lean** `Arm64.Hex.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 IntoBig.lean** `Arm64.IntoBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: hret, inv0, model_new, model_wb1, model_wb2, pre, preX, rt_eq, setup
- **arm64 MarshalJSON.lean** `Arm64.MarshalJSON.Witness.big`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MarshalJSON.lean** `Arm64.MarshalJSON.Witness.nonvacuous`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MarshalSSZ.lean** `Arm64.MarshalSSZ.Witness.nonvacuous`: 1 contracts [MakesliceContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 MarshalSSZAppendMain.lean** `Arm64.MarshalSSZAppendMain.Grow.Witness.nonvacuous`: 1 contracts [RtLiveContract]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **arm64 MarshalSSZAppendMain.lean** `Arm64.MarshalSSZAppendMain.Witness.nonvacuous`: 1 contracts [RtLiveContract]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **arm64 MarshalSSZIntoMain.lean** `Arm64.MarshalSSZIntoMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, setup
- **arm64 MarshalText.lean** `Arm64.MarshalText.Witness.big`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MarshalText.lean** `Arm64.MarshalText.Witness.nonvacuous`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MustFromBig.lean** `Arm64.MustFromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `by`; reusable: hret, pre, setup
- **arm64 MustFromDecimalMain.lean** `Arm64.MustFromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 MustFromHex.lean** `Arm64.MustFromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `by`; reusable: hret, pre, setup
- **arm64 NewInt.lean** `Arm64.NewInt.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 PaddedBytes.lean** `Arm64.PaddedBytes.Witness.nonvacuous`: 1 contracts [MakesliceContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 PrettyDec.lean** `Arm64.PrettyDec.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 Scan.lean** `Arm64.Scan.Byt.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.Nil.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.NoE.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.Other.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 SetFromDecimal.lean** `Arm64.SetFromDecimal.Witness.nonvacuous`: 7 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 String.lean** `Arm64.String.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 ToBig.lean** `Arm64.ToBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: hret, implOK, inv0, model_new, model_wb1, model_wb2, pre, rt_eq, setup
- **arm64 UnmarshalJSONMain.lean** `Arm64.UnmarshalJSONMain.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 UnmarshalJSONMain.lean** `Arm64.UnmarshalJSONMain.Witness.unquoted`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 UnmarshalSSZMain.lean** `Arm64.UnmarshalSSZMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, setup
- **arm64 UnmarshalTextMain.lean** `Arm64.UnmarshalTextMain.Witness.hex`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 UnmarshalTextMain.lean** `Arm64.UnmarshalTextMain.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Value.lean** `Arm64.Value.Witness.nonvacuous`: 2 contracts [RtLiveContract]; proof `by`; reusable: hret, pre, s0_inv, setup

Total witnesses: 82
## Update 2026-11-08: Janus pin for the full audit sweep = UP3b auditor 056c9381 (fixes the SetFromDecimal thin-witness size-walk reject), with JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore.
Do it AFTER integrating fv/csa + fv/csb into fv/wrun. Build a janus worktree at 056c9381 (cp -a .lake from /srv/janus-wrun2, lake build Janus.Tools.Audit janus-audit, go build), bump the scratch lakefile rev.
The compile sweep (stub-correctness, pin 29ff3727, 4 parallel workers with their own scratch trees /srv/fv-uint256-wrun-aud{,2,3,4}) logs: scratchpad sw-<isa>-<fn>.log, results sw2-res-*.txt.

## Update (latest): auditor pin for the integration audit = agent/up3-vacuity dba0069d (accepts wrapper + separate call-site conjuncts; fv arm64 IntoBig verified there).
Built at /srv/janus-wrun3 (bin/janus). For the integration audit: scratch lakefile rev = full hash of dba0069d, `lake update janus`, janus=/srv/janus-wrun3/bin/janus, --janus-root /srv/janus-wrun3,
JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore (arow.sh already exports it; edit arow.sh JANUS=/srv/janus-wrun3/bin/janus and --janus-root accordingly; replace the file by mv, never edit in place while a sweep runs).
The compile sweep (stub, pin 29ff3727) is pin independent: compile errors are the same.
