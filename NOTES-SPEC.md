# NOTES-SPEC (FV-SPEC handover)

Goal: `lean/Fv256/Spec/` = every Fv256 definition that a final `correctness` / `Witness.*` theorem STATEMENT depends on (transitively through
definitions; Janus.* / Extracted.* excluded); `lean/Fv256/Proofs/{Arm64,Amd64,Amd64v3,Common}/` = everything else. Namespaces unchanged.
Branch `fv/spec` in `/srv/fv-uint256-spec` (never pushed). `fv/spec-dry` + `/srv/fv-uint256-spec-dry` = throw-away worktree for dry runs
(`build/sync-dry.sh MSG` commits script edits on fv/spec and resets the dry worktree to it). NOT applied to fv/master.

## Tools (all under scripts/)
- `SvyTools.lean` : Lean metaprogram. Importing it makes every `theorem` body elaborate as `sorry` (statements still fully elaborated) and
  provides `#spec_closure t1 t2 ..` (Fv256 constants reachable from the TYPES, through def types+values, never through theorem values).
- `spec_survey.py --out F.json [--isa I] [FN..]` : for each verified COVERAGE row (+ Amd64v3 files) runs `janus extract` (flags from
  contract-flags.sh), builds the module's imports in a survey lake workspace (`build/spec-ws`, sorry mode, fast) and runs `#spec_closure` on
  `correctness` + every witness theorem (witness-theorems.py). Works on both layouts. Env: SPEC_WS, JANUS (default build/janus), SPEC_JANUS_PKG
  (janus lake package dir with built oleans; default lean/.lake/packages/janus), HEAVY=1, MEMCAP.
  Needs build/harness-{arm64,amd64,amd64v3} (copy from the main tree) and build/janus.
- `leansplit.py` : top-level command splitter for column-0 Lean (comments/strings aware, doc comments and `open X in` glued).
- `restructure.py [--closure F.json]` : idempotent (no-op when lean/Fv256/Proofs exists; needs a clean tracked tree). Plans per module:
  whole-move to Spec/, split (spec decls + all context commands -> Spec file, rest -> Proofs file importing the Spec file), or Proofs only;
  git mv; rewrites imports; rewrites paths in scripts/tools/docs; regenerates the TB modules (gen-tb-intobig*.sh are rewritten to process both
  Spec/ and Proofs/ parts); writes umbrella lean/Fv256/Spec.lean (Extracted-free spec modules) and updates lean/Fv256.lean.
  Module mapping: Fv256.Spec -> Fv256.Spec.Core, Fv256.SpecX -> Fv256.Spec.X, Fv256.{Arm64,Amd64}.M -> Fv256.Proofs.{..}.M (spec part
  Fv256.Spec.{..}.M), other Fv256.M -> Fv256.Proofs.Common.M (spec part Fv256.Spec.M).
- `check-spec-closure [--closure F.json]` : release check (see its header). FAILS if a statement reaches a Fv256 constant outside Fv256.Spec.*,
  or a Spec module imports a non-Spec Fv256 module.

## Facts learned
- Survey on fv/master 91de910 (old layout): 293 theorem rows (146 symbols x 2 ISAs + v3), 539 closure constants (536 defs, 3 aux proof terms),
  156 modules involved; survey takes ~30 min total (sorry mode, one lean at a time).
- Line numbers: the survey injects `import SvyTools ` on the first import line (same line!) so declaration ranges equal the original file lines.
- TB/FM modules (IntoBig re-targeted at ToBig/Format extraction) define their own copies of IntoBigDefs; their defs are in ToBig/Format
  statements, so the generators must produce the Spec/ part too (done for TB; FM generators are archival, only path-rewritten).
- Generators under tools/ are historical; paths/imports in them are rewritten best-effort, not re-tested.

## STATUS: PARKED (2026-11-08). fv/spec2 = restructure of fv/master 47243a67; NOT merged; re-run on the final fv/master when main calls.
Re-run recipe (on a fresh branch from the final fv/master, in a new worktree):
1. copy scripts/{SvyTools.lean,spec_survey.py,leansplit.py,restructure.py,check-spec-closure} from fv/spec2; build/harness-* (hash-checked) and build/janus = the pinned binary
   (/srv/janus-fvA-pin51d/bin/janus for pin 51d592da); lean/.lake/packages/janus -> a janus package dir with built oleans.
2. `SPEC_WS=$PWD/build/spec-ws SPEC_JANUS_PKG=<janus pkg> JANUS=$PWD/build/janus python3 scripts/restructure.py --survey-out build/spec-closure-pre.json`  (~35 min), commit.
3. `RELEASE=1 scripts/no-sorry.sh` (runs the full check-spec-closure, ~30 min), then verify-all on the new layout.
New files (witnesses, fv/inh ...) need no manual handling: the survey picks them up.

## Dry-run results on fv/spec2 (fv/master 47243a67, pin 51d592da, fresh cache)
- check-spec-closure, 293 rows: OK; 156 spec modules, 536 defs, 553 consts. RELEASE=1 no-sorry: OK.
- verify-all: Add arm64 PASS 731 s / amd64 PASS 31 s; Format amd64 PASS 1462 s; Scan arm64 PASS 1440 s (10 witnesses);
  Format arm64 FAIL = leanchecker kernel replay of Proofs.Arm64.By1Math hit the 24 GiB cap (resource limit, known pre-n11, expected fixed by n11 closure replay);
  Scan amd64 aborted by me (killed to free capacity, not a proof failure); SetFromDecimal and UnmarshalJSON not run.
- Full-rebuild estimate: restructure 35 min + closure check 30 min + verify-all of the whole tree as before (the layout adds no proof work; only module paths changed).
