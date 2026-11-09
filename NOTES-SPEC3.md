# NOTES-SPEC3 (progress log; successor: read this first)
Goal (main, 2026-11-09): restructure the FINAL fv tree (fv/wrun 9569cd95) into lean/Fv256/Spec/ (statement closure) + lean/Fv256/Proofs/{Arm64,Amd64,Amd64v3,Common}.
Branch fv/spec3, worktree /srv/fv-uint256-spec3 (from 9569cd95). Do NOT push. Trailer: Co-Authored-By: Claude Sonnet 5.5 <noreply@anthropic.com> (main agreed).
Prior art: /srv/fv-uint256-spec2 (fv/spec2) = same tooling on an older master; /srv/fv-uint256-spec/NOTES-SPEC.md has the tool descriptions.

## Setup done
- build/harness-* (hash OK), build/janus = /srv/janus-wrun8/bin/janus (8b12261b), build/janus-pkg = copy of wrun's lean/.lake/packages/janus (8b12261b, oleans built); lean/.lake/packages/janus -> build/janus-pkg.
- env for every survey/check: SPEC_WS=$PWD/build/spec-ws SPEC_JANUS_PKG=$PWD/build/janus-pkg JANUS=$PWD/build/janus
- Tooling committed on fv/spec3: scripts/{restructure.py,leansplit.py,check-spec-closure,test-spec-lints.sh,gen-layout.py}; spec_survey.py/SvyTools.lean now also record statement hashes ('stmt' per row, @@T lines).
- gen-layout.py: generators scripts/gen-*.sh stay UNCHANGED; they run on a legacy-layout view built from Spec+Proofs parts (scripts/layout-map.json, written by restructure), output is split back (by qualified name in the spec closure) into Spec/ and Proofs/ {Arm64,Amd64}/{TB,FM}. check-generated.sh gets a branch calling `gen-layout.py check`.
- restructure.py (changed vs spec2): TB/FM modules are not moved, they are git-rm'd and regenerated; layout-map.json; tactic-whitelist.txt paths+hashes updated (build/whitelist-moves.json lists IMPORT-LINES-ONLY vs CONTENT-CHANGED(split) per file: review); scripts/gen-* excluded from path rewriting.

## Steps / state
1. [running/was started 02:49] pre-restructure survey: `python3 scripts/spec_survey.py --out build/spec-closure-pre.json` (log build/survey-pre.log) -> done when the json exists.
2. `python3 scripts/restructure.py --closure build/spec-closure-pre.json` then commit.  (clean tracked tree required)
3. Debug until: python3 scripts/lint_source.py OK; python3 scripts/check-spec-closure --structure-only OK; scripts/check-generated.sh OK; scripts/test-lints.sh, test-spec-lints.sh OK.
4. Gates (heavy-run, one heavy job at a time, load<=62, MemAvailable>=60G, disk>=60G):
   - `RELEASE=1 JANUS=/srv/janus-wrun8/bin/janus scripts/no-sorry.sh` under /srv/janus-ops/bin/heavy-run, `timeout 14400` (4 h); includes check-spec-closure + check-generated + check-lean-lint.
   - audit-only sweep of all 292 rows with Janus 8b12261b, 4 workers, memcap per scripts/memcap-overrides.txt (find the audit-only flag in scripts/rowrun.sh / csa-*.sh / verify-all.sh).
   - real verify sample: arm64 Add, amd64 Format, arm64 MustFromDecimal, amd64 AddMod.
   - statement identity: compare 'stmt' hashes of every root between build/spec-closure-pre.json and the post survey (check-spec-closure's json build/spec-closure-check.json): must be identical.
5. Commit, do not push; report head + gate results + folder layout to main.

## Log
- 02:49 survey started (pid 1847463).
- 03:5x survey done (293 rows, no errors); restructure applied+committed: fv/spec3 66e66385 (156 spec modules + 4 generated Spec TB/FM parts; 8 whitelisted files CONTENT-CHANGED(split) = they lost spec defs, hashes updated; others import-lines only). lint_source (RELEASE) / structure-only / check-generated OK.
- NEXT: full `python3 scripts/check-spec-closure --index build/spec-index.md` (post survey, writes build/spec-closure-check.json), compare 'stmt' hashes vs build/spec-closure-pre.json; then gates in step 4.
