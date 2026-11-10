# NOTES-B4 (SPEC-B4 progress; delete at merge)
Batch: Mul MulOverflow IMul DivMod Mod SDiv SMod IDiv IMod ISDiv ISMod Reciprocal (both ISAs). Worktree /srv/fv-spec-b4, branch fv/spec-b4.
Generators (hand templates): /srv/janus-ops/spec-b4/{genclaims.py,gen2.py,gen3.py} write lean/Fv256/{Amd64,Arm64}/<Fn>.lean.
Equivalence: /srv/janus-ops/spec-b4/equiv.py apply|restore  (appends `section OldEquiv` with Iff.rfl to claim files; originals backed up in /srv/janus-ops/spec-b4/orig). MUST restore before commit.
Status: Specs written (12), Proofs renamed (correctness->correctness_proof, Witness->Wit), claims generated, Core.lean edited (Spec.mul moved to Spec/Mul.lean; imports it).
TODO: lake build, verify-all rows (JANUS_CACHE_DIR=/srv/janus-ops/jcache-spec-b4, ALLOW_WARM_CACHE=1 SKIP_HARNESS=1), fix claim errors, lint, check-spec-closure, commit.
Progress (17:5x): PASS (with Iff.rfl equivalence appended): arm64 Mul IMul MulOverflow Reciprocal; amd64 Mul IMul MulOverflow. Reciprocal needs real bridge (post_bridge/post_unbridge in Proofs/*/Reciprocal.lean, equiv proved by ensures_mono_post).
Running chain: a5 amd64 DivMod; a6 arm64 DivMod; then a7 amd64 {Reciprocal Mod SDiv SMod IDiv IMod ISDiv ISMod}; a8 arm64 {Mod..ISMod}. Logs build/v-<tag>.out, build/log-<isa>-<Fn>. Equiv sections are APPLIED in claim files: run `python3 /srv/janus-ops/spec-b4/equiv.py restore` BEFORE committing (restores originals from /srv/janus-ops/spec-b4/orig; restore now STRIPS the section (no orig copy needed)).
Commit 5423e74b (WIP, equiv stripped via temp index; worktree still has OldEquiv sections applied for running rows). Commit trick: GIT_INDEX_FILE=/srv/janus-ops/spec-b4/tmpidx, strip sections, update-index.
a9 queued: amd64 DivMod after a7; a8 (arm64 Mod..ISMod) waits for a6 (arm64 DivMod, old claim w/o heartbeat opt; rerun if FAIL)
a10 queued arm64 DivMod after a8
20:05 PASS: amd64 ISMod (3451s), arm64 ISMod (1509s) with equiv.
20:35 PASS amd64 IMod IDiv, arm64 IMod
21:00 PASS amd64 Reciprocal, arm64 IDiv
21:20 PASS amd64 Mod, arm64 Mod. Pending: SDiv SMod ISDiv (both), then DivMod (a9 amd64, a10 arm64 with heartbeat fix)
21:50 PASS SDiv both, arm64 SMod. Pending amd64 SMod, ISDiv both, DivMod both
22:10 a8 done: arm64 Mod SDiv SMod IDiv IMod ISDiv ISMod ALL PASS. a10 arm64 DivMod running; a7 amd64 still going (SMod, ISDiv left), then a9 amd64 DivMod
22:55 commit: 22/24 PASS (all except DivMod). DivMod redone with Spec.div/mod (divMod pair .1/.2 projection caused whnf timeout, bisected in /srv/janus-ops/spec-b4/t). Running b1 arm64 DivMod, b2 amd64 DivMod.
Final: c1 arm64 + c2 amd64 clean verify of committed claims, 24/24 PASS; closure OK (43 modules); lake build + lint OK. jcache removed.
