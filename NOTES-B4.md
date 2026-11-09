# NOTES-B4 (SPEC-B4 progress; delete at merge)
Batch: Mul MulOverflow IMul DivMod Mod SDiv SMod IDiv IMod ISDiv ISMod Reciprocal (both ISAs). Worktree /srv/fv-spec-b4, branch fv/spec-b4.
Generators (hand templates): /srv/janus-ops/spec-b4/{genclaims.py,gen2.py,gen3.py} write lean/Fv256/{Amd64,Arm64}/<Fn>.lean.
Equivalence: /srv/janus-ops/spec-b4/equiv.py apply|restore  (appends `section OldEquiv` with Iff.rfl to claim files; originals backed up in /srv/janus-ops/spec-b4/orig). MUST restore before commit.
Status: Specs written (12), Proofs renamed (correctness->correctness_proof, Witness->Wit), claims generated, Core.lean edited (Spec.mul moved to Spec/Mul.lean; imports it).
TODO: lake build, verify-all rows (JANUS_CACHE_DIR=/srv/janus-ops/jcache-spec-b4, ALLOW_WARM_CACHE=1 SKIP_HARNESS=1), fix claim errors, lint, check-spec-closure, commit.
Progress (17:5x): PASS (with Iff.rfl equivalence appended): arm64 Mul IMul MulOverflow Reciprocal; amd64 Mul IMul MulOverflow. Reciprocal needs real bridge (post_bridge/post_unbridge in Proofs/*/Reciprocal.lean, equiv proved by ensures_mono_post).
Running chain: a5 amd64 DivMod; a6 arm64 DivMod; then a7 amd64 {Reciprocal Mod SDiv SMod IDiv IMod ISDiv ISMod}; a8 arm64 {Mod..ISMod}. Logs build/v-<tag>.out, build/log-<isa>-<Fn>. Equiv sections are APPLIED in claim files: run `python3 /srv/janus-ops/spec-b4/equiv.py restore` BEFORE committing (restores originals from /srv/janus-ops/spec-b4/orig; restore now STRIPS the section (no orig copy needed)).
