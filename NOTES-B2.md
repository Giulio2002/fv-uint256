# NOTES-B2 (SPEC-B2, batch Cmp..Log10)
- Branch fv/spec-b2. Generator: /srv/janus-ops/spec-b2-equiv/gen.py (--proofs --claims --equiv); equiv run: /srv/janus-ops/spec-b2-equiv/run.sh (appends equiv, verifies amd64 then arm64, restores; marks in build/equiv.marks, outputs build/equiv-<isa>.out).
- Spec/Core.lean: removed the 15 moved defs (isZero eq lt gt cmp uint64 isUint64 sign signed slt sgt uint64Ov bitLen byteLen byte), added imports.
- New shared pure file Spec/Signed.lean (signed). CmpUint64/LtUint64/GtUint64 have no def of their own (use cmp/lt/gt).
- Scripts patched (separate commit): Amd64v3 claim-file support (verify-all, check-spec-closure, spec_survey).
- Status: step1 commit b29bd807; running equiv+verify. Then: restore, final clean verify, make build, lint, check-spec-closure, rm jcache.
