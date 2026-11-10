# NOTES-B3 (SPEC-B3: Lsh Rsh SRsh ILsh IRsh ISRsh ExtendSign ReverseBytes Float64 Sqrt ISqrt)
Worktree /srv/fv-spec-b3, branch fv/spec-b3 (base 8686a57d). Tooling in scratchpad:
- converter: /tmp/claude-0/-root/b301f400-a150-4f15-8f32-0b73b1894423/scratchpad/gen.py <Fn...> (writes claim files, edits proofs; already run for all 11)
- equivalence harness: /srv/janus-ops/spec-equiv-b3/{gen.py,run.sh} (temporarily appends old<->new theorem to each claim; FNS env selects rows)
- verify: scripts/verify-all.sh with JANUS=/srv/janus-rel/bin/janus JANUS_CACHE_DIR=/srv/janus-ops/jcache-spec-b3 ALLOW_WARM_CACHE=1 SKIP_HARNESS=1 ROWS=2 ONLY_ISA=<isa>
Status: see git log. Edits outside own files: Spec/Core.lean (removed lsh rsh srsh extendSign + 4 imports), Proofs/Common/Util.lean line 1541 (`try`),
scripts/pure-spec.txt (appended). Real bridges: ReverseBytes (Proofs/Common/ReverseBytesBridge.lean), Float64 (Proofs/Common/Float64Bridge.lean).
Old Spec/{Amd64,Arm64}/<Fn>.lean helpers deleted; Alias / PreRaw moved into the proof files (pilot pattern).
Remaining: verify all rows, run equivalence harness, gates (make build, lint_source, check-spec-closure), report to main. Delete /srv/janus-ops/jcache-spec-b3 at end.
