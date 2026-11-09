# NOTES-B1 (batch 1 arithmetic core) -- delete at merge
Branch fv/spec-b1 (base 8686a57d), worktree /srv/fv-spec-b1. Generators in scratchpad /tmp/claude-0/-root/b301f400-a150-4f15-8f32-0b73b1894423/scratchpad: gen_claims.py (20 simple rows), gen_rt.py (NewInt, Clone), gen_equiv.py (old<->new Iff.rfl blocks -> equiv/*.blk), v.sh (verify wrapper).
Done: Spec/<Fn>.lean x22 (+ pure-spec.txt), Core.lean defs removed + imports added (per Amendment), Proofs renamed (correctness_proof, Wit), Spec/Amd64/{15 files} + Spec/{Amd64,Arm64}/{NewInt,Clone} deleted (Alias moved into proof files, intType moved into Proofs), claim files generated for both ISAs.
Pending: verify rows, fix failures, equivalence runs, make build, lint, closure, commit.
Not touched: scripts/layout-map.json mentions deleted Spec/Amd64 modules (scripts are off limits).

## Status: DONE (all gates green)
verify-all PASS both ISAs 22/22 (build/keep/run-arm64all.out, run-amd64final.out), equivalence Iff.rfl 44/44 (run-equiv-*.out), make build OK, lint OK, check-spec-closure 44 rows OK.
Equiv generator: scratchpad gen_equiv.py (add to harness row list: Fns above, blocks appended temporarily to claim files).
