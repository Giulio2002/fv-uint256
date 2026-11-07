# NOTES-WRUN (FV-WRUN): upgrade every fv-uint256 witness to the returning-run shape (U-WITNESS-RUN)

Worktree /srv/fv-uint256-wrun (branch fv/wrun off fv/master b3b89b7a). Lakefile pin untouched.
Janus side: UP3 branch agent/up3-vacuity at f0c6bbef (shape frozen). My private janus build: /srv/janus-wrun (detached worktree of /srv/janus-up3 repo at f0c6bbef,
`bin/janus` built there; same commit as UP3's). Scratch audit tree: /srv/fv-uint256-wrun-aud (detached; lakefile pinned to /srv/janus-up3 f0c6bbef; lean/Fv256 is
rsynced from the wrun worktree before each run). Cache: /srv/janus-ops/jcache-wrun (DELETE when done).

## Tools
- scripts/upgrade-witness-run.py FILE... : the rewriter (statement gets the Returns/GoReturns conjunct, proof gets `correctness ...`). Idempotent. Tables HINTS (main binders the
  witness replaces by literals) and EXTRA_CONJUNCTS (extension point for the coming call-reach conjunct).
- scripts/stub-correctness.py : scratch-tree only, sorry's `correctness` for fast statement-level audit runs.
