# U10-fvb-div64: janus_run runs out of heartbeats on a loop-body proof (arm64 math/bits.Div64, second correction loop)

Files: Repro.lean (standalone: needs only Janus + Extracted; `hloop` stubbed), ex-arm64-Div/ (extraction with math/bits.Div64),
run.sh (builds exo/Extracted.olean, then runs lean on Repro.lean). `./run.sh [framework-lib-dir]`, env T=timeout s, OPTS=extra lean options
(e.g. OPTS="-Dtrace.profiler=true -Dtrace.profiler.threshold=1000").

Observed (pinned framework 6639dc84 / Janus 83049110, LEAN_NUM_THREADS=2): 9m37s wall, then
  error: janus_run: heartbeat budget exceeded at pc 0x8cbc8 (math/bits.Div64+0xe8) ... after 185 instructions. limit maxHeartbeats 8000000
  (deterministic) timeout at `whnf` (theorem loop2, case `zero` of the induction on qh)
(time1.log has the full output). The instructions are the loop2 body (head +0xc4, body +0xdc, exit +0xec) of Div64; the
state at the head carries 12 register equations e2..e10,e29,e30, a MemFrame, two stack-slot equations hm29/hm30 and ~10
Nat side facts (qh*yn1+rh=un21, bounds, ...).

A smaller isolated version of the same loop (fewer hypotheses: no MemFrame/hm29/hm30/frame facts, same register equations) runs in seconds,
so the blowup grows with the size of the hypothesis context (the per-step simp/omega seem to re-process all context facts, or hypotheses
`qh * yn1 + rh = un21` / `(un21*2^32+un0)/y' <= qh` are fed to the arithmetic side-condition solver on every step).
Workaround tried: `clear` the nonlinear facts before janus_run (done in the zero case: `clear h1 h2 h3`), `(budget := N)`, Nonempty-wrapping;
none made the full-context version finish. Not yet bisected which single hypothesis is responsible.

Needed from the engine: janus_run should not degrade with unrelated Nat hypotheses in context (or offer `janus_run only [...]`/a way to restrict
the context used for side conditions).
