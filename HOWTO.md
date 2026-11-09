# HOWTO: verify one function (commands that worked)

Prereqs: Go (this repo's go/ uses GOTOOLCHAIN=go1.26.0), Janus checkout built: `go build -o bin/janus ./cmd/janus`
(JANUS=path to that binary). Heavy commands go through `memcap`; LEAN_NUM_THREADS=4 JANUS_JOBS=2.

1. Build the harness (links every exported function) for each ISA, in `go/`:
   `GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 GOOS=linux GOARCH=arm64 go build -trimpath -buildvcs=false -o ../build/harness-arm64 ./cmd/harness` (same for amd64).
2. Extract one method: `$JANUS extract build/harness-arm64 'github.com/holiman/uint256.(*Int).IsZero' build/ex-arm64-IsZero`.
3. Write `lean/Fv256/<Arm64|Amd64>/<Fn>.lean`: `theorem correctness : Ensures Extracted.program Extracted.entry [args] pre post`
   where `post` states the result with `Fv256.Spec.*` (the independent Nat model) and `Janus.Spec.val256`/`valueAt` (memory bridge),
   plus `namespace Witness` with `nonvacuous` (a concrete state satisfies the precondition) and `returns` (that call returns
   the expected value). Proof: `janus_intro hs; janus_run` (arm64) / `janus64_intro hs; janus64_run [readLE_32]` (amd64), then arithmetic.
   Templates: Janus `examples/proofs/Eq32.lean` (arm64), `examples/proofs-amd64/Double/Proof.lean` (amd64, StackWritable s 0 8 + simp regSP).
4. Verify: `memcap $JANUS verify build/ex-arm64-IsZero --proof lean/Fv256/Proofs/Arm64/IsZero.lean --proof-root lean --theorem Fv256.Arm64.IsZero.correctness`
   (`scripts/verify-all.sh Fn` wraps this for a whole function). Warm run takes about 30-60 s; it runs the audit and kernel replay.
