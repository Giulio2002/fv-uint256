# NOTES (checkpoint)
- Janus worktree /srv/janus-fv-uint256-janus2 (fv/janus-main @83049110), bin/janus built.
- Build binaries: GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 GOOS=linux GOARCH=$a go build -trimpath -buildvcs=false -o build/harness-$a ./cmd/harness (in go/).
- Extract: janus extract build/harness-$a 'github.com/holiman/uint256.(*Int).IsZero' build/ex-$a-IsZero
- Verify: janus verify build/ex-arm64-IsZero --proof lean/Fv256/Arm64/IsZero.lean --proof-root lean --theorem Fv256.Arm64.IsZero.correctness
- State: first lake build + verify launched in background (bash task bp1dkb5vb); IsZero.correctness proof still `sorry` (placeholder to see the goal).
- lakefile.toml has an absolute janus path: replace by git rev before publishing.

## Checkpoint 2026-10-31
- Lesson: amd64 Mul took >30 min with plain omega (killed by timeout 1800, own pid). Fix: normalise BitVec products to Nat first
  (`simp only [BitVec.toNat_mul, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reduceMod]`) so `janus64_arith` can use the `janus_carry`
  reflection procedure: verifies in about 1 minute.
- Never edit Util.lean/Spec.lean while a `janus verify` runs (stale-input failure). Prototype lemmas in build/scr and merge between runs.
- Fast iteration: tools/util1.sh (compile Spec+Util), tools/lean2.sh ISA Fn (run lean on a theorem module against the newest consumer workspace;
  the workspace must come from a verify of that same function).
- Slt/Sgt amd64: shared limb lemmas Util.slt_toNat / sgt_toNat (sign bits first, then the borrow chain).
- Cmp: Util.cmp_ofInt, zero4_iff, ite01_eq*; Mul amd64 uses Util.OnlyWrites2 (result + scratch slot below SP).
