# NOTES (checkpoint)
- Janus worktree /srv/janus-fv-uint256-janus2 (fv/janus-main @83049110), bin/janus built.
- Build binaries: GOTOOLCHAIN=go1.26.0 CGO_ENABLED=0 GOOS=linux GOARCH=$a go build -trimpath -buildvcs=false -o build/harness-$a ./cmd/harness (in go/).
- Extract: janus extract build/harness-$a 'github.com/holiman/uint256.(*Int).IsZero' build/ex-$a-IsZero
- Verify: janus verify build/ex-arm64-IsZero --proof lean/Fv256/Arm64/IsZero.lean --proof-root lean --theorem Fv256.Arm64.IsZero.correctness
- State: first lake build + verify launched in background (bash task bp1dkb5vb); IsZero.correctness proof still `sorry` (placeholder to see the goal).
- lakefile.toml has an absolute janus path: replace by git rev before publishing.
