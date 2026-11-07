Deliberately shifts the harness layout (code + rodata addresses) to test layout independence of proofs:
cp -r go build/go-shift; cp -r tools/layout-shift/pad build/go-shift/pad;
add import "fv-uint256/harness/pad" and `pad.Pad, pad.Sink, pad.Sink2,` to Keep in cmd/harness/main.go; build as usual.
SSZ result (2026-11-07): arm64 MarshalSSZInto 0xb7500 -> 0xb7a30, amd64 0x4b2e20 -> 0x4b3320; all 8 SSZ Main verifies pass on both layouts.
