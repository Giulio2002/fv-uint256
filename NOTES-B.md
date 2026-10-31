# Notes, family B
- Reciprocal measured against Go: mu == (2^512-1)/m for most m, but about 0.5% of random m give exactly one less. The spec must therefore be a relation (floor-1 <= mu <= floor), or the exact Newton model.
- U7 (kernel deep recursion): see /srv/janus-ops/UINT256-UPSTREAM.md; repro wip/Float64-arm64-u1repro.lean. Facts: top-level proof term depth 315, auxiliary lemmas pass individually; failure is inside kernel evaluation during the epilogue load after a callee's stores.
- Private tooling: tools-local/lean1.sh (direct lean run against the last verify workspace); the workspace under ~/.cache/janus/.../consumer is shared per consumer hash and gets overwritten by the last `tools/v.sh` of ANY ISA/function: rerun v.sh to restore Extracted.
- A single extraction contains the callees (udivrem, udivremKnuth, udivremBy1, math/bits.Div64) identical across Div/Mod/...; proofs of their summaries must be repeated per extraction (generate from one template).
