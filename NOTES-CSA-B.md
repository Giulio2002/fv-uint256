# NOTES-CSA-B (fork B of FV-CSA2): arm64 Format call-sites

Generator: scripts/cs_format_a64.py (idempotent; checks out fv/wrun versions of FormatWitA/B/G/N + Format.lean first, rewrites them,
regenerates the aggregate lemmas csAll16/csAll0 at the end of lean/Fv256/Arm64/FormatCS.lean -- everything above `-- AGGREGATE-BEGIN` in FormatCS is hand-written and kept).
Design: one universal env memU/sU (R0 metadata, toy heap, hA/hB blocks, data) for the stubs; flat memory (Inhab.callSt) for ICall.
FINDING: `Hw` (FormatWitA) made the TypeAssert hypothesis's pre unsatisfiable (Ready Hw [x0,x1] false: Hw only admits 3-word args) -> Hw now also admits `∃ x y, a = [x,y]`;
models model1/2 (A, G) get `replace hpp := hpp.resolve_right ...`.
Thin witness proofs in Format.lean originally flattened `h10.. hp16` (wrong nesting for `exact`); generator nests `⟨h10,..,hp16⟩, hcs`.
## Status 01:15
First Format audit (KEEP=1) never compiled: since ~01:12 EVERY csa-q run rejects in 0-1 s with
"The janus dependency at lean/.lake/packages/janus does not match the framework at /srv/janus-up3 (SHA-256 3b9800d8...)":
/srv/janus-up3 working tree has uncommitted edits (M Janus/Tools/Audit.lean, audit/roundup3/run-verify-rows.sh; HEAD d3f93eaa, pin 8615b09c).
Fix (parent/main): run with --janus-root on a clean checkout of 8615b09c (e.g. `git -C /srv/janus-up3 worktree add --detach /srv/janus-up3-pin 8615b09c`) or ask UP3b to stop editing the pin tree.
Format draft: known placeholders: 4 `sorry` in FormatCS.bf_pre16 (limb readbacks + bigAbs); rest untested.
