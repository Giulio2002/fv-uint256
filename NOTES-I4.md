# NOTES-I4 (FV-I4: arm64 SetFromDecimal, strconv.ParseUint wrapper chain)
Worktree /srv/fv-uint256-wI4, branch fv/wi4 (from fv/wi + fv/master merge). Janus pin 655a23fa. Dev workspace build/ws (symlink to lean/Fv256, package override build/kept/janus; Extracted = arm64 SetFromDecimal extraction build/ex-arm64-SetFromDecimal).
Scripts: build/lt.sh REL.lean OUT (HEAVY=1 TMO= MEM= DEPS="Fv256.X ..."; priority 0 default; output build/out/OUT(.raw)), build/syn.sh (45 s parse check), tools/gen_sfdprog.sh (regenerate Arm64/SfdProg.lean; FV-B9 regenerated stubs/contracts on fv/wb7: take theirs when merging).
Watch pattern: `rm -f build/out/t2.fin; (HEAVY=1 ... build/lt.sh F t2.out; echo fin > build/out/t2.fin) &` then a run_in_background `until [ -e t2.fin ]` loop.
## Done (lean-checked, not yet janus-verified; all over Fv256.Arm64.SfdProg.program, Extracted-free)
SfdDecode (decoderune_sum), SfdParse (pu_sum), SfdMul (mul_sum), SfdEnv, SfdTePre (Mod with hT per FV-B9's fix, ChunkOK, TePre, TeObj, TePost),
SfdTeTail0 (te_tail0: flag-0 tail from te+0xe0, 7 s), SfdTeObj0 (te0_base, te0_lrS, te0_conv, tm_fields/tm_view/tm_frame/te0_copy, te_omega),
SfdTeSum0 (te_sum0, flag 0; prefix 206 s), SfdPw (statement PwPre/PwPost/PwSum, pw_sum is SORRY).
## Todo
te_sum1 (flag != 0: gcWriteBarrier2 then gcWriteBarrier1, slots in x25), te_sum = summary_split, pw_sum (mirror amd64 SfdPw), then hash to FV-B9 (a782b34e9c7f76b70), then janus verify nothing here (FV-B9 owns Extracted-level + witness).
## Lessons
- omega in giant contexts: te_omega (janus_clear_irrel; omega) took the prefix from >15 min to ~3 min. Heartbeat/timeouts: split into small cached files (tail, conversion).
- bl targets: stepper needs branch hyps in its own printed form (use set_option trace.janus true in).
- stepper reads of global addresses need literal addresses (rw abbrev = literal first) and `accessible` facts about the CURRENT memory (derive via MemFrame.accessible chain).
- Mod unsatisfiability found by FV-B9 (T descriptor inside R2.priv): hT replaces framing.
