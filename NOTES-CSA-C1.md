# NOTES-CSA-C1: scripts/cs_live_a64.py (arm64 Live-family call-site conjuncts for the toy-runtime cores)

Usage (from /srv/fv-uint256-csa, after `git checkout fv/wrun -- CORE_FILE THIN_FILE`):
  python3 scripts/cs_live_a64.py CFGNAME lean/Fv256/Arm64/<Core>.lean nonvacuous_core lean/Fv256/Arm64/<Thin>.lean nonvacuous [THEOREM..]
  python3 scripts/cs_live_a64.py CFGNAME --print            # show the block and the conjuncts
CFG entries: `sfd` (SfdWitC/SetFromDecimal: ok has 5 disjuncts, R2 = R0), `fd` / `mfd` (FdWitC, MFdWitC: 6 disjuncts, R2 = (R3 TW)).
New file families: copy a CFG entry and set: s0, R2, priv (R2.priv simp lemma), nok (number of `ok` disjuncts), pos (index of each stub in `ok`),
new_ok/mg_ok/mv_ok (inner proof after the Or-position), dst/src (memmove regs), newty, rt_eq, inv0, env0; `extra` = list of (defs, conj, term)
for RtLive etc. The block needs in the core file's namespace: s0, R, rt_eq, inv0, env0 (Env ... s0, 18 conjuncts, field 16 is R2.Env), addr_new/mg/mv/w1/w2,
outside_of_decide, and memory regions covering: type of newobject (numErrT), stack window [sp-4096, sp+8+24), memmove dst (writable) and src.
It adds: import Fv256.Arm64.CallSites.Base + `open Fv256.Arm64.CallSites` to both files, the block before the core's docstring, 7 conjuncts
(Newobject/Mallocgc/Memmove LiveSite, WbLiveSite x2, CmpstringPre 16, IfaceeqSite R2) at the END of the core statement (after the pre) and before
`Returns (`/`GoReturns (` of the thin statement, `cs1..cs7` binders in the thin's `obtain`, and the terms in both proofs.
Conjunct shape: `∃ s_c : State, s_c.pc = BitVec.ofNat 64 (contractAddr "runtime.X") ∧ XLiveSite R addr 4096 [] 0x400 s_c` (closed L, b).
Status: see COVERAGE of audits in NOTES-CSA.md.
