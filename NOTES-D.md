# NOTES-D (FV-D handoff, branch fv/wd)

## Verified (correctness + Witness.nonvacuous in one `janus verify`, pin f8a20f36 unless noted)
- Float64 arm64 (751 s cold) and amd64 (1170 s; re-confirmed on f8a20f36: 2025 s / 356 s).
- amd64 IDiv, IMod, ISDiv, ISMod (library form; cold times in wip-d/logs/*lib-cold*).
- amd64 Sqrt (1345 s with the split head proof; first run 2240 s) and ISqrt (349 s warm). Library: `lean/Fv256/SqrtProg.lean`,
  `Amd64/Sqrt{Small,Sum,Big,Loop,Main,Summary}L.lean`, `SqrtLibBase`, bridge `EnsuresOfS.ensures2s`, `Lsh/Rsh` summaries
  (`LshProg`/`LshSum`/`LshSumAlias`, `RshProg`/`RshSum`), ISA-independent math `SqrtMath`, `SqrtHead`, `SqrtLimb`, tactics `SqrtTac`
  (type-based lookup: grab_const / grab_frame / grab_proj_of; to be replaced by FV-E's shared GrabTac).
- Verify driver: `wip-d/ver5.sh ISA Fn` (snapshot of lean/, shared cache /srv/janus-ops/jcache-shared, timeout 7200). Stub runs with
  `WIT=` skip the witness theorem and leave a kept workspace (path on the `Kept workspace:` line of wip-d/logs/<isa>-<Fn>.log) for `lake env lean`.

## Written, not yet verified
- IAddMod amd64: `Amd64/IAddModCore.lean` (proof complete, conditional on the AddMod library summary as a THEOREM ARGUMENT; the audit
  rejects a verify target whose statement carries the library program, so the core is only imported), `Amd64/IAddMod.lean` (final
  theorem via `AddModSum.addmod_summary` + witness). Blocked on a fast `addmod_summary` build (FV-G reworking; both my stub and FV-F's
  verify timed out at ~7000 s). When it builds: `wip-d/ver5.sh amd64 IAddMod`.
- IExp amd64: skeleton only (`Amd64/IExp.lean`), now owned by FV-H. arm64 Sqrt/ISqrt: owned by FV-H.

## Lessons (speed)
- Never `bv_omega`/`simp (disch := omega)` over the big call-state goals: build tiny top-level lemmas (`sub144`, `retAddrOf_push`).
- Explicit `V` shape: the goal's value has zero limbs simp-normalised away (no `* 0`); a mismatched `V` in `exact leafA..` costs minutes.
- Split a janus64_run proof per branch (SqrtMainL: 414 s -> 130 s) by putting the branch facts in the theorem precondition.
- Never pass `-o /dev/null` to lean. Use no `-o`, or a scratch/workspace olean path.
- Do not use positional `rename_i` for summary facts; use content lookups.

## Queue (from FV-A/main)
1. IAddMod arm64 (arm64 AddMod verified by FV-G; same pattern: core over summary, final file, witness, one verify).
2. PrettyDec both ISAs (ask FV-E ac09fc55d2e9229a7 for the toy drafts; use Dec's dec_summary/DecAt and GrabTac).
3. Hex arm64 "blocked U16": read UINT256-UPSTREAM.md, report whether it is still a real blocker.
4. IAddMod amd64 final verify when FV-G reports.
5. IMulMod / IMulModWithReciprocal both ISAs once FV-F publishes the MulMod summary statements (wrappers `z.MulMod(z,x,m)` /
   `z.MulModWithReciprocal(z,x,m,mu)`).
6. When FV-A integrates GrabTac: make SqrtTac import it and delete the duplicate tactics (SqrtTac, IAddModCore, ISqrt import SqrtTac).
