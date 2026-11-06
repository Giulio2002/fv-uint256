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

## PrettyDec handover from FV-E (branch fv/we, /srv/fv-uint256-we; received after the notes above)
State: spec/math only, no machine-code proof started.
- Spec: `lean/Fv256/PrettyMath.lean` (proved, no sorry): `pad3`, `prettyBytes sep n`, `prettyBytes_lt/_ge`, `pcell sep v p`, `plen v`,
  `prettyBytes_length`, `pcell_add4`, `prettyBytes_getD`. `SpecTxt.lean` has `prettyBytes_zero` (= [48], the Go early return "0").
- Go code (decimal.go PrettyDec): IsZero early return "0"; else loop: udivrem by 10^19 into quot/rem, `strconv.AppendUint(buf[:0], rem.Uint64(), 10)`,
  copy buf backwards into out inserting `sep` every 3 digits (comma counter persists across the 19-digit chunks), final `string(out[pos-len...])` via slicebytetostring.
- Extractions `build/ex-{amd64,arm64}-PrettyDec` on fv/we are on the OLD pin: re-extract with
  `janus extract build/harness-<isa> '...(*Int).PrettyDec' DIR --contract runtime.slicebytetostring --contract runtime.growslice --contract runtime.gopanic`.
- Reusable: `Fv256/DecProg.lean`, `Fv256/Arm64/DecProg.lean` (library programs for Dec/FormatUint/AppendUint/formatBase10/formatBits + udivrem ChainProg). PrettyDec's data
  layout differs (.rodata + 0x2aa5a/0x31909/0x34c81/0x363b0, NOT 0x34b4a/0x34d06), so DecProg's data does not fit: use `tools/gen_libprog.py --base ChainProg` with its own `--fn`/`--data` list.
  `Fv256/LinkEq.lean` (ProgEq/LibIn) transfers a library summary + runtime contract to the extraction. `Fv256/GrabTac.lean` has content-based lookup.
  amd64 `fb10_summary` / `append_summary` (DecL / StrconvAppend) summarize formatBase10 / AppendUint if the program contains those segments (same addresses as in Dec's lib).
- Runtime facts: `slicebytetostringSpec` needs the staticuint64s address and its post has `StrAt`; `Fv256/DecAt.lean` shows how the result location is stated.
  Witness: stock Janus toys handle only zero-length args; `Fv256/ToyRuntime64.lean` has an unproved looping slicebytetostring (sbtsCopyCode), proved 2-byte straight-line
  sbts2/stb2 (Amd64/MarshalText.lean Witness), nothing for PrettyDec yet. Reference verify times: Dec 16-17 min, String 16-20 min once the shared cache is warm.
