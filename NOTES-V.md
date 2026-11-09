# NOTES-V (FV-V), 2026-11-07

## Findings
- Value (and MarshalText/JSON) second-call hypothesis `∀ M …` : Value demanded the concrete `R.inv` on EVERY frame-respecting M (unsatisfiable: garbage
  bump cell) -> val>=100 case vacuous. ALSO `liveReady (LiveCall …)` (the old `HL`) is unsatisfiable: LiveCall contains the stack check
  `m.readLE (g+16) 8 + stack < sp`, a fact about memory OUTSIDE the runtime view, while liveReady quantifies over all m with the same view.
- MarshalText / MarshalJSON are NOT vacuous (H is a parameter the witness chooses): `Witness.big` (z = 10^7) added + verified on arm64
  (fv/wt in /srv/fv-uint256-wT: 8c00a64 Text arm64 big, 05db73e JSON arm64 big; janus 77fb30cc).  amd64 Text big written (not yet verified in one run),
  amd64 JSON big NOT written.

## The Dec-live fix (arm64 done at lemma level; fv/wv in /srv/fv-uint256-wV, janus pin /srv/janus-wV-pin = u14 4ec8aab8)
- Fv256/Proofs/Arm64/SbtsG.lean: `sbtsG st G` (slicebytetostringSpec with guard := some 4096 and a ghost `G r0 r1 m` in the post), `Gp R g0 extra`
  (∃ L1 b1, R.inv b1 L1 g0 (view R.rt L1 m) ∧ extra ≤ b1 ∧ (0<r1 → InRanges r0 r1 L1)), `HG` (readiness WITHOUT the stack check; it is the spec guard),
  `contract_G` (RtLiveContract -> RtContract (HG..) (sbtsG..)), `Gp_congr` (Gp depends on the memory only through rtView).
- Fv256/Proofs/Arm64/{StrconvFormatUintGen,DecSummaryGen,DecLiftGen,DecExtGen}.lean: formatUint_summary_gen / dec_summary_gen / dec_summary_E_gen / dec_summary_ext_gen =
  the old summaries over `sbtsG st G` with an extra last post conjunct `100 <= v -> G (s'.regs 0) (s'.regs 1) s'.mem`; Dec pre now `GuardOK s 4576`
  (sbts call needs the stack check), formatUint pre `GuardOK s 4192`.  OLD SUMMARIES UNCHANGED (Dec/String/MarshalText/JSON need no re-verification).
- amd64 mirror: Fv256/Proofs/Amd64/{SbtsG (HG64, contract_G64, reuses Arm64.SbtsG), StrconvFormatUintGen, DecSummaryGen, DecLiftGen, DecExtGen}.lean, all compile
  (checked in the MarshalText amd64 kept workspace, janus 77fb30cc); amd64 pre `StackGuardOK s 4568`, formatUint pre gets `StackGuardOK s (0x58+4096)` + a g-apart fact.
- Value arm64 restated (lean/Fv256/Proofs/Arm64/Value.lean): `HL R` = ∀ m (same rtView) ∃ L b, LiveAt … (cost+16) … (no stack check), `GuardOK s 4608`,
  hLive: ∀ M p l L1 b1, frames → StrOut → DecAt → (100 ≤ v → R.inv b1 L1 g (view R.rt L1 M) ∧ 16 ≤ b1 ∧ (0<l → InRanges p l L1)) → ∃ L b, LiveAt … cvAddr ….
  The correctness proof compiles (kept workspace, 10 s).  Witness (z = 10^15, sbtsSeg ssAddr 16 16 + convTstringSeg cvAddr 16) is a skeleton with sorries:
  dataLoaded, hz, pre (see Value.lean).

## Next steps
1. vv.sh arm64 (running; cold framework build) -> kept workspace on 4ec8aab8 -> close the 3 sorries of the Value arm64 witness (iterate with `lake env lean Scratch.lean`).
2. amd64 Value from arm64 Value + Amd64/*Gen (HG64/contract_G64).
3. Verify MarshalText amd64 big (vt.sh MarshalText amd64 big …), write + verify MarshalJSON amd64 big (extraction ex-amd64-MarshalJSON already in /srv/fv-uint256-wT/build).
4. Report COVERAGE rows to FV-A (a080d76370e009554); message main at each milestone.
