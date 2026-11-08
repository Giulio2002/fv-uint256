# NOTES-WRUN (FV-WRUN) HANDOVER, 2026-11-07 ~23:20

Task: upgrade every fv-uint256 final-theorem witness to the Janus "returning-run" shape (U-WITNESS-RUN), then add the call-site conjunct
(U-WITNESS-CALLSITE). Worktree /srv/fv-uint256-wrun, branch fv/wrun off fv/master b3b89b7a (lakefile pin untouched).

## Status
- PHASE 1 DONE AND COMMITTED (86887ba5): the Returns/GoReturns conjunct + `correctness ...` proof in 314 witness theorems (292 row-files, both ISAs).
  Rewritten by scripts/upgrade-witness-run.py (311), by hand (PaddedBytes arm64/amd64), amd64 DivMod was already in shape.
  Only arm64 Add was audited/verified end-to-end (against Janus f0c6bbef, cold: 666 s). The rest is NOT yet compile-checked: expect a few type errors
  (core-mode `obtain` proofs, `_` args for Format, HINTS) to appear in the sweep.
- PHASE 2 NOT STARTED: call-site conjunct for the 82 contract-bearing witnesses (list below). WAITING for UP3b (a7a5a1e757be0f837) to publish the per-family
  conjunct text that handles the `∀ L b, Summary` Live contracts: expected auditor false reject "does not unfold to a Summary" for NewobjectLive/WbLive/MallocgcLive/
  RtLive (Audit.lean ~l.3068 only unfolds up to Summary, no forall telescope). Not confirmed: the IntoBig stub run was still in progress (see below).
- Nothing about timings measured yet (subset: Add, Format, SetFromDecimal, Scan, UnmarshalJSON, IntoBig, both ISAs; before = fv/master files + old pin, after = upgraded).

## Environment (all mine; delete when done)
- Private janus: /srv/janus-wrun (detached worktree of /srv/janus-up3's repo, now at 29ff3727, bin/janus built with `lake build Janus.Tools.Audit janus-audit` +
  `CGO_ENABLED=0 /usr/local/go/bin/go build -o bin/janus ./cmd/janus`). Repin = `git -C /srv/janus-wrun checkout --detach <rev>` + both builds + bump rev in the scratch lakefile.
- Scratch audit tree: /srv/fv-uint256-wrun-aud (detached; lean/lakefile.toml git=/srv/janus-up3 rev=29ff372758d364539bc611f7011f6d2a32148b9b, `lake update janus` done).
- Cache: /srv/janus-ops/jcache-wrun  (DELETE at the end; a new framework pin costs a cold ~10 min framework build + ~8 min leanchecker first verify).
- Row runner: /tmp/claude-0/-root/b301f400-a150-4f15-8f32-0b73b1894423/scratchpad/arow.sh ISA FN [audit|full] (rsyncs lean/Fv256 from the wrun worktree into the scratch tree,
  extracts with build/harness-* copied from /srv/fv-uint256/build, runs janus verify with all witness theorems); env STUB=1 sorries `correctness` first (scratch tree only).
  Run it under `HEAVY_PRIORITY=1 /srv/janus-ops/bin/heavy-run -- timeout N ...`. NOTE: JANUS_STOP_AFTER_AUDIT=1 did NOT shortcut anything in the f0c6bbef build (it did a full verify).
- Row list: scratchpad/rows.txt (isa fn file nwit witnesses), files.txt.

## Tools in the repo
- scripts/upgrade-witness-run.py FILE... (idempotent; `--dry`): parses the main `correctness` (binders, hyps, Ensures/EnsuresGo atoms) and each witness theorem
  (`∃ vars, hyps ∧ RetAddr ∧ CallSetup ∧ pre`), appends the Returns/GoReturns conjunct (post lambda renamed to the witness's variables), and rewrites the proof:
  anonymous-constructor proofs keep all components (non-identifier ones become `?wK` holes + `case wK => exact ..`), proofs that are a bare theorem name
  (`FdWit.nonvacuous_core`, `FormatWitB.nonvacuous_core`...) use `obtain ⟨vars, pattern⟩ := core; exact ⟨vars, pattern, correctness ...⟩`. Main binders that the witness
  does not instantiate by a variable: positional rename via the CallSetup args, `HINTS` table (CmpBig/SetFromBig len, Format fW fP ... stack b0 zv RW ...), or `_`.
  Pin conjuncts (`pinT`) are skipped as hypotheses. Extension point: `EXTRA_CONJUNCTS(ctx)` (returns extra conjunct texts; not wired to the proof yet) for the call-site conjunct.
- scripts/stub-correctness.py (scratch trees only).

## Phase 2: call-site conjunct (frozen by UP3, commit 29ff3727, NOTES-UP3.md "FROZEN (step 2)")
For EVERY contract hypothesis c of the main theorem the witness statement must contain, with c's own instantiated entry/args and the SAME variables:
    (∃ s_c : State, s_c.pc = BitVec.ofNat 64 <entry> ∧ <pre of c's Summary> s_c)         -- amd64: Janus.Amd64.State, s_c.rip
  ICallContract[64] fn nargs stack above rt keep R P pres : entry = fn, pre = ICallPre[64] nargs stack above rt P
  stub families (Newobject/Wb/Mallocgc/Memmove/Rt/Cmpstring/Ifaceeq/Errorf/ConvT64/TypeAssert/Makeslice): entry = Extracted.program.contractAddr "<name>" (value `newA` etc. in the
  witness), pre = the Summary pre of the family def (e.g. NewobjectContract: NewobjectPre stack s ∧ Ready H rt [typ] s; NewobjectLive: ∀ L b, NewobjectPre ∧ StackRoom ∧ LiveAt R addr [typ] L b round (x28) mem calleeStack).
  Proof term `⟨wsCall, rfl, wsCall_pre⟩` with closed `def wsCall : State` + `theorem wsCall_pre`. Templates: Janus examples/proofs/WriteTo.lean (arm64),
  examples/proofs-amd64/WriteTo/Proof.lean, CountThenWrite; Janus/Contracts/ICallSat[Amd64].lean `wstate`/`wstate_pre`; fv lean/Fv256/InhabBase.lean `callSt`, `callSt64`.
  Suggested construction for the stub runtimes: `s_c := { s0 with pc := ofNat <addr>, regs := <set arg registers> }` over the witness's existing s0 and reuse its runtime invariant
  lemma (`inv0` : R.inv 0x400 [] (x28) (view R.rt [] mem), proved for s0.mem) for the LiveAt part; CallOK/StackRoom/TypeOK by `decide` on the concrete s0 frame.
  Live families: wait for UP3b's text on the `∀ L b` (take L := [], b := 0x400 as inv0 does).
Scripting hint: the call-site conjunct and its proof need per-witness concrete values, so generate the statement conjunct + `⟨wsCall_i, rfl, wsCall_i_pre⟩` in the script
(EXTRA_CONJUNCTS) and write the `def wsCall_i` / lemma per (witness, contract) by hand or from a per-family template.

## Verification plan (not yet done)
1. repin done (29ff3727); run arow.sh on every row (all 292) in audit mode, ONE heavy job at a time (load<62, MemAvailable>=60G, df / >=70G), collect false rejects; fix rewrites.
2. Phase 2 per family (below); re-audit.
3. Timing subset before/after (warm cache), 4. report to main + FV-A2 (a66f673964e9e7ef5); tell UP3b when the tree is ready.

## IntoBig arm64 result on pin 29ff3727 (942 s, cold): REJECTED "the contract hypothesis Janus.Contracts.NewobjectLiveContract does not unfold to a Summary (U-WITNESS-CALLSITE)" -> confirmed false reject for the forall-L-b Live families; reported to UP3b (a7a5a1e757be0f837). The Returns part was not the issue.

## Work list (generated by the snippet in this file's history; 82 contract-bearing witnesses, 334 contract hypotheses)

Family -> witnesses. Each line = one contract hypothesis = one `(∃ s_c, s_c.pc = ofNat <entry> ∧ <family pre> s_c)` conjunct to add. Callee `runtime.x` = `Extracted.program.contractAddr "runtime.x"`.

### WbLiveContract (34)
- arm64 Format.lean `big` -- runtime.gcWriteBarrier1
- arm64 Format.lean `big` -- runtime.gcWriteBarrier2
- arm64 Format.lean `nil` -- runtime.gcWriteBarrier1
- arm64 Format.lean `nil` -- runtime.gcWriteBarrier2
- arm64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier1
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier2
- arm64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier1
- arm64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier2
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier2

### WbLiveContract64 (34)
- amd64 Format.lean `big` -- runtime.gcWriteBarrier1
- amd64 Format.lean `big` -- runtime.gcWriteBarrier2
- amd64 Format.lean `nil` -- runtime.gcWriteBarrier1
- amd64 Format.lean `nil` -- runtime.gcWriteBarrier2
- amd64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Format.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 IntoBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 Scan.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 ToBig.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.gcWriteBarrier2
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier1
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.gcWriteBarrier2
- amd64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier1
- amd64 UnmarshalTextMain.lean `hex` -- runtime.gcWriteBarrier2
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier1
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.gcWriteBarrier2

### Ifaceeq (24)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.ifaceeq
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.ifaceeq
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.ifaceeq
- amd64 UnmarshalTextMain.lean `hex` -- runtime.ifaceeq
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 Scan.lean `nonvacuous` -- runtime.ifaceeq
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.ifaceeq
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.ifaceeq
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.ifaceeq
- arm64 UnmarshalTextMain.lean `hex` -- runtime.ifaceeq
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.ifaceeq

### ICallContract (19)
- arm64 EncodeRLP.lean `nonvacuous` -- addr: ICallContract P fn 4 stack 96 rt (fun _ => []) R (fun sc => sc.regs 0 = w ∧ StrOut sc.mem 
- arm64 Format.lean `big` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `big` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `big` -- addr: ICallContract P fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `big` -- addr: ICallContract P fa 4 4608 120 rt (fun _ => []) Rc (FastWP data (Fv256.FormatSpec.fastBytes
- arm64 Format.lean `big` -- fmt.Fprint
- arm64 Format.lean `big` -- math/big.(*Int).Format
- arm64 Format.lean `nil` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nil` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nil` -- addr: ICallContract P fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nil` -- addr: ICallContract P fa 4 4608 120 rt (fun _ => []) Rc (FastWP data (Fv256.FormatSpec.fastBytes
- arm64 Format.lean `nil` -- fmt.Fprint
- arm64 Format.lean `nil` -- math/big.(*Int).Format
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 1 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 2 4608 120 rt (fun _ => []) Rc (fun _ => True) (RtPreserves R2)
- arm64 Format.lean `nonvacuous` -- addr: ICallContract P fa 4 4608 120 rt (fun _ => []) Rc (FastWP data (Fv256.FormatSpec.fastBytes
- arm64 Format.lean `nonvacuous` -- fmt.Fprint
- arm64 Format.lean `nonvacuous` -- math/big.(*Int).Format

### ICallContract64 (19)
- amd64 EncodeRLP.lean `nonvacuous` -- addr: ICallContract64 P fn 4 stack 56 rt (fun _ => []) R (fun sc => sc.regs 0 = w ∧ StrOut sc.me
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 2 4608 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `big` -- addr: ICallContract64 P 7340032 4 4608 80 rt (fun _ => []) RWr (FastWP data (Fv256.FormatSpec.fa
- amd64 Format.lean `big` -- fmt.Fprint
- amd64 Format.lean `big` -- math/big.(*Int).Format
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 2 4608 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nil` -- addr: ICallContract64 P 7340032 4 4608 80 rt (fun _ => []) RWr (FastWP data (Fv256.FormatSpec.fa
- amd64 Format.lean `nil` -- fmt.Fprint
- amd64 Format.lean `nil` -- math/big.(*Int).Format
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RP (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 1 4608 80 rt (fun _ => []) RW (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 2 4608 80 rt (fun _ => []) RF (fun _ => True) (RtPreserves64 R2)
- amd64 Format.lean `nonvacuous` -- addr: ICallContract64 P 7340032 4 4608 80 rt (fun _ => []) RWr (FastWP data (Fv256.FormatSpec.fa
- amd64 Format.lean `nonvacuous` -- fmt.Fprint
- amd64 Format.lean `nonvacuous` -- math/big.(*Int).Format

### RtContract (18)
- arm64 Dec.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 Format.lean `big` -- runtime.slicebytetostring
- arm64 Format.lean `big` -- runtime.stringtoslicebyte
- arm64 Format.lean `nil` -- runtime.slicebytetostring
- arm64 Format.lean `nil` -- runtime.stringtoslicebyte
- arm64 Format.lean `nonvacuous` -- runtime.slicebytetostring
- arm64 Format.lean `nonvacuous` -- runtime.stringtoslicebyte
- arm64 Hex.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalJSON.lean `big` -- addr: RtContract P cbAddr rt 4096 H (concatbyteSpec 3)
- arm64 MarshalJSON.lean `big` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalJSON.lean `nonvacuous` -- addr: RtContract P cbAddr rt 4096 H (concatbyteSpec 3)
- arm64 MarshalJSON.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalText.lean `big` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalText.lean `big` -- addr: RtContract P stAddr rt 4096 H stringtoslicebyteSpec
- arm64 MarshalText.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 MarshalText.lean `nonvacuous` -- addr: RtContract P stAddr rt 4096 H stringtoslicebyteSpec
- arm64 PrettyDec.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin
- arm64 String.lean `nonvacuous` -- addr: RtContract P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticuin

### RtContract64 (18)
- amd64 Dec.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 Format.lean `big` -- runtime.slicebytetostring
- amd64 Format.lean `big` -- runtime.stringtoslicebyte
- amd64 Format.lean `nil` -- runtime.slicebytetostring
- amd64 Format.lean `nil` -- runtime.stringtoslicebyte
- amd64 Format.lean `nonvacuous` -- runtime.slicebytetostring
- amd64 Format.lean `nonvacuous` -- runtime.stringtoslicebyte
- amd64 Hex.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalJSON.lean `big` -- addr: RtContract64 P cbAddr rt 4096 H (concatbyteSpec 3)
- amd64 MarshalJSON.lean `big` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalJSON.lean `nonvacuous` -- addr: RtContract64 P cbAddr rt 4096 H (concatbyteSpec 3)
- amd64 MarshalJSON.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalText.lean `big` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalText.lean `big` -- addr: RtContract64 P stAddr rt 4096 H stringtoslicebyteSpec
- amd64 MarshalText.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 MarshalText.lean `nonvacuous` -- addr: RtContract64 P stAddr rt 4096 H stringtoslicebyteSpec
- amd64 PrettyDec.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu
- amd64 String.lean `nonvacuous` -- addr: RtContract64 P ssAddr rt 4096 H (slicebytetostringSpec Extracted.dataAddr.«runtime.staticu

### NewobjectLiveContract (17)
- arm64 Format.lean `big` -- runtime.newobject
- arm64 Format.lean `nil` -- runtime.newobject
- arm64 Format.lean `nonvacuous` -- runtime.newobject
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.newobject
- arm64 IntoBig.lean `nonvacuous` -- runtime.newobject
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 Scan.lean `nonvacuous` -- runtime.newobject
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.newobject
- arm64 ToBig.lean `nonvacuous` -- runtime.newobject
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.newobject
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.newobject
- arm64 UnmarshalTextMain.lean `hex` -- runtime.newobject
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.newobject

### NewobjectLiveContract64 (17)
- amd64 Format.lean `big` -- runtime.newobject
- amd64 Format.lean `nil` -- runtime.newobject
- amd64 Format.lean `nonvacuous` -- runtime.newobject
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.newobject
- amd64 IntoBig.lean `nonvacuous` -- runtime.newobject
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 Scan.lean `nonvacuous` -- runtime.newobject
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.newobject
- amd64 ToBig.lean `nonvacuous` -- runtime.newobject
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.newobject
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.newobject
- amd64 UnmarshalTextMain.lean `hex` -- runtime.newobject
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.newobject

### RtLiveContract (13)
- arm64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- arm64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 Scan.lean `nonvacuous` -- addr: RtLiveContract P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 UnmarshalJSONMain.lean `unquoted` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalJSON.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 UnmarshalTextMain.lean `hex` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalText.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 UnmarshalTextMain.lean `nonvacuous` -- addr: RtLiveContract P Fv256.Arm64.UnmarshalText.sbAddr 4096 R (slicebytetostringSpec Fv256.Arm6
- arm64 Value.lean `nonvacuous` -- addr: RtLiveContract P cvAddr 4096 R convTstringSpec convTstringLive
- arm64 Value.lean `nonvacuous` -- addr: RtLiveContract P ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.staticui

### RtLiveContract64 (13)
- amd64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- amd64 MarshalSSZAppendMain.lean `nonvacuous` -- runtime.growslice
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 Scan.lean `nonvacuous` -- addr: RtLiveContract64 P sbAddr 4096 R (slicebytetostringSpec stAddr) slicebytetostringLive
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 UnmarshalJSONMain.lean `unquoted` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 UnmarshalTextMain.lean `hex` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 UnmarshalTextMain.lean `nonvacuous` -- addr: RtLiveContract64 P Fv256.Amd64.UnmarshalTextS.sbAddr 4096 R (slicebytetostringSpec Fv256.A
- amd64 Value.lean `nonvacuous` -- addr: RtLiveContract64 P cvAddr 4096 R convTstringSpec convTstringLive
- amd64 Value.lean `nonvacuous` -- addr: RtLiveContract64 P ssAddr 4096 R (slicebytetostringSpec Extracted.dataAddr.«runtime.static

### MallocgcLiveContract (12)
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 Scan.lean `nonvacuous` -- runtime.mallocgc
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.mallocgc
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.mallocgc
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.mallocgc
- arm64 UnmarshalTextMain.lean `hex` -- runtime.mallocgc
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.mallocgc

### MemmoveLive (12)
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.memmove
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 Scan.lean `nonvacuous` -- runtime.memmove
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.memmove
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.memmove
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.memmove
- arm64 UnmarshalTextMain.lean `hex` -- runtime.memmove
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.memmove

### CmpstringContract (12)
- arm64 FromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- arm64 MustFromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 Scan.lean `nonvacuous` -- runtime.cmpstring
- arm64 SetFromDecimal.lean `nonvacuous` -- runtime.cmpstring
- arm64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.cmpstring
- arm64 UnmarshalJSONMain.lean `unquoted` -- runtime.cmpstring
- arm64 UnmarshalTextMain.lean `hex` -- runtime.cmpstring
- arm64 UnmarshalTextMain.lean `nonvacuous` -- runtime.cmpstring

### MallocgcLiveContract64 (12)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 Scan.lean `nonvacuous` -- runtime.mallocgc
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.mallocgc
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.mallocgc
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.mallocgc
- amd64 UnmarshalTextMain.lean `hex` -- runtime.mallocgc
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.mallocgc

### MemmoveLive64 (12)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.memmove
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 Scan.lean `nonvacuous` -- runtime.memmove
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.memmove
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.memmove
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.memmove
- amd64 UnmarshalTextMain.lean `hex` -- runtime.memmove
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.memmove

### CmpstringContract64 (12)
- amd64 FromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- amd64 MustFromDecimalMain.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 Scan.lean `nonvacuous` -- runtime.cmpstring
- amd64 SetFromDecimal.lean `nonvacuous` -- runtime.cmpstring
- amd64 UnmarshalJSONMain.lean `nonvacuous` -- runtime.cmpstring
- amd64 UnmarshalJSONMain.lean `unquoted` -- runtime.cmpstring
- amd64 UnmarshalTextMain.lean `hex` -- runtime.cmpstring
- amd64 UnmarshalTextMain.lean `nonvacuous` -- runtime.cmpstring

### NewobjectContract (9)
- arm64 Bytes.lean `nonvacuous` -- runtime.newobject
- arm64 Clone.lean `nonvacuous` -- runtime.newobject
- arm64 DivMod.lean `nonvacuous` -- runtime.newobject
- arm64 EncodeRLP.lean `nonvacuous` -- runtime.newobject
- arm64 FromBig.lean `nonvacuous` -- runtime.newobject
- arm64 FromHex.lean `nonvacuous` -- runtime.newobject
- arm64 MustFromBig.lean `nonvacuous` -- runtime.newobject
- arm64 MustFromHex.lean `nonvacuous` -- runtime.newobject
- arm64 NewInt.lean `nonvacuous` -- runtime.newobject

### NewobjectContract64 (9)
- amd64 Bytes.lean `nonvacuous` -- runtime.newobject
- amd64 Clone.lean `nonvacuous` -- runtime.newobject
- amd64 DivMod.lean `nonvacuous` -- runtime.newobject
- amd64 EncodeRLP.lean `nonvacuous` -- runtime.newobject
- amd64 FromBig.lean `nonvacuous` -- runtime.newobject
- amd64 FromHex.lean `nonvacuous` -- runtime.newobject
- amd64 MustFromBig.lean `nonvacuous` -- runtime.newobject
- amd64 MustFromHex.lean `nonvacuous` -- runtime.newobject
- amd64 NewInt.lean `nonvacuous` -- runtime.newobject

### TypeAssert (6)
- amd64 Format.lean `big` -- runtime.typeAssert
- amd64 Format.lean `nil` -- runtime.typeAssert
- amd64 Format.lean `nonvacuous` -- runtime.typeAssert
- arm64 Format.lean `big` -- runtime.typeAssert
- arm64 Format.lean `nil` -- runtime.typeAssert
- arm64 Format.lean `nonvacuous` -- runtime.typeAssert

### ErrorfLive (4)
- amd64 MarshalSSZIntoMain.lean `nonvacuous` -- fmt.errorf
- amd64 UnmarshalSSZMain.lean `nonvacuous` -- fmt.errorf
- arm64 MarshalSSZIntoMain.lean `nonvacuous` -- fmt.errorf
- arm64 UnmarshalSSZMain.lean `nonvacuous` -- fmt.errorf

### ConvT64 (4)
- amd64 MarshalSSZIntoMain.lean `nonvacuous` -- runtime.convT64
- amd64 UnmarshalSSZMain.lean `nonvacuous` -- runtime.convT64
- arm64 MarshalSSZIntoMain.lean `nonvacuous` -- runtime.convT64
- arm64 UnmarshalSSZMain.lean `nonvacuous` -- runtime.convT64

### MakesliceContract (2)
- arm64 MarshalSSZ.lean `nonvacuous` -- runtime.makeslice
- arm64 PaddedBytes.lean `nonvacuous` -- runtime.makeslice

### MakesliceContract64 (2)
- amd64 MarshalSSZ.lean `nonvacuous` -- runtime.makeslice
- amd64 PaddedBytes.lean `nonvacuous` -- runtime.makeslice

## Per witness: reusable in-file material (state s0, invariant lemmas, setup, pre, models)

- **amd64 Bytes.lean** `Amd64.Bytes.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 Clone.lean** `Amd64.Clone.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 Dec.lean** `Amd64.Dec.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 DivMod.lean** `Amd64.DivMod.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 EncodeRLP.lean** `Amd64.EncodeRLP.Witness.nonvacuous`: 2 contracts [ICallContract64, NewobjectContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Format.lean** `Amd64.Format.Witness.big`: 12 contracts [ICallContract64, NewobjectLiveContract64, RtContract64, TypeAssert, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Format.lean** `Amd64.Format.Witness.nil`: 12 contracts [ICallContract64, NewobjectLiveContract64, RtContract64, TypeAssert, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Format.lean** `Amd64.Format.Witness.nonvacuous`: 12 contracts [ICallContract64, NewobjectLiveContract64, RtContract64, TypeAssert, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 FromBig.lean** `Amd64.FromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 FromDecimalMain.lean** `Amd64.FromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 FromHex.lean** `Amd64.FromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 Hex.lean** `Amd64.Hex.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 IntoBig.lean** `Amd64.IntoBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: hret, inv0, model_new, model_wb1, model_wb2, pre, preX, rt_eq, setup
- **amd64 MarshalJSON.lean** `Amd64.MarshalJSON.Witness.big`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MarshalJSON.lean** `Amd64.MarshalJSON.Witness.nonvacuous`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MarshalSSZ.lean** `Amd64.MarshalSSZ.Witness.nonvacuous`: 1 contracts [MakesliceContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 MarshalSSZAppendMain.lean** `Amd64.MarshalSSZAppendMain.Grow.Witness.nonvacuous`: 1 contracts [RtLiveContract64]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **amd64 MarshalSSZAppendMain.lean** `Amd64.MarshalSSZAppendMain.Witness.nonvacuous`: 1 contracts [RtLiveContract64]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **amd64 MarshalSSZIntoMain.lean** `Amd64.MarshalSSZIntoMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, s0_g, s0_sp, setup
- **amd64 MarshalText.lean** `Amd64.MarshalText.Witness.big`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MarshalText.lean** `Amd64.MarshalText.Witness.nonvacuous`: 2 contracts [RtContract64]; proof `by`; reusable: hret, pre, pre8, setup
- **amd64 MustFromBig.lean** `Amd64.MustFromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 MustFromDecimalMain.lean** `Amd64.MustFromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 MustFromHex.lean** `Amd64.MustFromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 NewInt.lean** `Amd64.NewInt.Witness.nonvacuous`: 1 contracts [NewobjectContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 PaddedBytes.lean** `Amd64.PaddedBytes.Witness.nonvacuous`: 1 contracts [MakesliceContract64]; proof `⟨impl,`; reusable: hret, pre, setup
- **amd64 PrettyDec.lean** `Amd64.PrettyDec.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 Scan.lean** `Amd64.Scan.Byt.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.Nil.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.NoE.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.Other.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Scan.lean** `Amd64.Scan.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 SetFromDecimal.lean** `Amd64.SetFromDecimal.Witness.nonvacuous`: 7 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 String.lean** `Amd64.String.Witness.nonvacuous`: 1 contracts [RtContract64]; proof `by`; reusable: hret, pre, setup
- **amd64 ToBig.lean** `Amd64.ToBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract64, WbLiveContract64]; proof `by`; reusable: hret, implOK, inv0, model_new, model_wb1, model_wb2, pre, rt_eq, setup
- **amd64 UnmarshalJSONMain.lean** `Amd64.UnmarshalJSONMain.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 UnmarshalJSONMain.lean** `Amd64.UnmarshalJSONMain.Witness.unquoted`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 UnmarshalSSZMain.lean** `Amd64.UnmarshalSSZMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, s0_g, s0_sp, setup
- **amd64 UnmarshalTextMain.lean** `Amd64.UnmarshalTextMain.Witness.hex`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 UnmarshalTextMain.lean** `Amd64.UnmarshalTextMain.Witness.nonvacuous`: 8 contracts [CmpstringContract64, Ifaceeq, MallocgcLiveContract64, MemmoveLive64, NewobjectLiveContract64, RtLiveContract64, WbLiveContract64]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **amd64 Value.lean** `Amd64.Value.Witness.nonvacuous`: 2 contracts [RtLiveContract64]; proof `by`; reusable: hret, pre, s0_inv, setup
- **arm64 Bytes.lean** `Arm64.Bytes.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 Clone.lean** `Arm64.Clone.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 Dec.lean** `Arm64.Dec.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 DivMod.lean** `Arm64.DivMod.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨implW,`; reusable: preW
- **arm64 EncodeRLP.lean** `Arm64.EncodeRLP.Witness.nonvacuous`: 2 contracts [ICallContract, NewobjectContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Format.lean** `Arm64.Format.Witness.big`: 12 contracts [ICallContract, NewobjectLiveContract, RtContract, TypeAssert, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Format.lean** `Arm64.Format.Witness.nil`: 12 contracts [ICallContract, NewobjectLiveContract, RtContract, TypeAssert, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Format.lean** `Arm64.Format.Witness.nonvacuous`: 12 contracts [ICallContract, NewobjectLiveContract, RtContract, TypeAssert, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 FromBig.lean** `Arm64.FromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `by`; reusable: hret, pre, setup
- **arm64 FromDecimalMain.lean** `Arm64.FromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 FromHex.lean** `Arm64.FromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 Hex.lean** `Arm64.Hex.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 IntoBig.lean** `Arm64.IntoBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: hret, inv0, model_new, model_wb1, model_wb2, pre, preX, rt_eq, setup
- **arm64 MarshalJSON.lean** `Arm64.MarshalJSON.Witness.big`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MarshalJSON.lean** `Arm64.MarshalJSON.Witness.nonvacuous`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MarshalSSZ.lean** `Arm64.MarshalSSZ.Witness.nonvacuous`: 1 contracts [MakesliceContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 MarshalSSZAppendMain.lean** `Arm64.MarshalSSZAppendMain.Grow.Witness.nonvacuous`: 1 contracts [RtLiveContract]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **arm64 MarshalSSZAppendMain.lean** `Arm64.MarshalSSZAppendMain.Witness.nonvacuous`: 1 contracts [RtLiveContract]; proof `by`; reusable: hret, inv0, model_gr, pre, rt_eq, setup
- **arm64 MarshalSSZIntoMain.lean** `Arm64.MarshalSSZIntoMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, setup
- **arm64 MarshalText.lean** `Arm64.MarshalText.Witness.big`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MarshalText.lean** `Arm64.MarshalText.Witness.nonvacuous`: 2 contracts [RtContract]; proof `by`; reusable: hret, pre, pre8, setup
- **arm64 MustFromBig.lean** `Arm64.MustFromBig.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `by`; reusable: hret, pre, setup
- **arm64 MustFromDecimalMain.lean** `Arm64.MustFromDecimalMain.Witness.nonvacuous`: 7 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 MustFromHex.lean** `Arm64.MustFromHex.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `by`; reusable: hret, pre, setup
- **arm64 NewInt.lean** `Arm64.NewInt.Witness.nonvacuous`: 1 contracts [NewobjectContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 PaddedBytes.lean** `Arm64.PaddedBytes.Witness.nonvacuous`: 1 contracts [MakesliceContract]; proof `⟨impl,`; reusable: hret, pre, setup
- **arm64 PrettyDec.lean** `Arm64.PrettyDec.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 Scan.lean** `Arm64.Scan.Byt.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.Nil.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.NoE.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.Other.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Scan.lean** `Arm64.Scan.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 SetFromDecimal.lean** `Arm64.SetFromDecimal.Witness.nonvacuous`: 7 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 String.lean** `Arm64.String.Witness.nonvacuous`: 1 contracts [RtContract]; proof `by`; reusable: hret, pre, setup
- **arm64 ToBig.lean** `Arm64.ToBig.Witness.nonvacuous`: 3 contracts [NewobjectLiveContract, WbLiveContract]; proof `by`; reusable: hret, implOK, inv0, model_new, model_wb1, model_wb2, pre, rt_eq, setup
- **arm64 UnmarshalJSONMain.lean** `Arm64.UnmarshalJSONMain.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 UnmarshalJSONMain.lean** `Arm64.UnmarshalJSONMain.Witness.unquoted`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 UnmarshalSSZMain.lean** `Arm64.UnmarshalSSZMain.Witness.nonvacuous`: 2 contracts [ConvT64, ErrorfLive]; proof `by`; reusable: pre0, setup
- **arm64 UnmarshalTextMain.lean** `Arm64.UnmarshalTextMain.Witness.hex`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 UnmarshalTextMain.lean** `Arm64.UnmarshalTextMain.Witness.nonvacuous`: 8 contracts [CmpstringContract, Ifaceeq, MallocgcLiveContract, MemmoveLive, NewobjectLiveContract, RtLiveContract, WbLiveContract]; proof `by`; reusable: (none in file: core module Fv256/<ISA>/*Wit*.lean)
- **arm64 Value.lean** `Arm64.Value.Witness.nonvacuous`: 2 contracts [RtLiveContract]; proof `by`; reusable: hret, pre, s0_inv, setup

Total witnesses: 82
## Update 2026-11-08: Janus pin for the full audit sweep = UP3b auditor 056c9381 (fixes the SetFromDecimal thin-witness size-walk reject), with JANUS_FRAMEWORK_STORE=/srv/janus-ops/fwstore.
Do it AFTER integrating fv/csa + fv/csb into fv/wrun. Build a janus worktree at 056c9381 (cp -a .lake from /srv/janus-wrun2, lake build Janus.Tools.Audit janus-audit, go build), bump the scratch lakefile rev.
The compile sweep (stub-correctness, pin 29ff3727, 4 parallel workers with their own scratch trees /srv/fv-uint256-wrun-aud{,2,3,4}) logs: scratchpad sw-<isa>-<fn>.log, results sw2-res-*.txt.
