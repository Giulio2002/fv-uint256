# Format path (ii) -- FV-F2 (branch fv/wf2, worktree /srv/fv-uint256-wf2) -- STATE 2026-11-07

amd64: DONE, sorry-free (axioms propext/choice/Quot.sound), checked in the kept janus workspace of build/ex2-amd64-Format
(`build/lre.sh`, lake build of every module, `lean/Fv256/Amd64/FormatFastAxioms.lean` prints the axioms of the top lemma).
NOT yet run through `janus verify` (these are lemmas, not an Ensures theorem; FV-G's assembly does the audit run).

Entry point for the assembly: `Fv256.Amd64.FormatFast.fast_amd64` (lean/Fv256/Amd64/FormatFastAll.lean):
  RT (Extracted.program.link impl) S0 [(retv, QFast), (Extracted.entry + 0x1cc, QBig)]
  S0 = state at Format+0x45 (just after the z != 0 split), `FPre` + FInv/Hist defs in lean/Fv256/FormatFastDefs.lean.
  `RT` = ordinary steps reach one of several addresses with a state predicate each (several-exit ReachesRet).
Modules (all under lean/Fv256/Amd64/): FormatFastW (Width site), P, F (5 Flag sites), B (branch segments), Sites, Sw (verb switch),
  Pre (pre_fast: Width..Flag chain + switch, 3 exits), Dec (Dec library summary), DecStr, Stb (stringtoslicebyte, Dec path),
  StbX (Hex path, [2:] slice), Wr (Write call + epilogue + ret; dec and hex variants), DecPath, HexSum/Hex/HexPath, All.
  FM/Hex.lean is GENERATED (scripts/gen-fm-hex-amd64.sh from Amd64/Hex.lean; retargeted at Format's extraction, plus an exported
  InRanges fact for the result string); the generated file is committed here, regenerate it after touching Hex.lean.
Extraction: scripts/contract-flags.sh Format (no mallocgc/memclr; stringtoslicebyte is a contract; memmove is CODE because the Dec
  library chain contains it).  build/ex2-{amd64,arm64}-Format.
Process: build/lre.sh FILE (PRE="mods to lake build first") = iterate in the kept workspace (path in build/ws-Amd64.txt).
  Create the workspace with build/vw.sh FormatFastDec probe (janus verify --keep-workspace; fails at the audit stage by design, but
  builds Extracted and the workspace).  Generators: scratch/gen_*.py (not part of the proof).

arm64: NOT STARTED.  The code has the same shape (see objdump of build/harness-arm64 at 0xb6030): call sites blr x1 with
  itab offsets 0x28/0x20/0x18 (flags), Dec at 0xb83c0, stringtoslicebyte contract at 0x6f390, Hex at 0xb7c90, Write blr x7 (+0x30),
  frame 80 bytes, tests are tbnz/tbz bit 0 (NOT the low byte), '-' and '#' use eor x2,x0,#1.  The proof pieces to port: FPre/FInv with
  the arm64 spill slots (str x1,[sp,#96]; x2,[sp,#104]; x0 -> [sp,#88]; w3 -> [sp,#112]), the Arm64 Iface namespace
  (Janus.Contracts.Iface, ICallContract), dec_summary (Arm64/DecSummary.lean), Hex (Arm64/Hex.lean, needs a Summary retarget like FM/Hex),
  stringtoslicebyteSpec via RtContract.  Expect the same recipes; the amd64 files are the template.

## HANDOVER (FV-F2 context exhausted after amd64; arm64 NOT started)
Caveats to check/close on amd64 before relying on it:
1. Only compiled with lake/lean in the kept janus workspace (build/ws-Amd64.txt, extraction build/ex2-amd64-Format, pin d52a1656); no `janus verify`
   (kernel replay / audit) has been run on these lemmas, because they are lemmas (the audit wants an Ensures-style theorem). FV-G's assembly run does it.
2. NO satisfiability / non-vacuity check was written for the hypothesis bundle of `fast_amd64` (FPre + the readiness hypotheses hH1 hH2 hHst hHx hHstx, which are
   universally quantified over all MemFrame memories M, plus the data/rt/guard facts).  Per the 2026-11-07 RULE this must be done early in the assembly witness.
3. Hex: the amd64 Hex proof had to be strengthened to export `InRanges ptr len rt` of the result string (Hex's own HexOut does not say where the string lives, and
   stringtoslicebyte's ReadsOutside needs it).  Done by the python patch inside scripts/gen-fm-hex-amd64.sh (generated file FM/Hex.lean); the original
   Amd64/Hex.lean (FV-E's) is untouched.  The Hex summary needs the extra hypothesis hcH over `P0H impl` (the slicebytetostring contract linked with Hex alone).
4. df/fsBase are not tracked after the Dec/Hex summaries (FInvD); nothing downstream needs them.
5. `hexoff` (Defs) = the `[2:]` offset arithmetic by finite check; `hexDigits_le64`, `strBytes_drop2` glue.
arm64 plan (template = the amd64 files, same names with an A64 suffix): see "arm64: NOT STARTED" above for the code shape.  Suggested order:
   FPre/FInv/FL for arm64 (SP-relative; spills sp+88/96/104/112; frame 80; saved x29/x30 at sp+72/sp+64 after the prologue -- check the prologue
   `str x30,[sp,#-80]!; stur x29,[sp,#-8]; sub x29,sp,#8`), w_call with ICallContract (retStateX, janus_run), the branch segments (tbnz bit 0),
   Dec summary from Arm64/DecSummary.lean, Hex summary (retarget Arm64/Hex.lean with a generator like scripts/gen-fm-hex-amd64.sh; Janus.Ensures.toSummaryIn),
   stringtoslicebyte via RtContract, Write (ICallContract nargs 4: x0 = data, x1 = ptr, x2 = len, x3 = cap), epilogue `ldur x29; ldr x30,[sp],#80; ret`.
