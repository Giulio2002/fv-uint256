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
