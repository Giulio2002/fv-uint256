# NOTES-INH (FV-INH, branch fv/inh off fv/master 47243a67, lakefile pin 51d592da kept)

U-ICALL-INHABITED lemmas (UP3 audit rule, /srv/janus-up3 NOTES-UP3.md): for every main theorem with an ICallContract[64] whose
call-site property P is not `fun _ => True`, a kernel-checked `∃ vars, ∃ s, ICallPre[64] nargs stack above rt P s`.

## Lemmas (all in namespace of the main theorem's ISA)
| lemma | file | covers (main theorem, hypothesis) |
|---|---|---|
| Fv256.Arm64.EncodeRLP.erlp_pre_inhabited | Arm64/ErlpInhabit.lean | Arm64.EncodeRLP.correctness `hw` (stack, 96, WP z w) |
| Fv256.Amd64.EncodeRLP.erlp_pre_inhabited | Amd64/ErlpInhabit.lean | Amd64.EncodeRLP.correctness `hw` (stack, 56) |
| Fv256.{Arm64,Amd64}.FormatInhabit.wr_pre_inhabited | {Arm64,Amd64}/FormatInhabit.lean | Format.correctness `hWr` (FastWP data (fastBytes zv ch)), nargs 4, above 120 / 80 |
| Fv256.{Arm64,Amd64}.FormatInhabit.bf_pre_inhabited | same | Format.correctness `hBf` (math/big.(*Int).Format, BigObj receiver) |
| Fv256.{Arm64,Amd64}.FormatInhabit.fp_pre_inhabited | {Arm64,Amd64}/FormatInhabitNil.lean | Format.correctness `hFp` (fmt.Fprint, FpArg data), nargs 5, above 80 |
`fp_pre_inhabited_gen` (same files as FormatInhabit) is the address-generic form; FormatInhabitNil instantiates it at strTyA/hdrA/litA.
Shared extraction-free helpers: lean/Fv256/InhabBase.lean (flatMem/strMem, callSt/callSt64 and callSt_pre/callSt64_pre, strOut_strMem,
strOut_writeLE, readLE_flatMem). These are the reusable call states for the returning-run witnesses.
Imports added: Arm64/Format, Amd64/Format (FormatInhabit, FormatInhabitNil), Arm64/EncodeRLP, Amd64/EncodeRLP (ErlpInhabit).
The `hW/hP/hF` Width/Precision/Flag contracts have P = `fun _ => True`: no lemma needed. FormatFast*/FormatBig*/Erlp* helper modules
carry ICallContract in sub-lemma statements, not main theorems; not covered (ask UP3 for corpus list to confirm).

## Evidence
- Extraction-free modules (InhabBase, *ErlpInhabit, *FormatInhabit) compiled with lean against the 51d592da library.
- Extraction-dependent FormatInhabitNil (both ISAs) and ErlpInhabit built with `lake build` in kept janus workspaces for ex-arm64-Format / ex-amd64-Format: success.
- RELEASE=1 scripts/no-sorry.sh: OK (incl. IO lint).
- NOT done: audit acceptance by UP3's auditor. Two attempts: janus verify of a sorry-stubbed Format.correctness needs the lake pin == UP3 head (UP3 moved 43807329 -> 9fd3862a -> 1de13d78 during the work); the last run was killed per coordinator (cold framework build each repin). Plain `janus verify` with the 51d592da binary rejects a lemma-only theorem ("statement does not mention Extracted.program"), as expected: lemmas are found by statement among imported modules, not verified on their own.
- #print axioms on all final lemmas (ErlpInhabit, wr/bf/fp_gen): only propext, Classical.choice, Quot.sound (fp_pre_inhabited itself is a one-line instance of fp_pre_inhabited_gen).

## Pending (upgrade workers)
New UP3 rule: witnesses need a returning run (U-WITNESS-RUN); the Format and EncodeRLP witnesses will need that.
Jcache /srv/janus-ops/jcache-inh deleted at end.
