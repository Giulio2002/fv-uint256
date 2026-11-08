# NOTES-CSA-C2 (fork C2 of FV-CSA2): arm64 UnmarshalJSON / UnmarshalText / Scan call-site conjuncts

Scripts: scripts/cs_unm_a64.py NS... (NS = UnmarshalJSON | UnmarshalText; edits {NS}WitC.lean block + the 2 cores, {NS}Main.lean thin witnesses; NOT idempotent over a pristine file: it checks the CALLSITE-BLOCK marker only in WitC),
scripts/cs_scan_a64.py (ScanWitC block + Scan.lean 5 thin witnesses via callsite-splice.py --nth k).
Design: 8 conjuncts per witness (newobject/mallocgc/memmove/wb1/wb2 Live Sites with `L b` (= [] / budget), CmpstringPre 16, IfaceeqSite R2, RtLivePre sb), states = s0 with pc at stub entry + args from the toy `ok` list
(Unmarshal: regs0 numErrT / [1,0,0] / [loW,0x301000,1] / zeros / X0=0 / [0,0x302000,48]; Scan: base `st 0#64 0#64`, memmove dst 0xFD000). Cores: conjunct appended to each core's statement end and proof tuple; thin Main re-packs hc1..hc8.
Status: see bottom.

## Status log
- Scan arm64: AUDIT-PASS (stub) with 8 conjuncts x 5 witnesses (csa-q, 2597 s because of a cold cache after csa-row switched janus roots).
- UnmarshalJSON/Text: WitC cores compile (JSON verified via kept workspace lake env lean); Main thin witnesses inlined with scripts/cs_inline_c2.py (auditor cannot read obtain over a core) -- audit pending.
- janus-up3 got dirty (UP3b) -> csa-row.sh now points at a clean pin worktree (/srv/janus-csa).
- AUDIT-PASS (stub): UnmarshalJSON 894 s, UnmarshalText 357 s, Scan 2597 s (cold).
- FULL-PASS (non-stub, rc=0): Scan 4340 s, UnmarshalJSON 939 s. C2 rows done.
