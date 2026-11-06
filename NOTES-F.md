# FV-F notes (worktree /srv/fv-uint256-wf, branch fv/wf)

## reduce4 (amd64) -- internal library summary
`uint256.(*Int).reduce4` is an internal (unexported-in-spirit) helper of MulMod/MulModWithReciprocal, so it has no COVERAGE row of its own and no
Witness: it is proved as a **library summary** `Fv256.Amd64.Reduce4.reduce4_summary : R4Summary` over the Extracted-free program
`Fv256.ReduceProg` (lean/Fv256/Amd64/Reduce4.lean, commit 1862ab9).  Consumers (MulMod, MulModWithReciprocal, IMulMod, IMulModWithReciprocal
amd64) instantiate it with `Fv256.CodeIn.lib_summary`; their witnesses cover it end to end.
- Statement (lean/Fv256/Amd64/ReduceSpec.lean): `R4Pre` (Go ABI: RAX=z 32 B writable, RBX=x 64 B, RCX=m 32 B with nonzero top limb, RDI=mu 40 B;
  stack window 0x120, guard 0xb0, buffers apart from the frame, `RecipWeak m mu`), `R4Post` (z = x % m; rsp+8, rbp, r14, xmm15, df, mxcsr preserved;
  MemFrame [(z,z+32),(rsp-0x120,rsp),(rsp+8,rsp+0x10)], i.e. the return slot is untouched).
- Proof architecture (all `Extracted`-free, default heartbeats, no sorry, axioms propext/Classical.choice/Quot.sound):
  phase A (entry..0x1cd, 55 s, ReduceSegA) -> `linkA` (PostA -> live state) -> generated chain `R4G.C_1cd_4ac` (16 liveness-cut segments, 3-12 s each,
  tools/g4seg.py + g4chain.py) -> borrow branch (R4Branch) -> final `while r>=m` loop + epilogue (R4Tail.tail4, induction on r/m) -> arithmetic
  `R4Arith.reduce4_arith` (S1 q-estimate rows+capacities, S2 q*m mod 2^320, S3 5-limb subtract, bridge to `MulModTrunc.trunc_q`, `R4Value.r4_value`
  on `MulModMath.reduce_value`) -> composition `R4Reduce.reduce4_machine` (~140 s).
- Lessons: (1) never `omega` a whole carry chain; per-row weighted invariants with capacity hypotheses (`Psi_k = Psi_{k+1}`) and ANF (`tools/g4anf.py`
  generalises each `/2^64`, `%2^64`) close in seconds; (2) use decimal literals for the weights `2^k` in huge goals (`2 ^ 320 * x` made `whnf` time out);
  (3) a big existential post must be destructured in two steps and its equations kept behind an `abbrev` (80-variable obtain 197 s -> 50 s);
  (4) `omega` after a `janus64_run` with `decide`/borrow hypotheses in context can take 30+ min: use tiny helper lemmas for frame/interval side goals.
- Generators: tools/g4*.py (parameterised by the constants at the top of g4seg.py: ROOT, disassembly path, END, frame offset 288).
