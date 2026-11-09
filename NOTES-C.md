# FV-C handoff (fv/wc, worktree /srv/fv-uint256-wC, verify workspace /srv/fv-uint256-wC-v) -- written 2026-11-06

## State (all committed on fv/wc, HEAD after this note)
VERIFIED (janus 655a23fa, shared cache JANUS_CACHE_DIR=/srv/janus-ops/jcache-shared, private binary /srv/janus-fvc-n5/bin/janus):
- IntoBig amd64 (1119 s), ToBig amd64 (1260 s), arm64 ToBig/IntoBig (older pins).
- MarshalSSZAppend FULL spec: arm64 `Fv256.Arm64.MarshalSSZAppendMain` (857 s) and amd64 `Fv256.Amd64.MarshalSSZAppendMain` (1825 s),
  correctness + Witness.nonvacuous in ONE run each (scripts vA1.sh = /srv/fv-uint256-wC-v/va1.sh, vm1.sh). NO-GROWTH witness only
  (len=0, cap=32, ok = False). Runtime assumption `DescOK` (Fv256.Msa.DescOK in lean/Fv256/MsaCommon.lean).
PENDING:
1. Growth-path witnesses (both ISAs): blocked by Janus U-GROWMULTI (janus_live_growslice fails for old arrays >= 16 bytes: missing
   p + ob <= 2^48 for the stepper). Repro /srv/janus-ops/repros/GROWSLICE-MULTICHUNK/. Fix worker on branch agent/growmulti from 655a23fa
   will send a hash. Then: `python3 wipC/gen_growth_witness.py arm64|amd64 > lean/Fv256/<Isa>/MarshalSSZAppendMain.lean`
   (adds namespace Witness2 / theorem nonvacuous_grow: len=cap=32, one request growslice(p,40,32,8,u8), implAt growsliceSeg grA 32 64 64,
   tactic args `40 32 8 64 64`), compile in the workspace, then one janus verify with `--theorem ...Witness2.nonvacuous_grow` added.
2. MarshalSSZInto / UnmarshalSSZ (both ISAs) FULL spec incl. error path. NOT STARTED beyond prep. Existing partial proofs:
   lean/Fv256/Proofs/Arm64/{MarshalSSZInto,UnmarshalSSZ}.lean (success path only). Extractions with contracts fmt.errorf, runtime.convT64,
   runtime.newobject already exist: build/ex-{arm64,amd64}-{MarshalSSZInto,UnmarshalSSZ} (identity.json lists the contracts).
   Private Janus pinned at d58575d2 (agent/u-errorf, on U-LIVESAT 45fe2132): /srv/janus-wc-errorf (built, bin/janus). Repin to n7 or
   its successor when it lands as integ. amd64 waits for the U-ERRORF agent's amd64 ErrWrap.

## Plan for arm64 MarshalSSZInto (model files in /srv/janus-wc-errorf)
- Model: examples/proofs/ErrWrap.lean (446 lines; ErrorfLive hypothesis, `facts` lemma with ArgsOK/errorfReads/msgOf/errorfCost,
  Post with FreshFrom/MemFrame/LiveFrame/R.inv), Janus/Contracts/ErrorfConsumer.lean (`argsOK_real`: fmt "%w: have %d, want %d bytes"),
  and examples/proofs/Box.lean for the `runtime.convT64` box (pointer to a stack slot below SP).
- Go: MarshalSSZInto: `if len(dst) < 32 { return nil, fmt.Errorf("%w: have %d, want %d bytes", ErrBadBufferLength, len(dst), 32) }`
  then four PutUint64 and `return dst[32:], nil`. UnmarshalSSZ: same format with ErrBadEncodedLength when len(buf) != 32, else loads limbs.
- Spec shape: success branch = existing partial theorem (generalise preconditions as in Append: runtime variable R, frames); error branch:
  x0 = itab of *fmt.wrapError, x1 = fresh 32-byte object whose msg block = "<ErrBadBufferLength text>: have <len>, want 32 bytes"
  and whose err field is the package variable's interface value; receiver z and dst unchanged; memory changes only in rt + stack window.
  Needs: ErrorfLive hyp (tErr iErr tInt iWrap 26 fmtNum bound), convT64 contract for `len(dst)` (and the static 32), newobject if present,
  `ErrHolds`-style hypothesis for the package error variable.
- Use the block/segment approach (janus_run until [pc] ... calls [hf]) like Append; hide big hypotheses (Nonempty pack) before calls.

## Recipes / pitfalls learned (see also /srv/janus-ops/FV-NEW-BRIEF.md)
- `Hidden p := p` in MsaCommon hides MemFrame hyps from the stepper (a visible MemFrame s.mem S.mem _ makes the first store step stuck).
- DO NOT hide a conjunction with `Hidden`: the engine destructs it into inaccessible hyps and positional `rename_i` shifts.
  Use `replace pack := Nonempty.intro pack` ... `obtain ⟨pack⟩ := pack` (restore AFTER the second run).
- omega blowup in growslice-call preconditions: prove the arithmetic side conditions in a tiny-context lemma (grow_pre / grow_pre_a64 in
  MsaCommon) and hide the Apart/bounds hyps behind Nonempty during `janus_run ... calls [hg]`.
- The engine rewrites `S.mem.readLE (z+8k) 8` to `s.mem.readLE (z+8k) 8` (via hz8) in the call's memory chain for k >= 1: state
  `hMr`/`hM16`/`hgC` with the s.mem form, and pass `_` for the stored values in `writeLE_inRanges` (unifying with the S.mem form
  hangs elaboration without counting heartbeats).
- janus64_data/janus_data must be given hypotheses about `s.mem` (the DataLoaded memory), not the stepped `S.mem` (kernel mismatch).
- `lake build` of the MsaBlk modules in the kept workspaces takes ~10 min; `lake env lean File.lean` for a single block 2-3 min.
  Kept workspaces: arm64 /srv/janus-ops/jcache-shared/v1/consumer/0f9595d5210bb2fd31b91b7e/f3c45a1d622368ab125921cb/root,
  amd64 (older Janus p4405) /srv/fv-uint256-wC-v/cached/v1/consumer/65598f3779703d7a4873c376/f868c42ce5c62ec2dabfcff8/root.
- Never TaskStop Bash tasks; kill by PID. One heavy job at a time (heavy-run); queue waits are 20-40 min.
- BitVec.ofNat/toNat and `Ready` ambiguity: amd64 uses Fv256.Amd64.Msa.Ready, arm64 Fv256.Msa.Ready.
- Generators: wipC/genblk.py (amd64 blocks), genblk3f.py (amd64 final block, branch texts in wipC/b3fa/), genblk_a64.py, genblk3f_a64.py
  (branch texts wipC/b3f/), assemble_a64.py / assemble_amd64.py write lean/Fv256/<Isa>/MsaBlk*.lean. Base files: lean/Fv256/Proofs/Arm64/
  MarshalSSZAppendG.lean and wipC/MsaBlk0.amd64.lean (amd64 block 0; `assemble_amd64.py` copies it to lean/Fv256/Proofs/Amd64/MsaBlk0.lean).

## Coverage rows already sent to FV-A
MarshalSSZAppend arm64 verified 857 s, amd64 verified 1825 s (no-growth witness; growth-path witness pending); DescOK assumption note.
