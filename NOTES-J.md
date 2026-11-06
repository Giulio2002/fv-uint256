# NOTES-J (FV-J): MulMod / MulModWithReciprocal glue (arm64 + amd64) -- branch fv/wj, worktree /srv/fv-uint256-wJ

## Env
- build/lc.sh FILE (absolute, no Extracted import) compiles into build/ol655; build/lcx.sh TAG FILE for files importing Extracted:
  TAG mm = ex-arm64-MulMod, rm = ex-arm64-MulModWithReciprocal, am = ex-amd64-MulMod, ar = ex-amd64-MulModWithReciprocal
  (Extracted.olean per tag in build/X-<tag>; Extracted-dependent oleans go to ol655 -- never mix tags in one file set).
- Pin 655a23fa (janus-fvA-pin655 binary). `lake update janus` done in lean/. oleans of other modules copied from /srv/fv-uint256-wg/scratch655.

## arm64 (all compile; glue parametrised over reduce4 (R4Summary) and Reciprocal (RecipSummary))
- Arm64/MulModSum (mulmod_summary hRec hR4), MulModRecSum (mulmodrec_summary hR4), MulModCorr / MulModRecCorr (correctness_param),
  MulModWit / MulModRecWit (Witness.nonvacuous), MulModLem (tail lemmas, copy40, ge192...), MulModDefs (RecipSummaryU = RecPre/RecSpec unfolded).
- RecipDefs/RecipProg/RecipSpecA copied from fv/wb5; ReduceSpec from fv/wb3 (713cac4). Statements negotiated with the callee owners:
  R4Post has x18 and frame [(sp-168, sp-8), (sp+8, sp+16)]; RecSpec needs x18 and frame [(sp-280, sp-8), (sp+8, sp+48)] (my local RecipSpecA/MulModDefs already assume it).
- ~2m10 per summary (janus_run). Instantiation TODO: replace the hypotheses hRec/hR4 by recip_summary (via MulModDefs.recipU_of) and reduce4 summary,
  define `correctness` (hypothesis free) in Arm64/MulModCorr + Witness in same namespace, then ONE verify: 
  janus verify build/ex-arm64-MulMod --proof lean/Fv256/Arm64/MulModWit.lean --proof-root lean --theorem Fv256.Arm64.MulModCorr.correctness --theorem Fv256.Arm64.MulModCorr.Witness.nonvacuous
  (witness namespaces: Fv256.Arm64.MulModCorr.Witness / Fv256.Arm64.MulModRecCorr.Witness).

## amd64 (compile; parametrised over Fv256.Amd64.ReduceSpec.R4Summary; Reciprocal via recip_summary)
- Amd64/MulModSum (correctness_param hR4 z x y m), MulModRecSum (correctness_param hR4 z x y m mu), MulModWit / MulModRecWit
  (Witness.nonvacuous in Fv256.Amd64.MulMod.Witness / MulModRec.Witness), MulModLemA, MulModDefsA (RecipSummaryU), ReduceSpec from fv/wf 592584f.
- ~35 s each. TODO final: Amd64/MulMod.lean with `theorem correctness ... := correctness_param reduce4_summary ...` in namespace Fv256.Amd64.MulMod.

## Spec
z = F.mulmodSpec x y m (0 if m = 0, else x*y mod m); MulModWithReciprocal under F.MuOK m mu (2^192 <= m -> RecipWeak m mu). z/x/y/m may alias (apart from the stack window only).
