import Fv256.Amd64.SfdTeBody

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64 Fv256.I Fv256.Amd64.SfdEnv

namespace Fv256.Amd64.SfdToError

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 20000 in
theorem te_sum1 (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (hl : R2.Laws)
    (T b : Nat) (L : List (Nat × Nat)) (fp fl sp sl : BitVec 64)
    (hif : Ifaceeq (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.ifaceeq") R2)
    (hnew : NewobjectLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") 4096 R)
    (hmg : MallocgcLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.mallocgc") 4096 R)
    (hmv : MemmoveLive64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.memmove") 4096 R)
    (hwb1 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier1") 4096 R 1)
    (hwb2 : WbLiveContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.gcWriteBarrier2") 4096 R 2) :
    Summary (Extracted.program.link impl) te (fun s => TePre R R2 T b L fp fl sp sl s ∧ ¬ s.mem.readLE 6156064 4 = 0) (TePost R R2 b L fp fl sp sl) := by
  intro s hpc ⟨⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, h7, h9, h10, hsl1, hsl2, hg, ⟨hlow, hnw, hacc⟩, hal, hNT1, hNT2, hNa, hIa, hSa, hdep, hc2,
    hout, hinv, hLs, hbud, hTd, hTty, hTreg, hTnd, hTsz, hoI, hoS, hoE, hoW, hoN, hprR, hLpr, hnR, hwR, hsRe, hokm, hokn, hokv, hokb1, hokb2, hsacc, hsp48, hsdisj, hgdis, hgR, hrt0, hnP, hwP, hePr, hwbacc, heacc, hspR, hspP⟩, hfl⟩
  te_body


end Fv256.Amd64.SfdToError
