import Fv256.ReduceProg
import Fv256.Spec
import Fv256.Util
import Fv256.SpecF
import Fv256.UtilF
import Fv256.MulModMath
import Fv256.MulModTrunc
import Fv256.Amd64.ReduceSpec

/-!
# `(*Int).reduce4(x *[8]uint64, m *Int, mu *[5]uint64) *Int` (amd64, library summary over `ReduceProg`)

Receiver `z` in `RAX`, `x` (64 bytes) in `RBX`, `m` in `RCX`, `mu` (40 bytes) in `RDI`.  For `m[3] ≠ 0` and `mu` in the `RecipWeak` window
the result at `z` is `x mod m`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.ReduceSum

open Fv256.Amd64.ReduceSpec

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem reduce4_summary : Summary Fv256.ReduceProg.program r4Entry R4Pre R4Post := by
  intro s hpc ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩
  have hgl := hg.load
  have hgb := hg.below
  have hnw2 := hg.noWrap
  have hgr := hg.readable
  simp only [regG, stackguard0Offset, regSP, stackguard0] at hgr hgb hgl hnw2 hdg
  simp only [regSP] at hacc hlow hnw hsp
  janus64_run [Util.readLE_32] until [r4Entry + 0x4da]
  all_goals trace_state
  all_goals sorry

end Fv256.Amd64.ReduceSum
