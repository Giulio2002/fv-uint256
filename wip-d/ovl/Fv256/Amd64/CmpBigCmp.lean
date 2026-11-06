import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC64

open Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic

namespace Fv256.Amd64.CmpBigCmp

set_option maxHeartbeats 8000000 in
theorem cmp_summary (z x : BitVec 64) :
    Fv256.C.CmpSummary64 Extracted.program (segAddr Extracted.program "github.com/holiman/uint256.(*Int).Cmp") z x := by
  intro s hpc ⟨⟨hr1, hr2, hx15, hdf⟩, hz0, hx0, ⟨hzw, hz⟩, ⟨hxw, hx⟩⟩
  simp only [valueAt] at *
  janus64_run [Util.readLE_32]
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat )); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat )); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); have hl := Util.lt_out_iff _ _ _ _ _ _ _ _ (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24)); simp only [Util.cmp_ofInt]; (simp only [Util.subFlags_fst_toNat, BitVec.toNat_or, BitVec.toNat_sub, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.or_eq_zero_iff, Nat.reducePow, Nat.reduceMod, Util.ite_one_toNat] at *); dec_facts; (repeat' split) <;> (try simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Bool.false_eq_true, Bool.true_eq_false, BitVec.reduceEq]) <;> first | rfl | omega)

end Fv256.Amd64.CmpBigCmp
