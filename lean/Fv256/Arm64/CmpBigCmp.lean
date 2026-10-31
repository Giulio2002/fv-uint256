import Extracted
import Fv256.Spec
import Fv256.SpecC
import Fv256.Util
import Fv256.UtilC
import Fv256.SumC

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec

namespace Fv256.Arm64.CmpBigCmp

set_option maxHeartbeats 8000000 in
theorem cmp_summary (z x : BitVec 64) :
    Fv256.C.CmpSummary Extracted.program (segAddr Extracted.program "github.com/holiman/uint256.(*Int).Cmp") z x := by
  intro s hpc ⟨h30a, h30b, hz0, hx0, ⟨hz, hz'⟩, ⟨hx, hx'⟩⟩
  janus_run
  all_goals ((try have := Util.readLE8_lt s.mem (z.toNat)); (try have := Util.readLE8_lt s.mem (z.toNat + 8)); (try have := Util.readLE8_lt s.mem (z.toNat + 16)); (try have := Util.readLE8_lt s.mem (z.toNat + 24)); (try have := Util.readLE8_lt s.mem (x.toNat)); (try have := Util.readLE8_lt s.mem (x.toNat + 8)); (try have := Util.readLE8_lt s.mem (x.toNat + 16)); (try have := Util.readLE8_lt s.mem (x.toNat + 24)); (try simp only [janus_post] at *); (try simp only [Nat.or_eq_zero_iff] at *); simp only [Janus.Tactic.sub_flags_c, BitVec.toNat_not, BitVec.toNat_ofNat, Util.readLE8_mod, Nat.reducePow, Nat.reduceMod] at *; have hb := Util.borrow4_dec _ _ _ _ _ _ _ _ (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24)); have hzz := Util.zero4_iff _ _ _ _ _ _ _ _ (Util.readLE8_lt s.mem z.toNat) (Util.readLE8_lt s.mem (z.toNat + 8)) (Util.readLE8_lt s.mem (z.toNat + 16)) (Util.readLE8_lt s.mem (z.toNat + 24)) (Util.readLE8_lt s.mem x.toNat) (Util.readLE8_lt s.mem (x.toNat + 8)) (Util.readLE8_lt s.mem (x.toNat + 16)) (Util.readLE8_lt s.mem (x.toNat + 24)); (try simp only [hb, hzz, Util.ite01_eq1, Util.ite01_eq0] at *); simp only [Util.cmp_ofInt]; dec_facts; (repeat' split) <;> (try simp only [BitVec.reduceEq, BitVec.reduceNe]) <;> first | rfl | omega | exact ⟨trivial, rfl⟩)

end Fv256.Arm64.CmpBigCmp
