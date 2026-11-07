import Janus
theorem hb_eq (x c : Nat) (hx : x < 256) (hc : c < 256) :
    (BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x))) - BitVec.ofNat 8 c = 0#8) ↔ x = c := by
  have h1 : BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 (BitVec.ofNat 8 x))) = BitVec.ofNat 8 x := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [h1]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp [BitVec.toNat_sub, BitVec.toNat_ofNat] at this
    omega
  · rintro rfl
    simp
