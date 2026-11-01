namespace Witness

def ret : Nat := 0x1000
def sp0 : Nat := 0x100000
def g0 : Nat := 0x200000
def zp : Nat := 0x30800
def val : Nat := 12345

/-- the tables `pows64`/`pows` hold the powers of ten, `zp` holds `val`, everything else is zero -/
def bytes (a : Nat) : Byte :=
  if 1772992 ≤ a ∧ a < 1772992 + 160 then BitVec.ofNat 8 (10 ^ ((a - 1772992) / 8) / 256 ^ ((a - 1772992) % 8) % 256)
  else if 1777472 ≤ a ∧ a < 1777472 + 1920 then BitVec.ofNat 8 (10 ^ (20 + (a - 1777472) / 32) / 256 ^ ((a - 1777472) % 32) % 256)
  else if zp ≤ a ∧ a < zp + 32 then BitVec.ofNat 8 (val / 256 ^ (a - zp) % 256) else 0

def x : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 28 then BitVec.ofNat 64 g0
      else if i = 29 then BitVec.ofNat 64 sp0 - 8#64 else if i = 30 then BitVec.ofNat 64 ret else 0,
    sp := BitVec.ofNat 64 sp0, pc := BitVec.ofNat 64 Extracted.entry,
    flags := ⟨false, false, false, false⟩,
    mem := ⟨bytes, [⟨sp0 - 32, 32, true⟩, ⟨g0, 0x100, false⟩, ⟨1772992, 160, false⟩, ⟨1777472, 1920, false⟩, ⟨zp, 0x100, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, rfl, by intro r h; simp at h; rcases r with _ | r <;> simp [s0] at h ⊢ <;> omega⟩

set_option maxRecDepth 100000 in
theorem hpre : GuardOK s0 0 ∧ StackOK s0 32 0 ∧ Extracted.program.DataLoaded s0.mem ∧ Ptr32 s0.mem x false ∧
    Disjoint x.toNat 32 (s0.sp.toNat - 32) 32 ∧ Tabs64 s0.mem ∧ TabsBig s0.mem ∧
    Disjoint 1772992 160 (s0.sp.toNat - 32) 32 ∧ Disjoint 1777472 1920 (s0.sp.toNat - 32) 32 :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide, by decide, by decide⟩, by unfold Program.DataLoaded; decide,
    ⟨by decide, by decide⟩, by unfold Disjoint; decide, by unfold Tabs64; decide, by unfold TabsBig; decide,
    by unfold Disjoint; decide, by unfold Disjoint; decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (GuardOK s 0 ∧ StackOK s 32 0 ∧ Extracted.program.DataLoaded s.mem ∧ Ptr32 s.mem x false ∧
      Disjoint x.toNat 32 (s.sp.toNat - 32) 32 ∧ Tabs64 s.mem ∧ TabsBig s.mem ∧
      Disjoint 1772992 160 (s.sp.toNat - 32) 32 ∧ Disjoint 1777472 1920 (s.sp.toNat - 32) 32) :=
  ⟨ret, s0, x, hret, setup, hpre⟩

set_option maxRecDepth 100000 in
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 4 := by
  refine (correctness x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  have hv : val256 s0.mem x.toNat = 12345 := by unfold val256; decide
  have h2 := h.2.2 (by rw [hv]; decide)
  rw [hv] at h2
  obtain ⟨h3, h4⟩ := h2
  generalize (s'.regs 0).toNat = r at h3 h4 ⊢
  rcases Nat.lt_or_ge r 5 with hr | hr
  · rcases Nat.lt_or_ge r 4 with hr4 | hr4
    · have : 10 ^ (r + 1) ≤ 10 ^ 4 := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · omega
  · have : 10 ^ 5 ≤ 10 ^ r := Nat.pow_le_pow_right (by decide) hr
    omega

end Witness

end Fv256.Arm64.Log10
