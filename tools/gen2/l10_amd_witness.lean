namespace Witness

def ret : Nat := 0x200000
def sp0 : Nat := 0x100000
def zp : Nat := 0x30800
def val : Nat := 12345

/-- the return address in the slot at `[SP]`, the tables `pows64`/`pows` hold the powers of ten, `zp` holds `val`, everything else is zero -/
def bytes (a : Nat) : Byte :=
  if a = sp0 + 2 then 0x20
  else if P64 ≤ a ∧ a < P64 + P64sz then BitVec.ofNat 8 (10 ^ ((a - P64) / 8) / 256 ^ ((a - P64) % 8) % 256)
  else if PB ≤ a ∧ a < PB + PBsz then BitVec.ofNat 8 (10 ^ (20 + (a - PB) / 32) / 256 ^ ((a - PB) % 32) % 256)
  else if zp ≤ a ∧ a < zp + 32 then BitVec.ofNat 8 (val / 256 ^ (a - zp) % 256) else 0

def x : BitVec 64 := BitVec.ofNat 64 zp

def s0 : State :=
  { regs := fun i => if i = 0 then x else if i = 4 then BitVec.ofNat 64 sp0 else 0,
    rip := BitVec.ofNat 64 Extracted.entry, flags := ⟨none, none, none, none, none, none⟩,
    xmm := fun _ => 0,
    mem := ⟨bytes, [⟨sp0 - 8, 16, true⟩, ⟨P64, P64sz, false⟩, ⟨PB, PBsz, false⟩, ⟨zp, 0x100, false⟩]⟩ }

theorem hret : RetAddr Extracted.program ret := RetAddr.of_check (by decide)

theorem setup : CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s0 :=
  ⟨rfl, by decide, rfl, by decide, by intro i h; simp at h; subst h; rfl, rfl⟩

set_option maxRecDepth 100000 in
theorem hpre : StackWritable s0 8 8 ∧ Buffer s0 x 32 false ∧
    (x.toNat + 32 ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 8 ≤ x.toNat) ∧
    Tabs64 s0.mem ∧ TabsBig s0.mem ∧
    (P64 + P64sz ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 8 ≤ P64) ∧
    (PB + PBsz ≤ (s0.regs regSP).toNat - 8 ∨ (s0.regs regSP).toNat + 8 ≤ PB) :=
  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by decide, by unfold Tabs64; decide, by unfold TabsBig; decide,
    by decide, by decide⟩

theorem nonvacuous : ∃ (ret : Nat) (s : State) (x : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [x] s ∧
    (StackWritable s 8 8 ∧ Buffer s x 32 false ∧
      (x.toNat + 32 ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ x.toNat) ∧
      Tabs64 s.mem ∧ TabsBig s.mem ∧
      (P64 + P64sz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ P64) ∧
      (PB + PBsz ≤ (s.regs regSP).toNat - 8 ∨ (s.regs regSP).toNat + 8 ≤ PB)) :=
  ⟨ret, s0, x, hret, setup, hpre⟩

set_option maxRecDepth 100000 in
theorem returns : Returns (Extracted.program.withExit ret) s0 fun s' =>
    ABIReturn s0 s' ∧ (s'.regs 0).toNat = 4 := by
  refine (correctness x ret hret s0 setup hpre).mono ?_
  intro s' h
  refine ⟨h.1, ?_⟩
  have hv : valueAt s0 x 32 = 12345 := by unfold valueAt; decide
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

end Fv256.Amd64.Log10
