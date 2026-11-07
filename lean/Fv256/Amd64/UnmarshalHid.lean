namespace Fv256.Amd64.UnmarshalHid

/-- An opaque wrapper: a hypothesis `Hid P` is not scanned by the executor's side-condition discharger. -/
@[irreducible] def Hid (P : Prop) : Prop := P

theorem Hid.mk {P : Prop} (h : P) : Hid P := by unfold Hid; exact h
theorem Hid.get {P : Prop} (h : Hid P) : P := by unfold Hid at h; exact h

end Fv256.Amd64.UnmarshalHid
