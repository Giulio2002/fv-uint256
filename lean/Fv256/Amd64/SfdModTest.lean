import Fv256.Amd64.SfdTopSpec
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.Amd64.SfdTopSpec
theorem mod_contra (C : SfdCfg) (R : RtInv) (R2 : IfaceModel) (T : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (s : State)
    (b : Nat) (hM : Mod C R R2 T L) (hE : Env C R R2 T b L lo hi s) : False := by
  obtain ⟨hl, -, -, -, -, -, -, hsp, -⟩ := hM
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hS, hR2, -⟩ := hE
  have hIsT : R2.IsType T := hS.2.1
  obtain ⟨-, -, -, hin⟩ := hl.type_desc s.mem (s.regs 14) T hR2 hIsT
  obtain ⟨r, hr, h1, h2⟩ := hin
  have ho : Outside T 48 R2.priv := by
    have := hsp (T, T + 48) (by simp [staticRanges])
    simpa using this
  have := MemFrame.outside_mem ho hr
  have h3 : (48:Nat) = typeDescSize := rfl
  omega
#print axioms mod_contra
