import Fv256.Amd64.SfdFdHd

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Janus.Contracts.IfaceAmd64
  Fv256.Amd64.SfdEnv Fv256.Amd64.SfdToError Fv256.Amd64.SfdBridge Fv256.Amd64.SfdPw Fv256.I Fv256.Amd64.SfdFd

namespace Fv256.Amd64.SfdFd

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 20000 in
/-- the empty string: `io.EOF`, `z` zeroed -/
theorem fd_eof (impl : List Janus.Amd64.Segment) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat))
    (lo hi : Nat) (z pS nS : BitVec 64) (s : State) (hpc : s.rip = BitVec.ofNat 64 fd)
    (hpre : FdPre R R2 T b L lo hi z pS nS s) (hn : nS = 0) :
    ReachesRet (Fv256.Amd64.SfdProg.program.link impl) (retAddrOf s) s (FdPost R R2 T b L lo hi z pS nS s) := by
  obtain ⟨⟨hra1, hra2, hx15, hdf⟩, h0, h3, h1, hn78, hMod, hEnv, hlo, hhi, hMult, hEOF, hEOFo, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, ⟨hpw, hp⟩, hpW, hpz, hCA, hfin⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := hEnv'
  have hgl : Amd64.load s.mem ((s.regs 14).toNat + 16) 8 = .ok (s.mem.readLE ((s.regs 14).toNat + 16) 8) := by
    simp [Amd64.load, e7]
  have hacc : s.mem.accessible ((s.regs 4).toNat - 144) 168 true = true :=
    Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  have hE0 := hEOFo
  simp only [outside_cons, outside_nil, and_true] at hE0
  obtain ⟨hE1', hE2'⟩ := hE0
  have hE1 : 5995600 + 16 ≤ lo ∨ hi ≤ 5995600 := hE1'
  have hE2 : 5995600 + 16 ≤ z.toNat ∨ z.toNat + 32 ≤ 5995600 := hE2'
  have hEacc : s.mem.accessible 5995600 16 false = true := hEOF
  have hs4 : (s.regs 4 + 8#64).toNat = (s.regs 4).toNat + 8 := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; have := (s.regs 4).isLt; simp only [Nat.reducePow] at *; omega
  subst hn
  janus64_run [h0, h1, hacc, hE1, hE2, hEacc]
  have hn0 : (0#64 : BitVec 64).toNat = 0 := rfl
  have hl8 : ∀ a, (BitVec.ofNat 64 (s.mem.readLE a 8)).toNat = s.mem.readLE a 8 := fun a => by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (Util.readLE8_lt _ _)
  all_goals (
    unfold FdPost Fv256.C.Kept
    refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · simp [retAddrOf]
    · simp [setRegF_apply]
    · simp [setRegF_apply]
    · simp [setRegF_apply]
    · rfl
    · simp [hdf]
    · rfl
    · rw [hn0]; exact fromDec_eof _
    · simp [setRegF_apply, hl8]; rfl
    · simp [setRegF_apply, hl8]; rfl
    · dsimp only
      unfold Janus.Spec.val256
      exact zero32 _ z.toNat
    · refine Env.frame hMod.1 hEnv ?_ (by simp [setRegF_apply]) ?_ hzR hzP hzS hzg
      · show lo ≤ (s.regs 4 + 8#64).toNat ∧ (s.regs 4 + 8#64).toNat + 8 ≤ hi ∧ (s.regs 4 + 8#64).toNat % 8 = 0
        rw [hs4]; refine ⟨by omega, by omega, by omega⟩
      · dsimp only
        repeat' first
          | exact MemFrame.refl _ _
          | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
          | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega)
    · dsimp only
      repeat' first
        | exact MemFrame.refl _ _
        | refine MemFrame.writeLE ?_ _ (r := (lo, hi)) (by simp) (by omega) (by omega)
        | refine MemFrame.writeLE ?_ _ (r := (z.toNat, z.toNat + 32)) (by simp) (by omega) (by omega))

end Fv256.Amd64.SfdFd
