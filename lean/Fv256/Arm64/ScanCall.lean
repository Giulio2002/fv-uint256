import Fv256.Arm64.ScanSpec
import Fv256.Arm64.ScanSciSpec

/-!
# `Scan` (arm64): the call to `scanScientificFromString` (Extracted-free helpers)

`str_pre0`: the entry facts of the `sci` summary at the call state `S` of `Scan`, from `TopPre0` at the `Scan` entry state.
`str_post`: the documented result of the string `(p, n)` at the `Scan` level from the `sci` post.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.ScanSciSpec Fv256.Arm64.ScanSpec

namespace Fv256.Arm64.ScanCall

variable (C : SfdCfg)

theorem pr_frame_n {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)} {p n : Nat} (hF : MemFrame m m' ws)
    (h : Fv256.IndexByte.PageReadable m p n) : Fv256.IndexByte.PageReadable m' p n := by
  unfold Fv256.IndexByte.PageReadable at *
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr ⟨h.1, by rw [hF.accessible]; exact h.2⟩

theorem str_pre0 {p : Janus.Program} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pS nS : BitVec 64} {s S : State}
    (hpre : TopPre0 C R R2 T b L lo hi z pS nS (viewS s pS nS)) (h30a : (s.regs 30).toNat % 4 = 0)
    (h30b : (s.regs 30).toNat < 2 ^ 48)
    (hinit : InitDone C R2 s.mem) (hpage : Fv256.IndexByte.PageReadable s.mem pS.toNat nS.toNat) (hdl : p.DataLoaded s.mem)
    (hF : MemFrame s.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)]) (hreg : S.mem.regions = s.mem.regions)
    (hal : S.sp.toNat % 16 = 0)
    (hr0 : S.regs 0 = z) (hr1 : S.regs 1 = pS) (hr2 : S.regs 2 = nS)
    (h30a' : (S.regs 30).toNat % 4 = 0) (h30b' : (S.regs 30).toNat < 2 ^ 48)
    (hr28 : S.regs 28 = s.regs 28) (hlo : lo + 4640 ≤ S.sp.toNat) (hhi : S.sp.toNat + 32 ≤ hi) :
    SciPre C R R2 T b L lo hi z pS nS S ∧ InitDone C R2 S.mem ∧ p.DataLoaded S.mem := by
  have htop : TopPre C R R2 T b L lo hi z pS nS (viewS s pS nS) :=
    TopPre0.toTop C (by simpa [viewS, setReg_apply] using h30a) (by simpa [viewS, setReg_apply] using h30b) hpre
  obtain ⟨h0, h1, h2, hMod, hEnv, hlo4, hhi4, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS, hzg, hPA, hP48,
    hPW, hPZ, hCh⟩ := hpre
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := hEnv'
  have hv28 : (viewS s pS nS).regs 28 = s.regs 28 := by simp [viewS, setReg_apply]
  refine ⟨⟨?_, hlo, ?_⟩, ?_, ?_⟩
  · refine call_pre C htop (s0 := viewS s pS nS) (by simpa [viewS] using hF) hal (Nat.le_refl _) (Or.inl rfl) hzW
      (Or.inr ⟨Nat.le_refl _, Nat.le_refl _⟩) hP48 hr0 hr1 hr2 h30a' h30b' (by rw [hr28, hv28]) (by omega) hhi hzR hzPr hzS
      (by simpa [hv28] using hzg) (by rw [hF.accessible]; exact hzP.1) hzP.2
  · exact pr_frame_n hF hpage
  · obtain ⟨i1, i2, i3, i4, i5⟩ := hinit
    have o1 : Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)] := hE2
    have o2 : Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)] := hB2
    have r1 := hF.readLE C.ioEOF 8 (Outside.of_sub o1 (Nat.le_refl _) (by omega))
    have r2 := hF.readLE (C.ioEOF + 8) 8 (Outside.of_sub o1 (by omega) (by omega))
    have r3 := hF.readLE C.errBig 8 (Outside.of_sub o2 (Nat.le_refl _) (by omega))
    have r4 := hF.readLE (C.errBig + 8) 8 (Outside.of_sub o2 (by omega) (by omega))
    exact ⟨by rw [r1]; exact i1, by rw [r2]; exact i2, by rw [r3]; exact i3, by rw [r4]; exact i4, i5⟩
  · refine dl_frame hdl hF hreg (fun r hr => ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact e5
    · have h : s.mem.accessible z.toNat 32 true = true := hzP.1
      simpa using h


open Fv256.ScanSpec in
/-- a syntax error of `sciParse` names a chunk inside the string -/
theorem sciParse_syn_le {b : Nat → Nat} {n lo len : Nat} (h : sciParse b n = Res.syntax lo len) : lo + len ≤ n := by
  unfold sciParse at h
  split at h
  · simp at h
  · rename_i hn
    split at h
    · exact (Fv256.I.decParse_syntax b n lo len h).2.1
    · rename_i i hi
      have hi' := idxE_some hi
      split at h
      · split at h
        · simp at h
        · split at h
          · split at h <;> simp_all
          · rename_i lo2 len2 hd2
            simp only [Res.syntax.injEq] at h
            have := (Fv256.I.decParse_syntax _ _ lo2 len2 hd2).2.1
            omega
          · exact absurd h (by
              rename_i hx
              exact fun hh => hx lo len hh)
      · have := (Fv256.I.decParse_syntax b i lo len h).2.1
        omega


/-- the `sci` post at the call state `S` gives the documented result at the `Scan` entry state `s`: `(p, n)` is the string the
documentation talks about, `(pS, n)` the one `sci` scanned (the same bytes) -/
theorem str_post {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L L' : List (Nat × Nat)} {lo hi hi3 : Nat} {dst p pS nS : BitVec 64}
    {s S S3 : State}
    {W : List (Nat × Nat)} (hF : MemFrame s.mem S.mem (W ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]))
    (hWsub : ∀ a n, Outside a n (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) →
      Outside a n (W ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]))
    (hbytes : ∀ k, k < nS.toNat → S.mem.readLE (pS.toNat + k) 1 = s.mem.readLE (p.toNat + k) 1)
    (hp48 : p.toNat + nS.toNat ≤ 2 ^ 48) (hpS48 : pS.toNat + nS.toNat ≤ 2 ^ 48)
    (hio1 : S.mem.readLE C.ioEOF 8 = s.mem.readLE C.ioEOF 8)
    (hio2 : S.mem.readLE (C.ioEOF + 8) 8 = s.mem.readLE (C.ioEOF + 8) 8)
    (her1 : S.mem.readLE C.errBig 8 = s.mem.readLE C.errBig 8)
    (her2 : S.mem.readLE (C.errBig + 8) 8 = s.mem.readLE (C.errBig + 8) 8)
    (hsy1 : S.mem.readLE C.strconvErrSyntax 8 = s.mem.readLE C.strconvErrSyntax 8)
    (hsy2 : S.mem.readLE (C.strconvErrSyntax + 8) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8)
    (hLsub : ∀ r ∈ L, r ∈ L') (hh3 : hi3 ≤ hi) (hpost : SciPost C R R2 T b L' lo hi3 dst pS nS S S3) :
    ScanStrPost C R R2 L W lo hi dst p nS s S3 := by
  have hcong : ∀ r, Fv256.ScanSpec.sciParse (bytesAt S.mem pS.toNat) nS.toNat = r →
      Fv256.ScanSpec.sciParse (bytesAt s.mem p.toNat) nS.toNat = r := by
    intro r hr
    rw [← hr]
    exact (sciParse_congr _ _ _ (fun k hk => by
      show S.mem.readLE (pS.toNat + k) 1 = s.mem.readLE (p.toNat + k) 1
      exact hbytes k hk)).symm
  obtain ⟨-, -, -, -, -, -, hcases⟩ := hpost
  have hW1 : ∀ M : MemFrame S.mem S3.mem [(lo, hi3), (dst.toNat, dst.toNat + 32)],
      MemFrame s.mem S3.mem (W ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := fun M =>
    hF.trans M (fun a n h => ⟨h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨by rcases h.2.1 with h1 | h1 <;> omega, h.2.2⟩⟩)
  have hW2 : ∀ M : MemFrame S.mem S3.mem (R.rt ++ R2.priv ++ [(lo, hi3), (dst.toNat, dst.toNat + 32)]),
      MemFrame s.mem S3.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := fun M =>
    hF.trans M (fun a n h => ⟨hWsub a n h, by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact ⟨h.1, by rcases h.2.1 with h1 | h1 <;> omega, h.2.2⟩⟩)
  rcases hcases with ⟨v, hv, h0, h1, hval, hM⟩ | ⟨hv, h0, h1, hM⟩ | ⟨hv, h0, h1, hM⟩ | ⟨lo', len', hv, q, t, h0, h1, hTe, hM⟩
  · exact Or.inl ⟨v, hcong _ hv, h0, h1, hval, hW1 hM⟩
  · exact Or.inr (Or.inl ⟨hcong _ hv, by rw [h0, hio1], by rw [h1, hio2], hW1 hM⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hcong _ hv, by rw [h0, her1], by rw [h1, her2], hW1 hM⟩))
  · refine Or.inr (Or.inr (Or.inr ⟨lo', len', hcong _ hv, q, t, h0, h1, ?_, ?_⟩))
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, -⟩ := hTe
      have hlen : lo' + len' ≤ nS.toNat := sciParse_syn_le hv
      refine ⟨a1, a2, fun r hr => a3 r (hLsub r hr), fun r hr => a4 r (by
        rcases List.mem_append.1 hr with h | h
        · exact List.mem_append_left _ (hLsub r h)
        · exact List.mem_append_right _ h), a5, a6, a7, a8, by rw [a9, hsy1], by rw [a10, hsy2], ?_⟩
      intro k hk
      have hk' : k < len' := by
        have : (BitVec.ofNat 64 len').toNat = len' := by
          simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
        omega
      rw [a11 k hk]
      have e1 : (BitVec.ofNat 64 (pS.toNat + lo')).toNat = pS.toNat + lo' := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have e2 : (BitVec.ofNat 64 (p.toNat + lo')).toNat = p.toNat + lo' := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      have e3 : (BitVec.ofNat 64 len').toNat = len' := by
        simp only [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
      rw [e1, e2, Nat.add_assoc, Nat.add_assoc]
      exact hbytes (lo' + k) (by omega)
    · exact hW2 hM


theorem str_out2 {pS nS lo hi dst k : Nat} (hPW : nS = 0 ∨ pS + nS ≤ lo ∨ hi ≤ pS)
    (hPZ : nS = 0 ∨ pS + nS ≤ dst ∨ dst + 32 ≤ pS) (hk : k < nS) :
    Outside (pS + k) 1 [(lo, hi), (dst, dst + 32)] := by
  simp only [outside_cons, outside_nil, and_true]
  rcases hPW with h | h | h <;> rcases hPZ with h' | h' | h' <;> omega

/-- the constants `Scan`'s callees read (the sentinel errors, `strconv.ErrSyntax`) are unchanged by a frame of the window -/
theorem frame_consts {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {z pS nS : BitVec 64} {s0 S : State}
    (hpre : TopPre0 C R R2 T b L lo hi z pS nS s0)
    (hF : MemFrame s0.mem S.mem [(lo, hi), (z.toNat, z.toNat + 32)]) :
    (S.mem.readLE C.ioEOF 8 = s0.mem.readLE C.ioEOF 8 ∧ S.mem.readLE (C.ioEOF + 8) 8 = s0.mem.readLE (C.ioEOF + 8) 8) ∧
    (S.mem.readLE C.errBig 8 = s0.mem.readLE C.errBig 8 ∧ S.mem.readLE (C.errBig + 8) 8 = s0.mem.readLE (C.errBig + 8) 8) ∧
    (S.mem.readLE C.strconvErrSyntax 8 = s0.mem.readLE C.strconvErrSyntax 8 ∧
      S.mem.readLE (C.strconvErrSyntax + 8) 8 = s0.mem.readLE (C.strconvErrSyntax + 8) 8) := by
  obtain ⟨h0, h1, h2, hMod, hEnv, hlo4, hhi4, hMult, hE1, hE2, hMa, hMo, hMr, hMb, hB1, hB2, hzP, hzW, hzR, hzPr, hzS, hzg, hPA, hP48,
    hPW, hPZ, hCh⟩ := hpre
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -⟩ := hEnv
  have hsy := e14 (C.strconvErrSyntax, C.strconvErrSyntax + 16) (by simp [staticRanges])
  have hsz := hzS (C.strconvErrSyntax, C.strconvErrSyntax + 16) (by simp [staticRanges])
  simp only [outside_cons, outside_nil, and_true, Nat.add_sub_cancel_left] at hsy hsz
  have o : Outside C.strconvErrSyntax 16 [(lo, hi), (z.toNat, z.toNat + 32)] := by
    simp only [outside_cons, outside_nil, and_true]; exact ⟨hsy, hsz⟩
  exact ⟨⟨hF.readLE _ _ (Outside.of_sub hE2 (Nat.le_refl _) (by omega)), hF.readLE _ _ (Outside.of_sub hE2 (by omega) (by omega))⟩,
    ⟨hF.readLE _ _ (Outside.of_sub hB2 (Nat.le_refl _) (by omega)), hF.readLE _ _ (Outside.of_sub hB2 (by omega) (by omega))⟩,
    ⟨hF.readLE _ _ (Outside.of_sub o (Nat.le_refl _) (by omega)), hF.readLE _ _ (Outside.of_sub o (by omega) (by omega))⟩⟩


theorem strpost_congr {R : RtInv} {R2 : IfaceModel} {L W : List (Nat × Nat)} {lo hi : Nat} {dst p n : BitVec 64}
    {s S3 S3' : State} (hm : S3'.mem = S3.mem) (h0 : S3'.regs 0 = S3.regs 0) (h1 : S3'.regs 1 = S3.regs 1)
    (h : ScanStrPost C R R2 L W lo hi dst p n s S3) : ScanStrPost C R R2 L W lo hi dst p n s S3' := by
  unfold ScanStrPost SynObj at *
  simp only [hm, h0, h1]
  exact h


theorem acc_le48 {m : Janus.Arm64.Memory} {a n : Nat} {w : Bool} (h : m.accessible a n w = true) : a + n ≤ 2 ^ 48 := by
  unfold Janus.Arm64.Memory.accessible at h
  simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨r, -, h1⟩, -⟩ := h
  omega

end Fv256.Arm64.ScanCall
