import Fv256.Proofs.Amd64.ScanSpec
import Fv256.Proofs.Amd64.ScanSfd
import Fv256.Proofs.Amd64.ScanIdx
import Fv256.Proofs.Amd64.ScanIbsCall
import Fv256.Proofs.Common.DecCongr

/-!
# `Scan` -> `scanScientificFromString`: the call-site facts (Extracted-free)
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Amd64.SfdTopSpec Fv256.Amd64.ScanSpec Fv256.ScanSpec Fv256.Amd64.ScanSfd Fv256.Amd64.ScanIdx

namespace Fv256.Amd64.ScanBPre

variable (C : SfdCfg)

set_option maxRecDepth 100000

/-- `TopPre0` (and `RetOK`) of the `scanScientificFromString(dst, p, n)` call made from the frame of `Scan` for a string source (window
`[lo, sp - 40)`, same live set): `s` is the entry state (viewed with the string in `RBX`/`RCX`), `S` the call state -/
theorem pre_str {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst p n : BitVec 64} {s S : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s) (hlo : lo + 4992 ≤ (s.regs 4).toNat)
    (hF1 : MemFrame s.mem S.mem [(lo, hi)]) (hret : S.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 47)
    (h4 : S.regs 4 = s.regs 4 - 72#64) (h0 : S.regs 0 = dst) (h3 : S.regs 3 = p) (h1 : S.regs 1 = n)
    (h14 : S.regs 14 = s.regs 14) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) :
    RetOK S ∧ TopPre0 C R R2 T b L lo ((s.regs 4).toNat - 40) dst p n S := by
  have hp0 := hp
  obtain ⟨-, -, -, hMod, hEnv, -, hhi, -, -, -, -, -, -, -, -, -, ⟨hzw, hz⟩, hzW, hzR, hzP, hzS, hzg, -⟩ := hp0
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, -⟩ := hEnv'
  have hsp := (s.regs 4).isLt
  have hs4 : (S.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [h4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hF2 : MemFrame s.mem S.mem [(lo, hi), (dst.toNat, dst.toNat + 32)] :=
    hF1.mono (fun a n h => by simp only [outside_cons, outside_nil, and_true] at h ⊢; exact h.1)
  have hE3 : Env C R R2 T b L lo ((s.regs 4).toNat - 40) S :=
    env_sub C hMod hEnv hF1 h14 (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_, toppre_sub C hp (by omega) hF2 hE3 h0 h3 h1 (by omega) (by omega) (Nat.le_refl _) (by omega) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  · unfold RetOK
    rw [hs4, hF1.accessible]
    refine ⟨?_, ?_, hx15, hdf⟩
    · exact Janus.Arm64.Memory.accessible_sub s.mem e5 (Or.inl rfl) (by omega) (by omega)
    · exact hret
  · intro a k h
    simp only [outside_cons, outside_nil, and_true] at h ⊢
    omega
  · exact ⟨hzw, by rw [hF1.accessible]; exact hz⟩
  · omega
  · exact hzR
  · exact hzP
  · exact hzS
  · rw [h14]; exact hzg
  · by_cases h0' : n.toNat = 0
    · exact Or.inl h0'
    · obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hp
      exact h

theorem sciParse_congr (b b' : Nat → Nat) (n : Nat) (h : ∀ k, k < n → b k = b' k) : sciParse b n = sciParse b' n := by
  by_cases hn : n = 0
  · simp [sciParse, hn]
  · have hid : idxE b n = idxE b' n := by
      unfold idxE
      exact Fv256.Amd64.ScanIbsCall.find_congr _ _ _ (fun i hi => by simp only [h i (List.mem_range.1 hi)])
    cases hi : idxE b n with
    | none =>
      have hi' : idxE b' n = none := by rw [← hid, hi]
      rw [sciParse_none b n hn hi, sciParse_none b' n hn hi']
      exact Fv256.I.decParse_congr _ _ _ h
    | some i =>
      have hi' : idxE b' n = some i := by rw [← hid, hi]
      have hin := (idxE_byte b n i hi).1
      have hd : decParse b i = decParse b' i := Fv256.I.decParse_congr _ _ _ (fun k hk => h k (by omega))
      by_cases hok : ∃ v, decParse b i = Res.ok v
      · obtain ⟨v, hv⟩ := hok
        have hv' : decParse b' i = .ok v := by rw [← hd, hv]
        rw [sciParse_some_ok b n i v hn hi hv, sciParse_some_ok b' n i v hn hi' hv']
        have e1 : b (i + 1) = b' (i + 1) ∨ ¬ (n - (i + 1) = 1) := by
          by_cases h1 : n - (i + 1) = 1
          · exact Or.inl (h _ (by omega))
          · exact Or.inr h1
        have e2 : decParse (fun k => b (i + 1 + k)) (n - (i + 1)) = decParse (fun k => b' (i + 1 + k)) (n - (i + 1)) :=
          Fv256.I.decParse_congr _ _ _ (fun k hk => h _ (by omega))
        rcases e1 with e1 | e1
        · rw [e1, e2]
        · rw [e2]; simp [e1]
      · have hno : ∀ v, decParse b i ≠ Res.ok v := fun v hv => hok ⟨v, hv⟩
        have hno' : ∀ v, decParse b' i ≠ Res.ok v := fun v hv => hno v (by rw [hd, hv])
        rw [sciParse_some_nonok b n i hn hi hno, sciParse_some_nonok b' n i hn hi' hno', hd]

theorem sciParse_syntax_bound (b : Nat → Nat) (n l m : Nat) (h : sciParse b n = .syntax l m) : l + m ≤ n := by
  by_cases hn : n = 0
  · simp [sciParse, hn, Res.ok, Res.syntax] at h
  · cases hi : idxE b n with
    | none =>
      rw [sciParse_none b n hn hi] at h
      have := Fv256.I.decParse_syntax _ _ _ _ h
      omega
    | some i =>
      have hin := (idxE_byte b n i hi).1
      by_cases hok : ∃ v, decParse b i = Res.ok v
      · obtain ⟨v, hv⟩ := hok
        rw [sciParse_some_ok b n i v hn hi hv] at h
        by_cases h1 : n - (i + 1) = 1 ∧ b (i + 1) = 48
        · rw [ite_eq_left h1] at h; simp [Res.ok, Res.syntax] at h
        · rw [ite_eq_right h1] at h
          split at h
          · split at h <;> simp [Res.ok, Res.syntax, Res.range] at h
          · rename_i lo2 len2 heq
            have h2 : i + 1 + lo2 = l ∧ len2 = m := by simpa [Res.syntax] using h
            have := Fv256.I.decParse_syntax _ _ _ _ heq
            omega
          · rename_i r hr1 hr2
            exact absurd h (hr2 l m)
      · have hno : ∀ v, decParse b i ≠ Res.ok v := fun v hv => hok ⟨v, hv⟩
        rw [sciParse_some_nonok b n i hn hi hno] at h
        have := Fv256.I.decParse_syntax _ _ _ _ h
        omega

/-- `ScanStrPost` of a call on the string `(p0, n)` in the call state `S` is `ScanStrPost` of the whole string `(p, n)` in the entry state `s`,
when the bytes and the static words agree -/
theorem strpost_transport {R : RtInv} {b b' : Nat} {L L' : List (Nat × Nat)} {lo hi lo' hi' : Nat}
    {dst p0 p n : BitVec 64} {s S s' : State}
    (hpw : p.toNat + n.toNat < 2 ^ 64) (hp0w : p0.toNat + n.toNat < 2 ^ 64)
    (hbytes : ∀ k, k < n.toNat → S.mem.readLE (p0.toNat + k) 1 = s.mem.readLE (p.toNat + k) 1)
    (hL : ∀ r ∈ L, r ∈ L')
    (heof : S.mem.readLE C.ioEOF 8 = s.mem.readLE C.ioEOF 8) (heof8 : S.mem.readLE (C.ioEOF + 8) 8 = s.mem.readLE (C.ioEOF + 8) 8)
    (herr : S.mem.readLE C.errBig 8 = s.mem.readLE C.errBig 8) (herr8 : S.mem.readLE (C.errBig + 8) 8 = s.mem.readLE (C.errBig + 8) 8)
    (hsy : S.mem.readLE C.strconvErrSyntax 8 = s.mem.readLE C.strconvErrSyntax 8)
    (hsy8 : S.mem.readLE (C.strconvErrSyntax + 8) 8 = s.mem.readLE (C.strconvErrSyntax + 8) 8)
    (hpost : ScanStrPost C R b' L' lo' hi' dst p0 n S s') : ScanStrPost C R b L lo hi dst p n s s' := by
  have hc : sciParse (bytesAt S.mem p0.toNat) n.toNat = sciParse (bytesAt s.mem p.toNat) n.toNat :=
    sciParse_congr _ _ _ (fun k hk => hbytes k hk)
  unfold ScanStrPost at hpost ⊢
  rcases hpost with ⟨v, hv, h0, h3, hval⟩ | ⟨hv, h0, h3⟩ | ⟨hv, h0, h3⟩ | ⟨l2, m2, hv, q, t, h0, h3, hso⟩
  · exact Or.inl ⟨v, by rw [← hc]; exact hv, h0, h3, hval⟩
  · refine Or.inr (Or.inl ⟨by rw [← hc]; exact hv, ?_, ?_⟩)
    · rw [h0, heof]
    · rw [h3, heof8]
  · refine Or.inr (Or.inr (Or.inl ⟨by rw [← hc]; exact hv, ?_, ?_⟩))
    · rw [h0, herr]
    · rw [h3, herr8]
  · have hb := sciParse_syntax_bound _ _ _ _ (hc ▸ hv)
    refine Or.inr (Or.inr (Or.inr ⟨l2, m2, by rw [← hc]; exact hv, q, t, h0, h3, ?_⟩))
    unfold SynObj at hso ⊢
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hso
    have e1 : (BitVec.ofNat 64 (p0.toNat + l2)).toNat = p0.toNat + l2 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have e2 : (BitVec.ofNat 64 (p.toNat + l2)).toNat = p.toNat + l2 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    have e3 : (BitVec.ofNat 64 m2).toNat = m2 := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    refine ⟨a1, a2, fun r hr => a3 r (hL r hr) |> fun x => x, ?_, a5, a6, a7, a8, ?_, ?_, ?_⟩
    · intro r hr
      rcases List.mem_append.1 hr with h | h
      · exact a4 r (List.mem_append_left _ (hL r h))
      · exact a4 r (List.mem_append_right _ h)
    · rw [a9, hsy]
    · rw [a10, hsy8]
    · intro k hk
      rw [e3] at hk
      rw [e2]
      rw [e3] at a11
      have := a11 k hk
      rw [e1] at this
      rw [this, show p0.toNat + l2 + k = p0.toNat + (l2 + k) by omega, hbytes (l2 + k) (by omega),
        show p.toNat + (l2 + k) = p.toNat + l2 + k by omega]

/-- `InitDone`, `TlsG` and `Outside` of the TLS slot survive stores inside the window -/
theorem tls_frame {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi hi3 : Nat}
    {dst p n : BitVec 64} {s S : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n s) (hF1 : MemFrame s.mem S.mem [(lo, hi)])
    (hfs : S.fsBase = s.fsBase) (h14 : S.regs 14 = s.regs 14) (hh3 : hi3 ≤ hi)
    (htls : TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) :
    TlsG S ∧ Outside (S.fsBase.toNat - 8) 8 [(lo, hi3)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone C R2 S.mem := by
  obtain ⟨hT, ho, hi0⟩ := htls
  have ho' := ho
  simp only [outside_cons, outside_nil, and_true] at ho'
  obtain ⟨-, -, -, -, -, -, -, -, hE1, hE2, hB1, hB2, -⟩ := hp
  simp only [outside_cons, outside_nil, and_true] at hE2 hB2
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hfs]; exact hT.base
  · rw [hfs, hF1.accessible]; exact hT.readable
  · rw [hfs, hF1.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; exact ho'), h14]; exact hT.g
  · rw [hfs]; simp only [outside_cons, outside_nil, and_true]; omega
  · obtain ⟨i1, i2, i3, i4, i5⟩ := hi0
    have r1 : ∀ a, (a = C.ioEOF ∨ a = C.ioEOF + 8 ∨ a = C.errBig ∨ a = C.errBig + 8) → S.mem.readLE a 8 = s.mem.readLE a 8 := by
      intro a ha
      refine hF1.readLE a 8 ?_
      simp only [outside_cons, outside_nil, and_true]
      rcases ha with rfl | rfl | rfl | rfl <;> omega
    refine ⟨?_, ?_, ?_, ?_, i5⟩
    · rw [r1 _ (Or.inl rfl)]; exact i1
    · rw [r1 _ (Or.inr (Or.inl rfl))]; exact i2
    · rw [r1 _ (Or.inr (Or.inr (Or.inl rfl)))]; exact i3
    · rw [r1 _ (Or.inr (Or.inr (Or.inr rfl)))]; exact i4

/-- `SciPre` of the string call; `TopPre0` is the one of the entry state viewed with the string in `RBX`/`RCX` -/
theorem sciPre_str {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat} {avx : Nat}
    {dst p n : BitVec 64} {s S : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n (viewS s p n)) (hlo : lo + 4992 ≤ (s.regs 4).toNat)
    (hF1 : MemFrame s.mem S.mem [(lo, hi)]) (hret : S.mem.readLE ((s.regs 4).toNat - 72) 8 < 2 ^ 47)
    (h4 : S.regs 4 = s.regs 4 - 72#64) (h0 : S.regs 0 = dst) (h3 : S.regs 3 = p) (h1 : S.regs 1 = n)
    (h14 : S.regs 14 = s.regs 14) (hx15 : S.xmm 15 = 0) (hdf : S.df = false) (hfs : S.fsBase = s.fsBase)
    (hav : s.mem.accessible avx 1 false = true) (hpg : Fv256.IndexByte.PageReadable s.mem p.toNat n.toNat)
    (htls : TlsG s ∧ Outside (s.fsBase.toNat - 8) 8 [(lo, hi)] ∧ Fv256.Amd64.FromDecimalSpec.InitDone C R2 s.mem) :
    SciPre C avx R R2 T b L lo ((s.regs 4).toNat - 40) dst p n S := by
  have hv4 : (viewS s p n).regs 4 = s.regs 4 := by simp [viewS, setRegF_apply]
  have hv14 : (viewS s p n).regs 14 = s.regs 14 := by simp [viewS, setRegF_apply]
  have hvm : (viewS s p n).mem = s.mem := rfl
  have hsp := (s.regs 4).isLt
  have hhi := hp.hi32
  rw [hv4] at hhi
  have hs4 : (S.regs 4).toNat = (s.regs 4).toNat - 72 := by
    rw [h4, BitVec.toNat_sub]; simp only [BitVec.toNat_ofNat]; omega
  have hlo' : lo + 4992 ≤ ((viewS s p n).regs 4).toNat := by rw [hv4]; exact hlo
  obtain ⟨hr, hT⟩ := pre_str C hp hlo' hF1 (by rw [hv4]; exact hret) (by rw [hv4]; exact h4) h0 h3 h1 (by rw [hv14]; exact h14) hx15 hdf
  rw [hv4] at hT
  have htlsV : TlsG (viewS s p n) ∧ Outside ((viewS s p n).fsBase.toNat - 8) 8 [(lo, hi)] ∧
      Fv256.Amd64.FromDecimalSpec.InitDone C R2 (viewS s p n).mem :=
    ⟨⟨htls.1.base, htls.1.readable, by simpa [viewS, setRegF_apply, regG] using htls.1.g⟩, htls.2.1, htls.2.2⟩
  refine ⟨hr, hT, by omega, by rw [hF1.accessible]; exact hav, ?_, tls_frame C hp hF1 hfs (by rw [hv14]; exact h14) (by omega) htlsV⟩
  unfold Fv256.IndexByte.PageReadable at hpg ⊢
  rw [hF1.accessible]; exact hpg


/-- the result of a string call, as `ScanStrPost`/`MemFrame` of the whole `Scan` call -/
theorem post_str {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {dst p n : BitVec 64} {s S s' : State}
    (hp : TopPre0 C R R2 T b L lo hi dst p n (viewS s p n)) (hF1 : MemFrame s.mem S.mem [(lo, hi)])
    (hpost : ScanStrPost C R b L lo ((s.regs 4).toNat - 40) dst p n S s')
    (hMF : MemFrame S.mem s'.mem (R.rt ++ R2.priv ++ [(lo, (s.regs 4).toNat - 40), (dst.toNat, dst.toNat + 32)])) :
    ScanStrPost C R b L lo hi dst p n s s' ∧ MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := by
  have hp0 := hp
  obtain ⟨-, -, -, -, hEnv, -, -, -, hE1, hE2, hB1, hB2, -, -, -, -, -, -, -, -, hzS, -, ⟨hP48, -⟩, hPW, hPz, -⟩ := hp0
  have hEnv' := hEnv
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, -⟩ := hEnv'
  have hsp := (s.regs 4).isLt
  have hhi := hp.hi32
  have hv4 : (viewS s p n).regs 4 = s.regs 4 := by simp [viewS, setRegF_apply]
  rw [hv4] at hhi
  have hmem : (viewS s p n).mem = s.mem := rfl
  refine ⟨?_, ?_⟩
  · refine strpost_transport C (hpw := by omega) (hp0w := by omega) ?_ (fun r hr => hr) ?_ ?_ ?_ ?_ ?_ ?_ hpost
    · intro k hk
      refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true]
      have h0 : ¬ n.toNat = 0 := by omega
      rcases hPW with h | h | h
      · omega
      · omega
      · omega
    · refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
      omega
    · refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true] at hE2 ⊢
      omega
    · refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true] at hB2 ⊢
      omega
    · refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true] at hB2 ⊢
      omega
    · have hmem : (C.strconvErrSyntax, C.strconvErrSyntax + 16) ∈ staticRanges C T := by simp [staticRanges]
      have hs1 := e14 _ hmem
      refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true] at hs1 ⊢
      omega
    · have hmem : (C.strconvErrSyntax, C.strconvErrSyntax + 16) ∈ staticRanges C T := by simp [staticRanges]
      have hs1 := e14 _ hmem
      refine hF1.readLE _ _ ?_
      simp only [outside_cons, outside_nil, and_true] at hs1 ⊢
      omega
  · have hF' : MemFrame s.mem S.mem (R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) := hF1.mono (fun a k h => by
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      exact h.2.1)
    exact hF'.trans hMF (rs'' := R.rt ++ R2.priv ++ [(lo, hi), (dst.toNat, dst.toNat + 32)]) (fun a k h => by
      refine ⟨h, ?_⟩
      simp only [outside_append, outside_cons, outside_nil, and_true] at h ⊢
      obtain ⟨h1, h2, h3⟩ := h
      exact ⟨h1, by omega, h3⟩)

theorem acc_le48 {m : Janus.Arm64.Memory} {a n : Nat} {w : Bool} (h : m.accessible a n w = true) : a + n ≤ 2 ^ 48 := by
  unfold Janus.Arm64.Memory.accessible at h
  simp only [Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨r, hr, h1⟩, -⟩ := h
  omega

end Fv256.Amd64.ScanBPre
