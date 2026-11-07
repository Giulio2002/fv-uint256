import Fv256.Arm64.UnmarshalPost
import Fv256.Arm64.UnmarshalSpecJ

/-!
# Postcondition of `UnmarshalJSON` (arm64), Extracted-free

`UnmarshalJSON(input)`: if `input` is a quoted string (`n ≥ 2`, first and last byte `"`) the result is that of
`UnmarshalText(input[1:n-1])` (hex if the inner string starts with `0x`/`0X`, decimal otherwise); otherwise `SetFromDecimal(string(input))`.
-/

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Spec.Type Janus.Contracts Fv256.I Fv256.C
open Fv256.Arm64.SfdTopSpec Fv256.Arm64.FromHexLib Fv256.Arm64.UnmarshalPost Fv256.Arm64.UnmarshalSpecJ

namespace Fv256.Arm64.UnmarshalJPost

def JPost (C : SfdCfg) (R : RtInv) (R2 : IfaceModel) (lo hi : Nat) (z : BitVec 64) (p n : Nat) (s s' : State) : Prop :=
  (Quoted s.mem p n →
    (IsHex s.mem (p + 1) (n - 2) → HexPart z s.mem (p + 1) (n - 2) s') ∧
    (¬ IsHex s.mem (p + 1) (n - 2) → DecPart C z s.mem (p + 1) (n - 2) s')) ∧
  (¬ Quoted s.mem p n → DecPart C z s.mem p n s') ∧
  MemFrame s.mem s'.mem (R.rt ++ R2.priv ++ [(lo, hi), (z.toNat, z.toNat + 32)])

theorem bytes_frame {m m' : Janus.Arm64.Memory} {lo hi p n : Nat} (hF : MemFrame m m' [(lo, hi)]) (hin : p + n ≤ lo ∨ hi ≤ p) :
    ∀ k, k < n → m'.readLE (p + k) 1 = m.readLE (p + k) 1 := by
  intro k hk
  exact hF.readLE (p + k) 1 (by simp only [outside_cons, outside_nil, and_true]; omega)

theorem decPart_frame {C : SfdCfg} {z : BitVec 64} {m m' : Janus.Arm64.Memory} {p n lo hi : Nat} {s' : State}
    (hF : MemFrame m m' [(lo, hi)]) (hin : p + n ≤ lo ∨ hi ≤ p) (hz : z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat)
    (hio : C.ioEOF + 16 ≤ lo ∨ hi ≤ C.ioEOF) (hbig : C.errBig + 16 ≤ lo ∨ hi ≤ C.errBig)
    (h : DecPart C z m' p n s') : DecPart C z m p n s' := by
  have hb := bytes_frame hF hin
  have hdp : decParse (bytesAt m' p) n = decParse (bytesAt m p) n := Fv256.I.decParse_congr _ _ _ (fun k hk => hb k hk)
  have r1 : m'.readLE C.ioEOF 8 = m.readLE C.ioEOF 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have r2 : m'.readLE (C.ioEOF + 8) 8 = m.readLE (C.ioEOF + 8) 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have r3 : m'.readLE C.errBig 8 = m.readLE C.errBig 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have r4 : m'.readLE (C.errBig + 8) 8 = m.readLE (C.errBig + 8) 8 := hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)
  have r5 : Janus.Spec.val256 m' z.toNat = Janus.Spec.val256 m z.toNat := by
    unfold Janus.Spec.val256
    rw [hF.readLE z.toNat 32 (by simp only [outside_cons, outside_nil, and_true]; omega)]
  unfold DecPart at h ⊢
  rw [hdp, r1, r2, r3, r4, r5] at h
  exact h

theorem hexPart_frame {z : BitVec 64} {m m' : Janus.Arm64.Memory} {p n lo hi : Nat} {s' : State}
    (hF : MemFrame m m' [(lo, hi)]) (hin : p + n ≤ lo ∨ hi ≤ p) (hev : 1792784 + 96 ≤ lo ∨ hi ≤ 1792784)
    (h : HexPart z m' p n s') : HexPart z m p n s' := by
  have hb := bytes_frame hF hin
  have hdp : parseHex (bytesAt m' p) n = parseHex (bytesAt m p) n := parseHex_congr _ _ _ (fun k hk => hb k hk)
  have hr : ∀ e, m'.readLE (errAddrOf e) 8 = m.readLE (errAddrOf e) 8 ∧
      m'.readLE (errAddrOf e + 8) 8 = m.readLE (errAddrOf e + 8) 8 := by
    intro e
    have := errAddrOf_bounds e
    exact ⟨hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega),
      hF.readLE _ _ (by simp only [outside_cons, outside_nil, and_true]; omega)⟩
  unfold HexPart at h ⊢
  rw [hdp] at h
  refine ⟨h.1, fun e he => ?_⟩
  obtain ⟨c0, c1⟩ := h.2 e he
  rw [(hr e).1] at c0
  rw [(hr e).2] at c1
  exact ⟨c0, c1⟩

end Fv256.Arm64.UnmarshalJPost
