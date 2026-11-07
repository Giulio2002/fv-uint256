import Fv256.FormatFastDefs

open Janus Janus.Amd64 Janus.Contracts.ICall

namespace Fv256.FormatFast

theorem out_fl {rt : List (Nat × Nat)} {r stack a n : Nat} (ho : Outside a n rt)
    (hd : a + n ≤ r - 8 - stack ∨ r + 0x78 ≤ a) (h8 : 8 + stack ≤ r) : Outside a n (FL rt r stack) := by
  simp only [FL, outside_append, outside_cons, outside_nil]
  refine ⟨ho, ?_, ?_, trivial⟩ <;> omega

/-- the itab words and `*z` as seen at any later state of the fast path -/
theorem finv_tab {rt : List (Nat × Nat)} {stack : Nat} {z tab data : BitVec 64} {fW fP fF fWr ch : Nat} {S0 S : State}
    (hp : FPre rt stack z tab data fW fP fF fWr S0) (hi : FInv rt stack z tab data ch S0 S) :
    S.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ S.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
    S.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ S.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
    S.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
    S.mem.readLE z.toNat 32 = S0.mem.readLE z.toNat 32 ∧ S.mem.accessible z.toNat 32 false = true ∧
    S.mem.accessible ((S0.regs 4).toNat - 8 - stack) (stack + 0x80) true = true := by
  obtain ⟨-, -, -, -, hal, hwb, hwn, hwa, hout, -, -, -, -, -, -, htb, hta, hF, hP, hW, hWr, hto, htd, hzb, hza, hzo, hzd⟩ := hp
  obtain ⟨-, -, -, -, -, -, hfr, -⟩ := hi
  have ot : ∀ a n, tab.toNat + 0x18 ≤ a → a + n ≤ tab.toNat + 0x38 → Outside a n (FL rt (S0.regs 4).toNat stack) :=
    fun a n h1 h2 => out_fl (hto.of_sub h1 h2) (by omega) hwb
  have oz : Outside z.toNat 32 (FL rt (S0.regs 4).toNat stack) := out_fl hzo (by omega) hwb
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hF
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hP
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hW
  · rw [hfr.readLE _ _ (ot _ _ (by omega) (by omega))]; exact hWr
  · rw [hfr.accessible]; exact hta
  · exact hfr.readLE _ _ oz
  · rw [hfr.accessible]; exact hza
  · rw [hfr.accessible]; exact hwa

end Fv256.FormatFast
