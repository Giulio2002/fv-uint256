import Fv256.Proofs.Amd64.RecipG.C_43c_502
import Fv256.Proofs.Amd64.RecipG.C_502_7ae
import Fv256.Proofs.Amd64.RecipArith3

open Janus Janus.Amd64

namespace Fv256.Amd64.RecipSeg
open Fv256.RecipMath

theorem sum4a (s : State) (y3 : Nat) (x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 : Nat) (S : State) (h : PC_43c_502 s y3 x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 S)
    (hb2 : x43crdx < 2 ^ 64) (hb0 : x43crbx < 2 ^ 64) (hb1 : x43cr8 < 2 ^ 64) (hy3 : x43crsi < 2 ^ 64) :
    ∃ x502rbx x502rdi x502r8 x502r9 x502r10 x4cam68 x4cam70, L502 s S x43crcx x502rbx x43crsi x502rdi x502r8 x502r9 x502r10 x4cam68 x4cam70 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 ∧ RecRegs s S ∧ RecMem s S.mem y3 ∧
      x502r10 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 1 ∧ x502rdi = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 2 ∧
      x502r8 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 3 ∧ x502rbx = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 4 ∧
      x502r9 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 5 ∧
      x4cam70 + 2 ^ 64 * x4cam68 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 0 * x43crsi := by
  obtain ⟨x4car9, x4car10, x4car11, x4car12, x4car13, x4car15, x4cam68, x4cam70, x4cam108, x4cam120, x4cam128, x502rbx, x502rdi, x502r8, x502r9, x502r10, hLz, h_x4car9, h_x4car10, h_x4car11, h_x4car12, h_x4car13, h_x4car15, h_x4cam68, h_x4cam70, h_x4cam108, h_x4cam120, h_x4cam128, h_x502rbx, h_x502rdi, h_x502r8, h_x502r9, h_x502r10, hRz, hMz⟩ := h
  have key : x502r10 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 1 ∧ x502rdi = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 2 ∧
      x502r8 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 3 ∧ x502rbx = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 4 ∧
      x502r9 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 5 ∧
      x4cam70 + 2 ^ 64 * x4cam68 = sqw (x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx) 0 * x43crsi := by
    subst h_x4car9 h_x4car10 h_x4car11 h_x4car12 h_x4car13 h_x4car15 h_x4cam68 h_x4cam70 h_x4cam108 h_x4cam120 h_x4cam128 h_x502rbx h_x502rdi h_x502r8 h_x502r9 h_x502r10
    unfold sqw
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    janus_carry
  exact ⟨_, _, _, _, _, _, _, hLz, hRz, hMz, key⟩

/-- the seven-word sum the code accumulates in stage 4: all products `w_i y_j` with `i + j ≥ 3` (`p03 = w0 y3`) -/
def stage4V (w1 w2 w3 w4 w5 p03 y0 y1 y2 y3 : Nat) : Nat :=
  (p03 + w1 * y2 + w2 * y1 + w3 * y0) + 2 ^ 64 * (w1 * y3 + w2 * y2 + w3 * y1 + w4 * y0) +
  2 ^ 128 * (w2 * y3 + w3 * y2 + w4 * y1 + w5 * y0) + 2 ^ 192 * (w3 * y3 + w4 * y2 + w5 * y1) +
  2 ^ 256 * (w4 * y3 + w5 * y2) + 2 ^ 320 * (w5 * y3)

end Fv256.Amd64.RecipSeg
