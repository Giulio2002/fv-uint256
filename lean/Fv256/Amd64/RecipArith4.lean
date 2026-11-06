import Fv256.Amd64.RecipG.C_43c_502
import Fv256.Amd64.RecipG.C_502_7ae
import Fv256.Amd64.RecipArith3

open Janus Janus.Amd64

namespace Fv256.Amd64.RecipSeg
open Fv256.RecipMath

theorem sum4a (s : State) (y3 : Nat) (x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 : Nat) (S : State) (h : PC_43c_502 s y3 x43crcx x43crdx x43crbx x43crsi x43cr8 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 S)
    (hb2 : x43crdx < 2 ^ 64) (hb0 : x43crbx < 2 ^ 64) (hb1 : x43cr8 < 2 ^ 64) (hy3 : x43crsi < 2 ^ 64) :
    ∃ x502rbx x502rdi x502r8 x502r9 x502r10 x4cam68 x4cam70, L502 s S x43crcx x502rbx x43crsi x502rdi x502r8 x502r9 x502r10 x4cam68 x4cam70 x43cm98 x43cma0 x43cma8 x43cm208 x43cm210 x43cm218 x43cm220 ∧
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
  exact ⟨_, _, _, _, _, _, _, hLz, key⟩

/-- the seven-word sum the code accumulates in stage 4: all products `w_i y_j` with `i + j ≥ 3` (`p03 = w0 y3`) -/
def stage4V (w1 w2 w3 w4 w5 p03 y0 y1 y2 y3 : Nat) : Nat :=
  (p03 + w1 * y2 + w2 * y1 + w3 * y0) + 2 ^ 64 * (w1 * y3 + w2 * y2 + w3 * y1 + w4 * y0) +
  2 ^ 128 * (w2 * y3 + w3 * y2 + w4 * y1 + w5 * y0) + 2 ^ 192 * (w3 * y3 + w4 * y2 + w5 * y1) +
  2 ^ 256 * (w4 * y3 + w5 * y2) + 2 ^ 320 * (w5 * y3)

theorem sum4b (s : State) (y3 : Nat) (x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220 : Nat) (S : State) (h : PC_502_7ae s y3 x502rcx x502rbx x502rsi x502rdi x502r8 x502r9 x502r10 x502m68 x502m70 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220 S)
    (b1 : x502r10 < 2 ^ 64) (b2 : x502rdi < 2 ^ 64) (b3 : x502r8 < 2 ^ 64) (b4 : x502rbx < 2 ^ 64) (b5 : x502r9 < 2 ^ 64)
    (bp0 : x502m70 < 2 ^ 64) (bp1 : x502m68 < 2 ^ 64) (b0 : x502m208 < 2 ^ 64) (b1' : x502m210 < 2 ^ 64) (b2' : x502m218 < 2 ^ 64)
    (b3' : x502m220 < 2 ^ 64) (hs : x502rsi = x502m220) :
    ∃ x7aerax x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11,
      L7ae s S x7aerax x502rcx x7aerdx x7aerbx x7aersi x7aerdi x7aer8 x7aer11 x502m98 x502ma0 x502ma8 x502m208 x502m210 x502m218 x502m220 ∧
      x7aerdx + 2 ^ 64 * x7aer11 + 2 ^ 128 * x7aerbx + 2 ^ 192 * x7aer8 + 2 ^ 256 * x7aerax + 2 ^ 320 * x7aersi + 2 ^ 384 * x7aerdi =
        stage4V x502r10 x502rdi x502r8 x502rbx x502r9 (x502m70 + 2 ^ 64 * x502m68) x502m208 x502m210 x502m218 x502m220 := by
    obtain ⟨x549rax, x549r13, x549r15, x549m48, x549m50, x549m58, x549m1f8, x549m200, x5e2r13, x5e2m38, x5e2m40, x5e2m198, x5e2m1a0, x5e2m1a8, x5e2m1b0, x5e2m1b8, x5e2m1c0, x5e2m1c8, x5e2m1d0, x5e2m1d8, x5e2m1e0, x5e2m1e8, x5e2m1f0, x689rax, x689rdx, x689rsi, x689rdi, x689r8, x689r9, x689r10, x689r13, x689m150, x689m158, x689m160, x689m168, x689m170, x689m178, x689m180, x689m188, x689m190, x6b3rdx, x6b3rbx, x6b3rsi, x6b3r13, x6e3rdx, x6e3rbx, x6e3rsi, x6e3r12, x6e3r15, x723rdx, x723rbx, x723rsi, x723r12, x723r13, x723r15, x74brdx, x74br10, x74br11, x74br12, x74br15, x776rbx, x776rsi, x776rdi, x776r8, x776r9, x776r10, x7aerax, x7aerdx, x7aerbx, x7aersi, x7aerdi, x7aer8, x7aer11, hLz, h_x549rax, h_x549r13, h_x549r15, h_x549m48, h_x549m50, h_x549m58, h_x549m1f8, h_x549m200, h_x5e2r13, h_x5e2m38, h_x5e2m40, h_x5e2m198, h_x5e2m1a0, h_x5e2m1a8, h_x5e2m1b0, h_x5e2m1b8, h_x5e2m1c0, h_x5e2m1c8, h_x5e2m1d0, h_x5e2m1d8, h_x5e2m1e0, h_x5e2m1e8, h_x5e2m1f0, h_x689rax, h_x689rdx, h_x689rsi, h_x689rdi, h_x689r8, h_x689r9, h_x689r10, h_x689r13, h_x689m150, h_x689m158, h_x689m160, h_x689m168, h_x689m170, h_x689m178, h_x689m180, h_x689m188, h_x689m190, h_x6b3rdx, h_x6b3rbx, h_x6b3rsi, h_x6b3r13, h_x6e3rdx, h_x6e3rbx, h_x6e3rsi, h_x6e3r12, h_x6e3r15, h_x723rdx, h_x723rbx, h_x723rsi, h_x723r12, h_x723r13, h_x723r15, h_x74brdx, h_x74br10, h_x74br11, h_x74br12, h_x74br15, h_x776rbx, h_x776rsi, h_x776rdi, h_x776r8, h_x776r9, h_x776r10, h_x7aerax, h_x7aerdx, h_x7aerbx, h_x7aersi, h_x7aerdi, h_x7aer8, h_x7aer11, hRz, hMz⟩ := h
  have key : x7aerdx + 2 ^ 64 * x7aer11 + 2 ^ 128 * x7aerbx + 2 ^ 192 * x7aer8 + 2 ^ 256 * x7aerax + 2 ^ 320 * x7aersi + 2 ^ 384 * x7aerdi =
        stage4V x502r10 x502rdi x502r8 x502rbx x502r9 (x502m70 + 2 ^ 64 * x502m68) x502m208 x502m210 x502m218 x502m220 := by
    subst h_x549rax h_x549r13 h_x549r15 h_x549m48 h_x549m50 h_x549m58 h_x549m1f8 h_x549m200 h_x5e2r13 h_x5e2m38 h_x5e2m40 h_x5e2m198 h_x5e2m1a0 h_x5e2m1a8 h_x5e2m1b0 h_x5e2m1b8 h_x5e2m1c0 h_x5e2m1c8 h_x5e2m1d0 h_x5e2m1d8 h_x5e2m1e0 h_x5e2m1e8 h_x5e2m1f0 h_x689rax h_x689rdx h_x689rsi h_x689rdi h_x689r8 h_x689r9 h_x689r10 h_x689r13 h_x689m150 h_x689m158 h_x689m160 h_x689m168 h_x689m170 h_x689m178 h_x689m180 h_x689m188 h_x689m190 h_x6b3rdx h_x6b3rbx h_x6b3rsi h_x6b3r13 h_x6e3rdx h_x6e3rbx h_x6e3rsi h_x6e3r12 h_x6e3r15 h_x723rdx h_x723rbx h_x723rsi h_x723r12 h_x723r13 h_x723r15 h_x74brdx h_x74br10 h_x74br11 h_x74br12 h_x74br15 h_x776rbx h_x776rsi h_x776rdi h_x776r8 h_x776r9 h_x776r10 h_x7aerax h_x7aerdx h_x7aerbx h_x7aersi h_x7aerdi h_x7aer8 h_x7aer11
    unfold stage4V
    janus_carry
  exact ⟨_, _, _, _, _, _, _, hLz, key⟩

end Fv256.Amd64.RecipSeg
