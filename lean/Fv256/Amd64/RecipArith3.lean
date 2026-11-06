import Fv256.Amd64.RecipG.C_1f3_43c
import Fv256.Amd64.RecipArith2
import Fv256.Amd64.RecipArith3s

open Janus Janus.Amd64

namespace Fv256.Amd64.RecipSeg
open Fv256.RecipMath

/-- words of `R2²` -/
def sqw (R : Nat) (i : Nat) : Nat := R * R / 2 ^ (64 * i) % 2 ^ 64

theorem sum3 (s : State) (y3 : Nat) (x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 : Nat)
    (S : State) (h : PC_1f3_43c s y3 x1f3rax x1f3rcx x1f3rsi x1f3rdi x1f3r8 x1f3r9 x1f3r10 x1f3mb0 x1f3m208 x1f3m210 x1f3m218 x1f3m220 S)
    (ha : x1f3rax < 2 ^ 64) (hb : x1f3r10 < 2 ^ 64) (h3 : x1f3rsi < 2 ^ 64) (h2 : x1f3rdi < 2 ^ 64) (h1 : x1f3r8 < 2 ^ 64) (h0 : x1f3r9 < 2 ^ 64) (hmb : x1f3mb0 = x1f3rax) :
    ∃ x43crdx x43crbx x43cr8 x43cm98 x43cma0 x43cma8, L43c s S x1f3rcx x43crdx x43crbx x1f3rsi x43cr8 x43cm98 x43cma0 x43cma8 x1f3m208 x1f3m210 x1f3m218 x1f3m220 ∧ RecRegs s S ∧ RecMem s S.mem y3 ∧
      x43cma0 = x43crbx ∧ x43cm98 = x43cr8 ∧ x43cma8 = x43crdx ∧
      x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx =
        2 * ((((x1f3rax + 2 ^ 64 * x1f3r10) * 2 ^ 192 + 2 ^ 320 - (stage3q (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 0) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 1) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 2) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 3) x1f3r9 x1f3r8 x1f3rdi x1f3rsi)) % 2 ^ 320) / 2 ^ 128) % 2 ^ 192 := by
  unfold PC_1f3_43c at h
  obtain ⟨x273rax, x273rbx, x273r10, x273r11, x273r12, x273r13, x273r15, x273mb8, x273m100, x30dr12, x30dm68, x30dm70, x30dme8, x30dmf0, x30dmf8, x30dm1c0, x30dm1c8, x30dm1d0, x30dm1d8, x30dm1e0, x30dm1e8, x30dm1f0, x30dm1f8, x30dm200, x3bbrax, x3bbrdx, x3bbrbx, x3bbrdi, x3bbr10, x3bbr11, x3bbr12, x3bbme0, x3f0rax, x3f0rdx, x3f0rdi, x3f0r13, x3f0r15, x43crdx, x43crbx, x43cr8, x43cm98, x43cma0, x43cma8, hLz, h_x273rax, h_x273rbx, h_x273r10, h_x273r11, h_x273r12, h_x273r13, h_x273r15, h_x273mb8, h_x273m100, h_x30dr12, h_x30dm68, h_x30dm70, h_x30dme8, h_x30dmf0, h_x30dmf8, h_x30dm1c0, h_x30dm1c8, h_x30dm1d0, h_x30dm1d8, h_x30dm1e0, h_x30dm1e8, h_x30dm1f0, h_x30dm1f8, h_x30dm200, h_x3bbrax, h_x3bbrdx, h_x3bbrbx, h_x3bbrdi, h_x3bbr10, h_x3bbr11, h_x3bbr12, h_x3bbme0, h_x3f0rax, h_x3f0rdx, h_x3f0rdi, h_x3f0r13, h_x3f0r15, h_x43crdx, h_x43crbx, h_x43cr8, h_x43cm98, h_x43cma0, h_x43cma8, hRz, hMz⟩ := h
  have hV : x3f0r13 + 2 ^ 64 * x3f0r15 + 2 ^ 128 * x3f0rax + 2 ^ 192 * x3f0rdx + 2 ^ 256 * x3f0rdi =
      stage3q (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 0) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 1) (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 2)
          (sqw (x1f3rax + 2 ^ 64 * x1f3r10) 3) x1f3r9 x1f3r8 x1f3rdi x1f3rsi := by
    subst h_x273rax h_x273rbx h_x273r10 h_x273r11 h_x273r12 h_x273r13 h_x273r15 h_x273mb8 h_x273m100 h_x30dr12 h_x30dm68 h_x30dm70 h_x30dme8 h_x30dmf0 h_x30dmf8 h_x30dm1c0 h_x30dm1c8 h_x30dm1d0 h_x30dm1d8 h_x30dm1e0 h_x30dm1e8 h_x30dm1f0 h_x30dm1f8 h_x30dm200 h_x3bbrax h_x3bbrdx h_x3bbrbx h_x3bbrdi h_x3bbr10 h_x3bbr11 h_x3bbr12 h_x3bbme0 h_x3f0rax h_x3f0rdx h_x3f0rdi h_x3f0r13 h_x3f0r15
    unfold sqw stage3q
    simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
    janus_carry
  have hl : ∀ a e : Nat, a = e % 18446744073709551616 → a < 2 ^ 64 := fun a e h => by rw [h]; exact Nat.mod_lt _ (by decide)
  have b13 : x3f0r13 < 2 ^ 64 := hl _ _ h_x3f0r13
  have b15 : x3f0r15 < 2 ^ 64 := hl _ _ h_x3f0r15
  have bax : x3f0rax < 2 ^ 64 := hl _ _ h_x3f0rax
  have bdx : x3f0rdx < 2 ^ 64 := hl _ _ h_x3f0rdx
  have bdi : x3f0rdi < 2 ^ 64 := hl _ _ h_x3f0rdi
  have bmb8 : x273mb8 < 2 ^ 64 := by rw [h_x273mb8]; exact Nat.mod_lt _ (by decide)
  have bmb0 : x1f3mb0 < 2 ^ 64 := by rw [hmb]; exact ha
  have hB : x43crbx + 2 ^ 64 * x43cr8 + 2 ^ 128 * x43crdx =
      2 * (((x1f3mb0 + 2 ^ 64 * x273mb8) * 2 ^ 192 + 2 ^ 320 - (x3f0r13 + 2 ^ 64 * x3f0r15 + 2 ^ 128 * x3f0rax + 2 ^ 192 * x3f0rdx + 2 ^ 256 * x3f0rdi)) % 2 ^ 320 / 2 ^ 128) % 2 ^ 192 := by
    exact sbb3 x3f0rax x3f0rdx x3f0rdi x3f0r13 x3f0r15 x1f3mb0 x273mb8 x43crdx x43crbx x43cr8 bax bdx bdi b13 b15 bmb0 bmb8 h_x43crdx h_x43crbx h_x43cr8
  rw [hV, hmb, h_x273mb8, Nat.mod_eq_of_lt hb] at hB
  refine ⟨_, _, _, _, _, _, hLz, hRz, hMz, ?_, ?_, ?_, hB⟩
  · rw [h_x43cma0, h_x43crbx]
  · rw [h_x43cm98, h_x43cr8]
  · rw [h_x43cma8, h_x43crdx]

end Fv256.Amd64.RecipSeg
