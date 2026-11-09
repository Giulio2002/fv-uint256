import Fv256.Proofs.Amd64.R4Seg0

set_option exponentiation.threshold 400
namespace Fv256.Amd64.R4Seg

theorem mulb (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : a * b < 2 ^ 128 := by
  have := Nat.mul_lt_mul'' ha hb
  rwa [← Nat.pow_add] at this

theorem prodS2_u0 (x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128 x33erax x33erbx x33ersi x33er9 x33er11 x33er12 x33er13 x33er15 x33em20 x33em28 : Nat)
    (b_x2f8rax : x2f8rax < 2 ^ 64)
    (b_x2f8rcx : x2f8rcx < 2 ^ 64)
    (b_x2f8rdx : x2f8rdx < 2 ^ 64)
    (b_x2f8rdi : x2f8rdi < 2 ^ 64)
    (b_x2f8r8 : x2f8r8 < 2 ^ 64)
    (b_x2f8r10 : x2f8r10 < 2 ^ 64)
    (b_x2f8m0 : x2f8m0 < 2 ^ 64)
    (b_x2f8m8 : x2f8m8 < 2 ^ 64)
    (b_x2f8m10 : x2f8m10 < 2 ^ 64)
    (b_x2f8m18 : x2f8m18 < 2 ^ 64)
    (b_x2f8m60 : x2f8m60 < 2 ^ 64)
    (b_x2f8m68 : x2f8m68 < 2 ^ 64)
    (b_x2f8m70 : x2f8m70 < 2 ^ 64)
    (b_x2f8m88 : x2f8m88 < 2 ^ 64)
    (b_x2f8m128 : x2f8m128 < 2 ^ 64)
    (h_x33erax : x33erax = (x2f8m70 * x2f8rdx) % 18446744073709551616)
    (h_x33erbx : x33erbx = x2f8rax % 18446744073709551616)
    (h_x33ersi : x33ersi = x2f8rdx % 18446744073709551616)
    (h_x33er9 : x33er9 = (x2f8rdi * x2f8rax) % 18446744073709551616)
    (h_x33er11 : x33er11 = (x2f8rdi * x2f8rax / 18446744073709551616 + x2f8rdi * x2f8rdx) % 18446744073709551616)
    (h_x33er12 : x33er12 = x2f8m70 % 18446744073709551616)
    (h_x33er13 : x33er13 = (x2f8m70 * x2f8rax) % 18446744073709551616)
    (h_x33er15 : x33er15 = (x2f8m70 * x2f8rax / 18446744073709551616) % 18446744073709551616)
    (h_x33em20 : x33em20 = (x2f8m70 * x2f8rdx / 18446744073709551616) % 18446744073709551616)
    (h_x33em28 : x33em28 = (x2f8m70 * x2f8rcx) % 18446744073709551616)
    : (2 ^ 192 * (x2f8m60 * x2f8r10) + 2 ^ 256 * (x2f8m60 * x2f8r8) + 2 ^ 128 * (x2f8m60 * x2f8rcx) + 2 ^ 0 * (x2f8m60 * x33erbx) + 2 ^ 64 * (x2f8m60 * x33ersi) + 2 ^ 256 * (x2f8m68 * x2f8r10) + 2 ^ 192 * (x2f8m68 * x2f8rcx) + 2 ^ 64 * (x2f8m68 * x33erbx) + 2 ^ 128 * (x2f8m68 * x33ersi) + 2 ^ 128 * (x2f8m70 * x2f8rax) + 2 ^ 256 * (x2f8m70 * x2f8rcx) + 2 ^ 192 * (x2f8m70 * x2f8rdx) + 2 ^ 192 * (x2f8rdi * x2f8rax) + 2 ^ 256 * (x2f8rdi * x2f8rdx)) % 2 ^ 320 = (2 ^ 192 * x33erax + 2 ^ 192 * x33er9 + 2 ^ 256 * x33er11 + 2 ^ 128 * x33er13 + 2 ^ 192 * x33er15 + 2 ^ 256 * x33em20 + 2 ^ 256 * x33em28 + 2 ^ 192 * (x2f8m60 * x2f8r10) + 2 ^ 256 * (x2f8m60 * x2f8r8) + 2 ^ 128 * (x2f8m60 * x2f8rcx) + 2 ^ 0 * (x2f8m60 * x33erbx) + 2 ^ 64 * (x2f8m60 * x33ersi) + 2 ^ 256 * (x2f8m68 * x2f8r10) + 2 ^ 192 * (x2f8m68 * x2f8rcx) + 2 ^ 64 * (x2f8m68 * x33erbx) + 2 ^ 128 * (x2f8m68 * x33ersi)) % 2 ^ 320 := by
  have := mulb x2f8m60 x2f8r10 b_x2f8m60 b_x2f8r10
  have := Nat.mul_comm x2f8m60 x2f8r10
  have := mulb x2f8m60 x2f8r8 b_x2f8m60 b_x2f8r8
  have := Nat.mul_comm x2f8m60 x2f8r8
  have := mulb x2f8m60 x2f8rcx b_x2f8m60 b_x2f8rcx
  have := Nat.mul_comm x2f8m60 x2f8rcx
  have := Nat.mul_comm x2f8m60 x33erbx
  have := Nat.mul_comm x2f8m60 x33ersi
  have := mulb x2f8m68 x2f8r10 b_x2f8m68 b_x2f8r10
  have := Nat.mul_comm x2f8m68 x2f8r10
  have := mulb x2f8m68 x2f8rcx b_x2f8m68 b_x2f8rcx
  have := Nat.mul_comm x2f8m68 x2f8rcx
  have := Nat.mul_comm x2f8m68 x33erbx
  have := Nat.mul_comm x2f8m68 x33ersi
  have := mulb x2f8m70 x2f8rax b_x2f8m70 b_x2f8rax
  have := Nat.mul_comm x2f8m70 x2f8rax
  have := mulb x2f8m70 x2f8rcx b_x2f8m70 b_x2f8rcx
  have := Nat.mul_comm x2f8m70 x2f8rcx
  have := mulb x2f8m70 x2f8rdx b_x2f8m70 b_x2f8rdx
  have := Nat.mul_comm x2f8m70 x2f8rdx
  have := mulb x2f8rdi x2f8rax b_x2f8rdi b_x2f8rax
  have := Nat.mul_comm x2f8rdi x2f8rax
  have := mulb x2f8rdi x2f8rdx b_x2f8rdi b_x2f8rdx
  have := Nat.mul_comm x2f8rdi x2f8rdx
  have e_x33erbx : x2f8rax = x33erbx := by rw [h_x33erbx]; exact (Nat.mod_eq_of_lt b_x2f8rax).symm
  subst e_x33erbx
  have e_x33ersi : x2f8rdx = x33ersi := by rw [h_x33ersi]; exact (Nat.mod_eq_of_lt b_x2f8rdx).symm
  subst e_x33ersi
  have e_x33er12 : x2f8m70 = x33er12 := by rw [h_x33er12]; exact (Nat.mod_eq_of_lt b_x2f8m70).symm
  subst e_x33er12
  omega

theorem prodS2_u1 (x33erax x2f8rcx x33erbx x33ersi x2f8rdi x2f8r8 x33er9 x2f8r10 x33er11 x33er12 x33er13 x33er15 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x33em20 x33em28 x2f8m60 x2f8m68 x2f8m88 x2f8m128 x38bm30 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 : Nat)
    (b_x33erax : x33erax < 2 ^ 64)
    (b_x2f8rcx : x2f8rcx < 2 ^ 64)
    (b_x33erbx : x33erbx < 2 ^ 64)
    (b_x33ersi : x33ersi < 2 ^ 64)
    (b_x2f8rdi : x2f8rdi < 2 ^ 64)
    (b_x2f8r8 : x2f8r8 < 2 ^ 64)
    (b_x33er9 : x33er9 < 2 ^ 64)
    (b_x2f8r10 : x2f8r10 < 2 ^ 64)
    (b_x33er11 : x33er11 < 2 ^ 64)
    (b_x33er12 : x33er12 < 2 ^ 64)
    (b_x33er13 : x33er13 < 2 ^ 64)
    (b_x33er15 : x33er15 < 2 ^ 64)
    (b_x2f8m0 : x2f8m0 < 2 ^ 64)
    (b_x2f8m8 : x2f8m8 < 2 ^ 64)
    (b_x2f8m10 : x2f8m10 < 2 ^ 64)
    (b_x2f8m18 : x2f8m18 < 2 ^ 64)
    (b_x33em20 : x33em20 < 2 ^ 64)
    (b_x33em28 : x33em28 < 2 ^ 64)
    (b_x2f8m60 : x2f8m60 < 2 ^ 64)
    (b_x2f8m68 : x2f8m68 < 2 ^ 64)
    (b_x2f8m88 : x2f8m88 < 2 ^ 64)
    (b_x2f8m128 : x2f8m128 < 2 ^ 64)
    (h_x38bm30 : x38bm30 = (x2f8m68 * x33erbx) % 18446744073709551616)
    (h_x38bme8 : x38bme8 = (x2f8m68 * x33ersi) % 18446744073709551616)
    (h_x38bmf0 : x38bmf0 = (x2f8m68 * x33ersi / 18446744073709551616) % 18446744073709551616)
    (h_x38bmf8 : x38bmf8 = (x2f8m68 * x2f8rcx) % 18446744073709551616)
    (h_x38bm100 : x38bm100 = (x2f8m68 * x2f8rcx / 18446744073709551616) % 18446744073709551616)
    (h_x38bm108 : x38bm108 = (x2f8m68 * x33erbx / 18446744073709551616) % 18446744073709551616)
    (h_x38bm110 : x38bm110 = x33erax % 18446744073709551616)
    : (2 ^ 192 * x33erax + 2 ^ 192 * x33er9 + 2 ^ 256 * x33er11 + 2 ^ 128 * x33er13 + 2 ^ 192 * x33er15 + 2 ^ 256 * x33em20 + 2 ^ 256 * x33em28 + 2 ^ 192 * (x2f8m60 * x2f8r10) + 2 ^ 256 * (x2f8m60 * x2f8r8) + 2 ^ 128 * (x2f8m60 * x2f8rcx) + 2 ^ 0 * (x2f8m60 * x33erbx) + 2 ^ 64 * (x2f8m60 * x33ersi) + 2 ^ 256 * (x2f8m68 * x2f8r10) + 2 ^ 192 * (x2f8m68 * x2f8rcx) + 2 ^ 64 * (x2f8m68 * x33erbx) + 2 ^ 128 * (x2f8m68 * x33ersi)) % 2 ^ 320 = (2 ^ 192 * x33er9 + 2 ^ 256 * x33er11 + 2 ^ 128 * x33er13 + 2 ^ 192 * x33er15 + 2 ^ 256 * x33em20 + 2 ^ 256 * x33em28 + 2 ^ 64 * x38bm30 + 2 ^ 128 * x38bme8 + 2 ^ 192 * x38bmf0 + 2 ^ 192 * x38bmf8 + 2 ^ 256 * x38bm100 + 2 ^ 128 * x38bm108 + 2 ^ 192 * x38bm110 + 2 ^ 192 * (x2f8m60 * x2f8r10) + 2 ^ 256 * (x2f8m60 * x2f8r8) + 2 ^ 128 * (x2f8m60 * x2f8rcx) + 2 ^ 0 * (x2f8m60 * x33erbx) + 2 ^ 64 * (x2f8m60 * x33ersi) + 2 ^ 256 * (x2f8m68 * x2f8r10)) % 2 ^ 320 := by
  have := mulb x2f8m60 x2f8r10 b_x2f8m60 b_x2f8r10
  have := Nat.mul_comm x2f8m60 x2f8r10
  have := mulb x2f8m60 x2f8r8 b_x2f8m60 b_x2f8r8
  have := Nat.mul_comm x2f8m60 x2f8r8
  have := mulb x2f8m60 x2f8rcx b_x2f8m60 b_x2f8rcx
  have := Nat.mul_comm x2f8m60 x2f8rcx
  have := mulb x2f8m60 x33erbx b_x2f8m60 b_x33erbx
  have := Nat.mul_comm x2f8m60 x33erbx
  have := mulb x2f8m60 x33ersi b_x2f8m60 b_x33ersi
  have := Nat.mul_comm x2f8m60 x33ersi
  have := mulb x2f8m68 x2f8r10 b_x2f8m68 b_x2f8r10
  have := Nat.mul_comm x2f8m68 x2f8r10
  have := mulb x2f8m68 x2f8rcx b_x2f8m68 b_x2f8rcx
  have := Nat.mul_comm x2f8m68 x2f8rcx
  have := mulb x2f8m68 x33erbx b_x2f8m68 b_x33erbx
  have := Nat.mul_comm x2f8m68 x33erbx
  have := mulb x2f8m68 x33ersi b_x2f8m68 b_x33ersi
  have := Nat.mul_comm x2f8m68 x33ersi
  have e_x38bm110 : x33erax = x38bm110 := by rw [h_x38bm110]; exact (Nat.mod_eq_of_lt b_x33erax).symm
  subst e_x38bm110
  omega

theorem prodS2_u2 (x2f8rcx x33erbx x33ersi x2f8rdi x2f8r8 x33er9 x2f8r10 x33er11 x33er12 x33er13 x33er15 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x33em20 x33em28 x38bm30 x2f8m60 x2f8m68 x2f8m88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x2f8m128 x3earax x3earcx x3eardx x3earbx x3earsi x3ear8 x3eamc8 x3eamd0 x3eamd8 x3eame0 : Nat)
    (b_x2f8rcx : x2f8rcx < 2 ^ 64)
    (b_x33erbx : x33erbx < 2 ^ 64)
    (b_x33ersi : x33ersi < 2 ^ 64)
    (b_x2f8rdi : x2f8rdi < 2 ^ 64)
    (b_x2f8r8 : x2f8r8 < 2 ^ 64)
    (b_x33er9 : x33er9 < 2 ^ 64)
    (b_x2f8r10 : x2f8r10 < 2 ^ 64)
    (b_x33er11 : x33er11 < 2 ^ 64)
    (b_x33er12 : x33er12 < 2 ^ 64)
    (b_x33er13 : x33er13 < 2 ^ 64)
    (b_x33er15 : x33er15 < 2 ^ 64)
    (b_x2f8m0 : x2f8m0 < 2 ^ 64)
    (b_x2f8m8 : x2f8m8 < 2 ^ 64)
    (b_x2f8m10 : x2f8m10 < 2 ^ 64)
    (b_x2f8m18 : x2f8m18 < 2 ^ 64)
    (b_x33em20 : x33em20 < 2 ^ 64)
    (b_x33em28 : x33em28 < 2 ^ 64)
    (b_x38bm30 : x38bm30 < 2 ^ 64)
    (b_x2f8m60 : x2f8m60 < 2 ^ 64)
    (b_x2f8m68 : x2f8m68 < 2 ^ 64)
    (b_x2f8m88 : x2f8m88 < 2 ^ 64)
    (b_x38bme8 : x38bme8 < 2 ^ 64)
    (b_x38bmf0 : x38bmf0 < 2 ^ 64)
    (b_x38bmf8 : x38bmf8 < 2 ^ 64)
    (b_x38bm100 : x38bm100 < 2 ^ 64)
    (b_x38bm108 : x38bm108 < 2 ^ 64)
    (b_x38bm110 : x38bm110 < 2 ^ 64)
    (b_x2f8m128 : x2f8m128 < 2 ^ 64)
    (h_x3earax : x3earax = (x2f8m60 * x2f8r10) % 18446744073709551616)
    (h_x3earcx : x3earcx = (x2f8m60 * x2f8rcx) % 18446744073709551616)
    (h_x3eardx : x3eardx = (x2f8m60 * x2f8r10 / 18446744073709551616) % 18446744073709551616)
    (h_x3earbx : x3earbx = (x2f8m60 * x33erbx) % 18446744073709551616)
    (h_x3earsi : x3earsi = (x2f8m60 * x33ersi) % 18446744073709551616)
    (h_x3ear8 : x3ear8 = (x2f8m60 * x2f8r8) % 18446744073709551616)
    (h_x3eamc8 : x3eamc8 = (x2f8m60 * x33ersi / 18446744073709551616) % 18446744073709551616)
    (h_x3eamd0 : x3eamd0 = (x2f8m60 * x2f8rcx / 18446744073709551616) % 18446744073709551616)
    (h_x3eamd8 : x3eamd8 = (x2f8m60 * x33erbx / 18446744073709551616) % 18446744073709551616)
    (h_x3eame0 : x3eame0 = (x2f8m68 * x2f8r10) % 18446744073709551616)
    : (2 ^ 192 * x33er9 + 2 ^ 256 * x33er11 + 2 ^ 128 * x33er13 + 2 ^ 192 * x33er15 + 2 ^ 256 * x33em20 + 2 ^ 256 * x33em28 + 2 ^ 64 * x38bm30 + 2 ^ 128 * x38bme8 + 2 ^ 192 * x38bmf0 + 2 ^ 192 * x38bmf8 + 2 ^ 256 * x38bm100 + 2 ^ 128 * x38bm108 + 2 ^ 192 * x38bm110 + 2 ^ 192 * (x2f8m60 * x2f8r10) + 2 ^ 256 * (x2f8m60 * x2f8r8) + 2 ^ 128 * (x2f8m60 * x2f8rcx) + 2 ^ 0 * (x2f8m60 * x33erbx) + 2 ^ 64 * (x2f8m60 * x33ersi) + 2 ^ 256 * (x2f8m68 * x2f8r10)) % 2 ^ 320 = (2 ^ 192 * x3earax + 2 ^ 128 * x3earcx + 2 ^ 256 * x3eardx + x3earbx + 2 ^ 64 * x3earsi + 2 ^ 256 * x3ear8 + 2 ^ 192 * x33er9 + 2 ^ 256 * x33er11 + 2 ^ 128 * x33er13 + 2 ^ 192 * x33er15 + 2 ^ 256 * x33em20 + 2 ^ 256 * x33em28 + 2 ^ 64 * x38bm30 + 2 ^ 128 * x3eamc8 + 2 ^ 192 * x3eamd0 + 2 ^ 64 * x3eamd8 + 2 ^ 256 * x3eame0 + 2 ^ 128 * x38bme8 + 2 ^ 192 * x38bmf0 + 2 ^ 192 * x38bmf8 + 2 ^ 256 * x38bm100 + 2 ^ 128 * x38bm108 + 2 ^ 192 * x38bm110) % 2 ^ 320 := by
  have := mulb x2f8m60 x2f8r10 b_x2f8m60 b_x2f8r10
  have := Nat.mul_comm x2f8m60 x2f8r10
  have := mulb x2f8m60 x2f8r8 b_x2f8m60 b_x2f8r8
  have := Nat.mul_comm x2f8m60 x2f8r8
  have := mulb x2f8m60 x2f8rcx b_x2f8m60 b_x2f8rcx
  have := Nat.mul_comm x2f8m60 x2f8rcx
  have := mulb x2f8m60 x33erbx b_x2f8m60 b_x33erbx
  have := Nat.mul_comm x2f8m60 x33erbx
  have := mulb x2f8m60 x33ersi b_x2f8m60 b_x33ersi
  have := Nat.mul_comm x2f8m60 x33ersi
  have := mulb x2f8m68 x2f8r10 b_x2f8m68 b_x2f8r10
  have := Nat.mul_comm x2f8m68 x2f8r10
  omega

theorem adcB_u0 (x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x3ear9 x3ear11 x3ear12 x3ear13 x3ear15 x3eam0 x3eam8 x3eam10 x3eam18 x3eam20 x3eam28 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eamf8 x3eam100 x3eam108 x3eam110 x3eam128 x429r10 x429r11 x429r13 : Nat)
    (b_x3earax : x3earax < 2 ^ 64)
    (b_x3earcx : x3earcx < 2 ^ 64)
    (b_x3eardx : x3eardx < 2 ^ 64)
    (b_x3earbx : x3earbx < 2 ^ 64)
    (b_x3earsi : x3earsi < 2 ^ 64)
    (b_x3eardi : x3eardi < 2 ^ 64)
    (b_x3ear8 : x3ear8 < 2 ^ 64)
    (b_x3ear9 : x3ear9 < 2 ^ 64)
    (b_x3ear11 : x3ear11 < 2 ^ 64)
    (b_x3ear12 : x3ear12 < 2 ^ 64)
    (b_x3ear13 : x3ear13 < 2 ^ 64)
    (b_x3ear15 : x3ear15 < 2 ^ 64)
    (b_x3eam0 : x3eam0 < 2 ^ 64)
    (b_x3eam8 : x3eam8 < 2 ^ 64)
    (b_x3eam10 : x3eam10 < 2 ^ 64)
    (b_x3eam18 : x3eam18 < 2 ^ 64)
    (b_x3eam20 : x3eam20 < 2 ^ 64)
    (b_x3eam28 : x3eam28 < 2 ^ 64)
    (b_x3eam30 : x3eam30 < 2 ^ 64)
    (b_x3eam60 : x3eam60 < 2 ^ 64)
    (b_x3eam68 : x3eam68 < 2 ^ 64)
    (b_x3eam88 : x3eam88 < 2 ^ 64)
    (b_x3eamc8 : x3eamc8 < 2 ^ 64)
    (b_x3eamd0 : x3eamd0 < 2 ^ 64)
    (b_x3eamd8 : x3eamd8 < 2 ^ 64)
    (b_x3eame0 : x3eame0 < 2 ^ 64)
    (b_x3eame8 : x3eame8 < 2 ^ 64)
    (b_x3eamf0 : x3eamf0 < 2 ^ 64)
    (b_x3eamf8 : x3eamf8 < 2 ^ 64)
    (b_x3eam100 : x3eam100 < 2 ^ 64)
    (b_x3eam108 : x3eam108 < 2 ^ 64)
    (b_x3eam110 : x3eam110 < 2 ^ 64)
    (b_x3eam128 : x3eam128 < 2 ^ 64)
    (h_x429r10 : x429r10 = (x3eam108 + x3ear13) % 18446744073709551616)
    (h_x429r11 : x429r11 = (((x3ear11 + x3eam28 + (x3ear15 + x3ear9) / 18446744073709551616) % 18446744073709551616 + x3eam20 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x3eam100 + (x3eamf8 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) % 18446744073709551616 + (x3eam108 + x3ear13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x429r13 : x429r13 = (x3eamf8 + (x3eam110 + (x3ear15 + x3ear9) % 18446744073709551616) % 18446744073709551616 + (x3eam108 + x3ear13) / 18446744073709551616) % 18446744073709551616)
    : (2 ^ 192 * x3earax + 2 ^ 128 * x3earcx + 2 ^ 256 * x3eardx + x3earbx + 2 ^ 64 * x3earsi + 2 ^ 256 * x3ear8 + 2 ^ 192 * x3ear9 + 2 ^ 256 * x3ear11 + 2 ^ 128 * x3ear13 + 2 ^ 192 * x3ear15 + 2 ^ 256 * x3eam20 + 2 ^ 256 * x3eam28 + 2 ^ 64 * x3eam30 + 2 ^ 128 * x3eamc8 + 2 ^ 192 * x3eamd0 + 2 ^ 64 * x3eamd8 + 2 ^ 256 * x3eame0 + 2 ^ 128 * x3eame8 + 2 ^ 192 * x3eamf0 + 2 ^ 192 * x3eamf8 + 2 ^ 256 * x3eam100 + 2 ^ 128 * x3eam108 + 2 ^ 192 * x3eam110) % 2 ^ 320 = (2 ^ 192 * x3earax + 2 ^ 128 * x3earcx + 2 ^ 256 * x3eardx + x3earbx + 2 ^ 64 * x3earsi + 2 ^ 256 * x3ear8 + 2 ^ 128 * x429r10 + 2 ^ 256 * x429r11 + 2 ^ 192 * x429r13 + 2 ^ 64 * x3eam30 + 2 ^ 128 * x3eamc8 + 2 ^ 192 * x3eamd0 + 2 ^ 64 * x3eamd8 + 2 ^ 256 * x3eame0 + 2 ^ 128 * x3eame8 + 2 ^ 192 * x3eamf0) % 2 ^ 320 := by
  omega

theorem adcB_u1 (x3earax x3earcx x3eardx x3earbx x3earsi x3eardi x3ear8 x429r10 x429r11 x3ear12 x429r13 x3eam0 x3eam8 x3eam10 x3eam18 x3eam30 x3eam60 x3eam68 x3eam88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x3eame8 x3eamf0 x3eam128 x46brcx x46br9 x46br11 x46br13 : Nat)
    (b_x3earax : x3earax < 2 ^ 64)
    (b_x3earcx : x3earcx < 2 ^ 64)
    (b_x3eardx : x3eardx < 2 ^ 64)
    (b_x3earbx : x3earbx < 2 ^ 64)
    (b_x3earsi : x3earsi < 2 ^ 64)
    (b_x3eardi : x3eardi < 2 ^ 64)
    (b_x3ear8 : x3ear8 < 2 ^ 64)
    (b_x429r10 : x429r10 < 2 ^ 64)
    (b_x429r11 : x429r11 < 2 ^ 64)
    (b_x3ear12 : x3ear12 < 2 ^ 64)
    (b_x429r13 : x429r13 < 2 ^ 64)
    (b_x3eam0 : x3eam0 < 2 ^ 64)
    (b_x3eam8 : x3eam8 < 2 ^ 64)
    (b_x3eam10 : x3eam10 < 2 ^ 64)
    (b_x3eam18 : x3eam18 < 2 ^ 64)
    (b_x3eam30 : x3eam30 < 2 ^ 64)
    (b_x3eam60 : x3eam60 < 2 ^ 64)
    (b_x3eam68 : x3eam68 < 2 ^ 64)
    (b_x3eam88 : x3eam88 < 2 ^ 64)
    (b_x3eamc8 : x3eamc8 < 2 ^ 64)
    (b_x3eamd0 : x3eamd0 < 2 ^ 64)
    (b_x3eamd8 : x3eamd8 < 2 ^ 64)
    (b_x3eame0 : x3eame0 < 2 ^ 64)
    (b_x3eame8 : x3eame8 < 2 ^ 64)
    (b_x3eamf0 : x3eamf0 < 2 ^ 64)
    (b_x3eam128 : x3eam128 < 2 ^ 64)
    (h_x46brcx : x46brcx = (x3earcx + (x3eame8 + x429r10) % 18446744073709551616 + (x3eamd8 + x3eam30) / 18446744073709551616) % 18446744073709551616)
    (h_x46br9 : x46br9 = (x3eamd0 + (x3eamf0 + x429r13 + (x3eame8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x3earcx + (x3eame8 + x429r10) % 18446744073709551616 + (x3eamd8 + x3eam30) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x46br11 : x46br11 = ((x429r11 + x3eame0 + (x3eamf0 + x429r13 + (x3eame8 + x429r10) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x3ear8 + (x3eamd0 + (x3eamf0 + x429r13 + (x3eame8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x3earcx + (x3eame8 + x429r10) % 18446744073709551616 + (x3eamd8 + x3eam30) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x46br13 : x46br13 = (x3eamd8 + x3eam30) % 18446744073709551616)
    : (2 ^ 192 * x3earax + 2 ^ 128 * x3earcx + 2 ^ 256 * x3eardx + x3earbx + 2 ^ 64 * x3earsi + 2 ^ 256 * x3ear8 + 2 ^ 128 * x429r10 + 2 ^ 256 * x429r11 + 2 ^ 192 * x429r13 + 2 ^ 64 * x3eam30 + 2 ^ 128 * x3eamc8 + 2 ^ 192 * x3eamd0 + 2 ^ 64 * x3eamd8 + 2 ^ 256 * x3eame0 + 2 ^ 128 * x3eame8 + 2 ^ 192 * x3eamf0) % 2 ^ 320 = (2 ^ 192 * x3earax + 2 ^ 128 * x46brcx + 2 ^ 256 * x3eardx + x3earbx + 2 ^ 64 * x3earsi + 2 ^ 192 * x46br9 + 2 ^ 256 * x46br11 + 2 ^ 64 * x46br13 + 2 ^ 128 * x3eamc8) % 2 ^ 320 := by
  omega

theorem adcB_u2 (x3earax x46brcx x3eardx x3earbx x3earsi x3eardi x46br9 x46br11 x3ear12 x46br13 x3eam0 x3eam8 x3eam10 x3eam18 x3eam60 x3eam68 x3eam88 x3eamc8 x3eam128 x47frax x47frsi x47fr8 x47fr11 : Nat)
    (b_x3earax : x3earax < 2 ^ 64)
    (b_x46brcx : x46brcx < 2 ^ 64)
    (b_x3eardx : x3eardx < 2 ^ 64)
    (b_x3earbx : x3earbx < 2 ^ 64)
    (b_x3earsi : x3earsi < 2 ^ 64)
    (b_x3eardi : x3eardi < 2 ^ 64)
    (b_x46br9 : x46br9 < 2 ^ 64)
    (b_x46br11 : x46br11 < 2 ^ 64)
    (b_x3ear12 : x3ear12 < 2 ^ 64)
    (b_x46br13 : x46br13 < 2 ^ 64)
    (b_x3eam0 : x3eam0 < 2 ^ 64)
    (b_x3eam8 : x3eam8 < 2 ^ 64)
    (b_x3eam10 : x3eam10 < 2 ^ 64)
    (b_x3eam18 : x3eam18 < 2 ^ 64)
    (b_x3eam60 : x3eam60 < 2 ^ 64)
    (b_x3eam68 : x3eam68 < 2 ^ 64)
    (b_x3eam88 : x3eam88 < 2 ^ 64)
    (b_x3eamc8 : x3eamc8 < 2 ^ 64)
    (b_x3eam128 : x3eam128 < 2 ^ 64)
    (h_x47frax : x47frax = (x3earax + x46br9 + (x3eamc8 + x46brcx + (x3earsi + x46br13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x47frsi : x47frsi = (x3earsi + x46br13) % 18446744073709551616)
    (h_x47fr8 : x47fr8 = (x3eamc8 + x46brcx + (x3earsi + x46br13) / 18446744073709551616) % 18446744073709551616)
    (h_x47fr11 : x47fr11 = (x46br11 + x3eardx + (x3earax + x46br9 + (x3eamc8 + x46brcx + (x3earsi + x46br13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    : (2 ^ 192 * x3earax + 2 ^ 128 * x46brcx + 2 ^ 256 * x3eardx + x3earbx + 2 ^ 64 * x3earsi + 2 ^ 192 * x46br9 + 2 ^ 256 * x46br11 + 2 ^ 64 * x46br13 + 2 ^ 128 * x3eamc8) % 2 ^ 320 = (2 ^ 192 * x47frax + x3earbx + 2 ^ 64 * x47frsi + 2 ^ 128 * x47fr8 + 2 ^ 256 * x47fr11) % 2 ^ 320 := by
  omega

theorem s2_arith (x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128 x33erax x33erbx x33ersi x33er9 x33er11 x33er12 x33er13 x33er15 x33em20 x33em28 x38bm30 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x3earax x3earcx x3eardx x3earbx x3earsi x3ear8 x3eamc8 x3eamd0 x3eamd8 x3eame0 x429r10 x429r11 x429r13 x46brcx x46br9 x46br11 x46br13 x47frax x47frsi x47fr8 x47fr11 : Nat)
    (b_x2f8rax : x2f8rax < 2 ^ 64)
    (b_x2f8rcx : x2f8rcx < 2 ^ 64)
    (b_x2f8rdx : x2f8rdx < 2 ^ 64)
    (b_x2f8rdi : x2f8rdi < 2 ^ 64)
    (b_x2f8r8 : x2f8r8 < 2 ^ 64)
    (b_x2f8r10 : x2f8r10 < 2 ^ 64)
    (b_x2f8m0 : x2f8m0 < 2 ^ 64)
    (b_x2f8m8 : x2f8m8 < 2 ^ 64)
    (b_x2f8m10 : x2f8m10 < 2 ^ 64)
    (b_x2f8m18 : x2f8m18 < 2 ^ 64)
    (b_x2f8m60 : x2f8m60 < 2 ^ 64)
    (b_x2f8m68 : x2f8m68 < 2 ^ 64)
    (b_x2f8m70 : x2f8m70 < 2 ^ 64)
    (b_x2f8m88 : x2f8m88 < 2 ^ 64)
    (b_x2f8m128 : x2f8m128 < 2 ^ 64)
    (h_x33erax : x33erax = (x2f8m70 * x2f8rdx) % 18446744073709551616)
    (h_x33erbx : x33erbx = x2f8rax % 18446744073709551616)
    (h_x33ersi : x33ersi = x2f8rdx % 18446744073709551616)
    (h_x33er9 : x33er9 = (x2f8rdi * x2f8rax) % 18446744073709551616)
    (h_x33er11 : x33er11 = (x2f8rdi * x2f8rax / 18446744073709551616 + x2f8rdi * x2f8rdx) % 18446744073709551616)
    (h_x33er12 : x33er12 = x2f8m70 % 18446744073709551616)
    (h_x33er13 : x33er13 = (x2f8m70 * x2f8rax) % 18446744073709551616)
    (h_x33er15 : x33er15 = (x2f8m70 * x2f8rax / 18446744073709551616) % 18446744073709551616)
    (h_x33em20 : x33em20 = (x2f8m70 * x2f8rdx / 18446744073709551616) % 18446744073709551616)
    (h_x33em28 : x33em28 = (x2f8m70 * x2f8rcx) % 18446744073709551616)
    (h_x38bm30 : x38bm30 = (x2f8m68 * x33erbx) % 18446744073709551616)
    (h_x38bme8 : x38bme8 = (x2f8m68 * x33ersi) % 18446744073709551616)
    (h_x38bmf0 : x38bmf0 = (x2f8m68 * x33ersi / 18446744073709551616) % 18446744073709551616)
    (h_x38bmf8 : x38bmf8 = (x2f8m68 * x2f8rcx) % 18446744073709551616)
    (h_x38bm100 : x38bm100 = (x2f8m68 * x2f8rcx / 18446744073709551616) % 18446744073709551616)
    (h_x38bm108 : x38bm108 = (x2f8m68 * x33erbx / 18446744073709551616) % 18446744073709551616)
    (h_x38bm110 : x38bm110 = x33erax % 18446744073709551616)
    (h_x3earax : x3earax = (x2f8m60 * x2f8r10) % 18446744073709551616)
    (h_x3earcx : x3earcx = (x2f8m60 * x2f8rcx) % 18446744073709551616)
    (h_x3eardx : x3eardx = (x2f8m60 * x2f8r10 / 18446744073709551616) % 18446744073709551616)
    (h_x3earbx : x3earbx = (x2f8m60 * x33erbx) % 18446744073709551616)
    (h_x3earsi : x3earsi = (x2f8m60 * x33ersi) % 18446744073709551616)
    (h_x3ear8 : x3ear8 = (x2f8m60 * x2f8r8) % 18446744073709551616)
    (h_x3eamc8 : x3eamc8 = (x2f8m60 * x33ersi / 18446744073709551616) % 18446744073709551616)
    (h_x3eamd0 : x3eamd0 = (x2f8m60 * x2f8rcx / 18446744073709551616) % 18446744073709551616)
    (h_x3eamd8 : x3eamd8 = (x2f8m60 * x33erbx / 18446744073709551616) % 18446744073709551616)
    (h_x3eame0 : x3eame0 = (x2f8m68 * x2f8r10) % 18446744073709551616)
    (h_x429r10 : x429r10 = (x38bm108 + x33er13) % 18446744073709551616)
    (h_x429r11 : x429r11 = (((x33er11 + x33em28 + (x33er15 + x33er9) / 18446744073709551616) % 18446744073709551616 + x33em20 + (x38bm110 + (x33er15 + x33er9) % 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x38bm100 + (x38bmf8 + (x38bm110 + (x33er15 + x33er9) % 18446744073709551616) % 18446744073709551616 + (x38bm108 + x33er13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x429r13 : x429r13 = (x38bmf8 + (x38bm110 + (x33er15 + x33er9) % 18446744073709551616) % 18446744073709551616 + (x38bm108 + x33er13) / 18446744073709551616) % 18446744073709551616)
    (h_x46brcx : x46brcx = (x3earcx + (x38bme8 + x429r10) % 18446744073709551616 + (x3eamd8 + x38bm30) / 18446744073709551616) % 18446744073709551616)
    (h_x46br9 : x46br9 = (x3eamd0 + (x38bmf0 + x429r13 + (x38bme8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x3earcx + (x38bme8 + x429r10) % 18446744073709551616 + (x3eamd8 + x38bm30) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x46br11 : x46br11 = ((x429r11 + x3eame0 + (x38bmf0 + x429r13 + (x38bme8 + x429r10) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616 + x3ear8 + (x3eamd0 + (x38bmf0 + x429r13 + (x38bme8 + x429r10) / 18446744073709551616) % 18446744073709551616 + (x3earcx + (x38bme8 + x429r10) % 18446744073709551616 + (x3eamd8 + x38bm30) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x46br13 : x46br13 = (x3eamd8 + x38bm30) % 18446744073709551616)
    (h_x47frax : x47frax = (x3earax + x46br9 + (x3eamc8 + x46brcx + (x3earsi + x46br13) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    (h_x47frsi : x47frsi = (x3earsi + x46br13) % 18446744073709551616)
    (h_x47fr8 : x47fr8 = (x3eamc8 + x46brcx + (x3earsi + x46br13) / 18446744073709551616) % 18446744073709551616)
    (h_x47fr11 : x47fr11 = (x46br11 + x3eardx + (x3earax + x46br9 + (x3eamc8 + x46brcx + (x3earsi + x46br13) / 18446744073709551616) / 18446744073709551616) / 18446744073709551616) % 18446744073709551616)
    : x3earbx + 2 ^ 64 * x47frsi + 2 ^ 128 * x47fr8 + 2 ^ 192 * x47frax + 2 ^ 256 * x47fr11 = ((x2f8rax + 2 ^ 64 * x2f8rdx + 2 ^ 128 * x2f8rcx + 2 ^ 192 * x2f8r10 + 2 ^ 256 * x2f8r8) * (x2f8m60 + 2 ^ 64 * x2f8m68 + 2 ^ 128 * x2f8m70 + 2 ^ 192 * x2f8rdi)) % 2 ^ 320 := by
  have b_x33erax : x33erax < 2 ^ 64 := by
    first | (rw [h_x33erax]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33erax]; exact BitVec.isLt _)
  have b_x33erbx : x33erbx < 2 ^ 64 := by
    first | (rw [h_x33erbx]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33erbx]; exact BitVec.isLt _)
  have b_x33ersi : x33ersi < 2 ^ 64 := by
    first | (rw [h_x33ersi]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33ersi]; exact BitVec.isLt _)
  have b_x33er9 : x33er9 < 2 ^ 64 := by
    first | (rw [h_x33er9]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33er9]; exact BitVec.isLt _)
  have b_x33er11 : x33er11 < 2 ^ 64 := by
    first | (rw [h_x33er11]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33er11]; exact BitVec.isLt _)
  have b_x33er12 : x33er12 < 2 ^ 64 := by
    first | (rw [h_x33er12]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33er12]; exact BitVec.isLt _)
  have b_x33er13 : x33er13 < 2 ^ 64 := by
    first | (rw [h_x33er13]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33er13]; exact BitVec.isLt _)
  have b_x33er15 : x33er15 < 2 ^ 64 := by
    first | (rw [h_x33er15]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33er15]; exact BitVec.isLt _)
  have b_x33em20 : x33em20 < 2 ^ 64 := by
    first | (rw [h_x33em20]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33em20]; exact BitVec.isLt _)
  have b_x33em28 : x33em28 < 2 ^ 64 := by
    first | (rw [h_x33em28]; exact Nat.mod_lt _ (by decide)) | (rw [h_x33em28]; exact BitVec.isLt _)
  have b_x38bm30 : x38bm30 < 2 ^ 64 := by
    first | (rw [h_x38bm30]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bm30]; exact BitVec.isLt _)
  have b_x38bme8 : x38bme8 < 2 ^ 64 := by
    first | (rw [h_x38bme8]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bme8]; exact BitVec.isLt _)
  have b_x38bmf0 : x38bmf0 < 2 ^ 64 := by
    first | (rw [h_x38bmf0]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bmf0]; exact BitVec.isLt _)
  have b_x38bmf8 : x38bmf8 < 2 ^ 64 := by
    first | (rw [h_x38bmf8]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bmf8]; exact BitVec.isLt _)
  have b_x38bm100 : x38bm100 < 2 ^ 64 := by
    first | (rw [h_x38bm100]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bm100]; exact BitVec.isLt _)
  have b_x38bm108 : x38bm108 < 2 ^ 64 := by
    first | (rw [h_x38bm108]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bm108]; exact BitVec.isLt _)
  have b_x38bm110 : x38bm110 < 2 ^ 64 := by
    first | (rw [h_x38bm110]; exact Nat.mod_lt _ (by decide)) | (rw [h_x38bm110]; exact BitVec.isLt _)
  have b_x3earax : x3earax < 2 ^ 64 := by
    first | (rw [h_x3earax]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3earax]; exact BitVec.isLt _)
  have b_x3earcx : x3earcx < 2 ^ 64 := by
    first | (rw [h_x3earcx]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3earcx]; exact BitVec.isLt _)
  have b_x3eardx : x3eardx < 2 ^ 64 := by
    first | (rw [h_x3eardx]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3eardx]; exact BitVec.isLt _)
  have b_x3earbx : x3earbx < 2 ^ 64 := by
    first | (rw [h_x3earbx]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3earbx]; exact BitVec.isLt _)
  have b_x3earsi : x3earsi < 2 ^ 64 := by
    first | (rw [h_x3earsi]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3earsi]; exact BitVec.isLt _)
  have b_x3ear8 : x3ear8 < 2 ^ 64 := by
    first | (rw [h_x3ear8]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3ear8]; exact BitVec.isLt _)
  have b_x3eamc8 : x3eamc8 < 2 ^ 64 := by
    first | (rw [h_x3eamc8]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3eamc8]; exact BitVec.isLt _)
  have b_x3eamd0 : x3eamd0 < 2 ^ 64 := by
    first | (rw [h_x3eamd0]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3eamd0]; exact BitVec.isLt _)
  have b_x3eamd8 : x3eamd8 < 2 ^ 64 := by
    first | (rw [h_x3eamd8]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3eamd8]; exact BitVec.isLt _)
  have b_x3eame0 : x3eame0 < 2 ^ 64 := by
    first | (rw [h_x3eame0]; exact Nat.mod_lt _ (by decide)) | (rw [h_x3eame0]; exact BitVec.isLt _)
  have b_x429r10 : x429r10 < 2 ^ 64 := by
    first | (rw [h_x429r10]; exact Nat.mod_lt _ (by decide)) | (rw [h_x429r10]; exact BitVec.isLt _)
  have b_x429r11 : x429r11 < 2 ^ 64 := by
    first | (rw [h_x429r11]; exact Nat.mod_lt _ (by decide)) | (rw [h_x429r11]; exact BitVec.isLt _)
  have b_x429r13 : x429r13 < 2 ^ 64 := by
    first | (rw [h_x429r13]; exact Nat.mod_lt _ (by decide)) | (rw [h_x429r13]; exact BitVec.isLt _)
  have b_x46brcx : x46brcx < 2 ^ 64 := by
    first | (rw [h_x46brcx]; exact Nat.mod_lt _ (by decide)) | (rw [h_x46brcx]; exact BitVec.isLt _)
  have b_x46br9 : x46br9 < 2 ^ 64 := by
    first | (rw [h_x46br9]; exact Nat.mod_lt _ (by decide)) | (rw [h_x46br9]; exact BitVec.isLt _)
  have b_x46br11 : x46br11 < 2 ^ 64 := by
    first | (rw [h_x46br11]; exact Nat.mod_lt _ (by decide)) | (rw [h_x46br11]; exact BitVec.isLt _)
  have b_x46br13 : x46br13 < 2 ^ 64 := by
    first | (rw [h_x46br13]; exact Nat.mod_lt _ (by decide)) | (rw [h_x46br13]; exact BitVec.isLt _)
  have b_x47frax : x47frax < 2 ^ 64 := by
    first | (rw [h_x47frax]; exact Nat.mod_lt _ (by decide)) | (rw [h_x47frax]; exact BitVec.isLt _)
  have b_x47frsi : x47frsi < 2 ^ 64 := by
    first | (rw [h_x47frsi]; exact Nat.mod_lt _ (by decide)) | (rw [h_x47frsi]; exact BitVec.isLt _)
  have b_x47fr8 : x47fr8 < 2 ^ 64 := by
    first | (rw [h_x47fr8]; exact Nat.mod_lt _ (by decide)) | (rw [h_x47fr8]; exact BitVec.isLt _)
  have b_x47fr11 : x47fr11 < 2 ^ 64 := by
    first | (rw [h_x47fr11]; exact Nat.mod_lt _ (by decide)) | (rw [h_x47fr11]; exact BitVec.isLt _)
  have p0 := prodS2_u0 x2f8rax x2f8rcx x2f8rdx x2f8rdi x2f8r8 x2f8r10 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m70 x2f8m88 x2f8m128 x33erax x33erbx x33ersi x33er9 x33er11 x33er12 x33er13 x33er15 x33em20 x33em28 b_x2f8rax b_x2f8rcx b_x2f8rdx b_x2f8rdi b_x2f8r8 b_x2f8r10 b_x2f8m0 b_x2f8m8 b_x2f8m10 b_x2f8m18 b_x2f8m60 b_x2f8m68 b_x2f8m70 b_x2f8m88 b_x2f8m128 h_x33erax h_x33erbx h_x33ersi h_x33er9 h_x33er11 h_x33er12 h_x33er13 h_x33er15 h_x33em20 h_x33em28
  have p1 := prodS2_u1 x33erax x2f8rcx x33erbx x33ersi x2f8rdi x2f8r8 x33er9 x2f8r10 x33er11 x33er12 x33er13 x33er15 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x33em20 x33em28 x2f8m60 x2f8m68 x2f8m88 x2f8m128 x38bm30 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 b_x33erax b_x2f8rcx b_x33erbx b_x33ersi b_x2f8rdi b_x2f8r8 b_x33er9 b_x2f8r10 b_x33er11 b_x33er12 b_x33er13 b_x33er15 b_x2f8m0 b_x2f8m8 b_x2f8m10 b_x2f8m18 b_x33em20 b_x33em28 b_x2f8m60 b_x2f8m68 b_x2f8m88 b_x2f8m128 h_x38bm30 h_x38bme8 h_x38bmf0 h_x38bmf8 h_x38bm100 h_x38bm108 h_x38bm110
  have p2 := prodS2_u2 x2f8rcx x33erbx x33ersi x2f8rdi x2f8r8 x33er9 x2f8r10 x33er11 x33er12 x33er13 x33er15 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x33em20 x33em28 x38bm30 x2f8m60 x2f8m68 x2f8m88 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x2f8m128 x3earax x3earcx x3eardx x3earbx x3earsi x3ear8 x3eamc8 x3eamd0 x3eamd8 x3eame0 b_x2f8rcx b_x33erbx b_x33ersi b_x2f8rdi b_x2f8r8 b_x33er9 b_x2f8r10 b_x33er11 b_x33er12 b_x33er13 b_x33er15 b_x2f8m0 b_x2f8m8 b_x2f8m10 b_x2f8m18 b_x33em20 b_x33em28 b_x38bm30 b_x2f8m60 b_x2f8m68 b_x2f8m88 b_x38bme8 b_x38bmf0 b_x38bmf8 b_x38bm100 b_x38bm108 b_x38bm110 b_x2f8m128 h_x3earax h_x3earcx h_x3eardx h_x3earbx h_x3earsi h_x3ear8 h_x3eamc8 h_x3eamd0 h_x3eamd8 h_x3eame0
  have a0 := adcB_u0 x3earax x3earcx x3eardx x3earbx x3earsi x2f8rdi x3ear8 x33er9 x33er11 x33er12 x33er13 x33er15 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x33em20 x33em28 x38bm30 x2f8m60 x2f8m68 x2f8m88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x2f8m128 x429r10 x429r11 x429r13 b_x3earax b_x3earcx b_x3eardx b_x3earbx b_x3earsi b_x2f8rdi b_x3ear8 b_x33er9 b_x33er11 b_x33er12 b_x33er13 b_x33er15 b_x2f8m0 b_x2f8m8 b_x2f8m10 b_x2f8m18 b_x33em20 b_x33em28 b_x38bm30 b_x2f8m60 b_x2f8m68 b_x2f8m88 b_x3eamc8 b_x3eamd0 b_x3eamd8 b_x3eame0 b_x38bme8 b_x38bmf0 b_x38bmf8 b_x38bm100 b_x38bm108 b_x38bm110 b_x2f8m128 h_x429r10 h_x429r11 h_x429r13
  have a1 := adcB_u1 x3earax x3earcx x3eardx x3earbx x3earsi x2f8rdi x3ear8 x429r10 x429r11 x33er12 x429r13 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x38bm30 x2f8m60 x2f8m68 x2f8m88 x3eamc8 x3eamd0 x3eamd8 x3eame0 x38bme8 x38bmf0 x2f8m128 x46brcx x46br9 x46br11 x46br13 b_x3earax b_x3earcx b_x3eardx b_x3earbx b_x3earsi b_x2f8rdi b_x3ear8 b_x429r10 b_x429r11 b_x33er12 b_x429r13 b_x2f8m0 b_x2f8m8 b_x2f8m10 b_x2f8m18 b_x38bm30 b_x2f8m60 b_x2f8m68 b_x2f8m88 b_x3eamc8 b_x3eamd0 b_x3eamd8 b_x3eame0 b_x38bme8 b_x38bmf0 b_x2f8m128 h_x46brcx h_x46br9 h_x46br11 h_x46br13
  have a2 := adcB_u2 x3earax x46brcx x3eardx x3earbx x3earsi x2f8rdi x46br9 x46br11 x33er12 x46br13 x2f8m0 x2f8m8 x2f8m10 x2f8m18 x2f8m60 x2f8m68 x2f8m88 x3eamc8 x2f8m128 x47frax x47frsi x47fr8 x47fr11 b_x3earax b_x46brcx b_x3eardx b_x3earbx b_x3earsi b_x2f8rdi b_x46br9 b_x46br11 b_x33er12 b_x46br13 b_x2f8m0 b_x2f8m8 b_x2f8m10 b_x2f8m18 b_x2f8m60 b_x2f8m68 b_x2f8m88 b_x3eamc8 b_x2f8m128 h_x47frax h_x47frsi h_x47fr8 h_x47fr11
  have e_x33erbx : x2f8rax = x33erbx := by rw [h_x33erbx]; exact (Nat.mod_eq_of_lt b_x2f8rax).symm
  subst e_x33erbx
  have e_x33ersi : x2f8rdx = x33ersi := by rw [h_x33ersi]; exact (Nat.mod_eq_of_lt b_x2f8rdx).symm
  subst e_x33ersi
  have e_x33er12 : x2f8m70 = x33er12 := by rw [h_x33er12]; exact (Nat.mod_eq_of_lt b_x2f8m70).symm
  subst e_x33er12
  have e_x38bm110 : x33erax = x38bm110 := by rw [h_x38bm110]; exact (Nat.mod_eq_of_lt b_x33erax).symm
  subst e_x38bm110
  have hfull : (x2f8rax + 2 ^ 64 * x2f8rdx + 2 ^ 128 * x2f8rcx + 2 ^ 192 * x2f8r10 + 2 ^ 256 * x2f8r8) * (x2f8m60 + 2 ^ 64 * x2f8m68 + 2 ^ 128 * x2f8m70 + 2 ^ 192 * x2f8rdi) = 2 ^ 0 * (x2f8m60 * x2f8rax) + 2 ^ 64 * (x2f8m68 * x2f8rax) + 2 ^ 128 * (x2f8m70 * x2f8rax) + 2 ^ 192 * (x2f8rdi * x2f8rax) + 2 ^ 64 * (x2f8m60 * x2f8rdx) + 2 ^ 128 * (x2f8m68 * x2f8rdx) + 2 ^ 192 * (x2f8m70 * x2f8rdx) + 2 ^ 256 * (x2f8rdi * x2f8rdx) + 2 ^ 128 * (x2f8m60 * x2f8rcx) + 2 ^ 192 * (x2f8m68 * x2f8rcx) + 2 ^ 256 * (x2f8m70 * x2f8rcx) + 2 ^ 320 * (x2f8rdi * x2f8rcx) + 2 ^ 192 * (x2f8m60 * x2f8r10) + 2 ^ 256 * (x2f8m68 * x2f8r10) + 2 ^ 320 * (x2f8m70 * x2f8r10) + 2 ^ 384 * (x2f8rdi * x2f8r10) + 2 ^ 256 * (x2f8m60 * x2f8r8) + 2 ^ 320 * (x2f8m68 * x2f8r8) + 2 ^ 384 * (x2f8m70 * x2f8r8) + 2 ^ 448 * (x2f8rdi * x2f8r8) := by janus_ring
  have mb00 := mulb x2f8m60 x2f8rax b_x2f8m60 b_x2f8rax
  have mb01 := mulb x2f8m68 x2f8rax b_x2f8m68 b_x2f8rax
  have mb02 := mulb x2f8m70 x2f8rax b_x2f8m70 b_x2f8rax
  have mb03 := mulb x2f8rdi x2f8rax b_x2f8rdi b_x2f8rax
  have mb10 := mulb x2f8m60 x2f8rdx b_x2f8m60 b_x2f8rdx
  have mb11 := mulb x2f8m68 x2f8rdx b_x2f8m68 b_x2f8rdx
  have mb12 := mulb x2f8m70 x2f8rdx b_x2f8m70 b_x2f8rdx
  have mb13 := mulb x2f8rdi x2f8rdx b_x2f8rdi b_x2f8rdx
  have mb20 := mulb x2f8m60 x2f8rcx b_x2f8m60 b_x2f8rcx
  have mb21 := mulb x2f8m68 x2f8rcx b_x2f8m68 b_x2f8rcx
  have mb22 := mulb x2f8m70 x2f8rcx b_x2f8m70 b_x2f8rcx
  have mb23 := mulb x2f8rdi x2f8rcx b_x2f8rdi b_x2f8rcx
  have mb30 := mulb x2f8m60 x2f8r10 b_x2f8m60 b_x2f8r10
  have mb31 := mulb x2f8m68 x2f8r10 b_x2f8m68 b_x2f8r10
  have mb32 := mulb x2f8m70 x2f8r10 b_x2f8m70 b_x2f8r10
  have mb33 := mulb x2f8rdi x2f8r10 b_x2f8rdi b_x2f8r10
  have mb40 := mulb x2f8m60 x2f8r8 b_x2f8m60 b_x2f8r8
  have mb41 := mulb x2f8m68 x2f8r8 b_x2f8m68 b_x2f8r8
  have mb42 := mulb x2f8m70 x2f8r8 b_x2f8m70 b_x2f8r8
  have mb43 := mulb x2f8rdi x2f8r8 b_x2f8rdi b_x2f8r8
  clear h_x33erax h_x33erbx h_x33ersi h_x33er9 h_x33er11 h_x33er12 h_x33er13 h_x33er15 h_x33em20 h_x33em28 h_x38bm30 h_x38bme8 h_x38bmf0 h_x38bmf8 h_x38bm100 h_x38bm108 h_x38bm110 h_x3earax h_x3earcx h_x3eardx h_x3earbx h_x3earsi h_x3ear8 h_x3eamc8 h_x3eamd0 h_x3eamd8 h_x3eame0 h_x429r10 h_x429r11 h_x429r13 h_x46brcx h_x46br9 h_x46br11 h_x46br13 h_x47frax h_x47frsi h_x47fr8 h_x47fr11
  have hchain := p0.trans (p1.trans (p2.trans (a0.trans (a1.trans (a2)))))
  clear p0 p1 p2 a0 a1 a2
  have hBlt : x3earbx + 2 ^ 64 * x47frsi + 2 ^ 128 * x47fr8 + 2 ^ 192 * x47frax + 2 ^ 256 * x47fr11 < 2 ^ 320 := by omega
  rw [hfull]
  omega

end Fv256.Amd64.R4Seg
