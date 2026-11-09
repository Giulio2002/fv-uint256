namespace Fv256.Amd64.RecipSeg

theorem rcx_lt (c x14crcx x160rcx xc49rcx : Nat) (hcl : c ≤ 63) (hcx : x14crcx = (63 - c + 192) % 18446744073709551616)
    (h2 : x160rcx = (x14crcx % 64 + 18446744073709551615) % 18446744073709551616)
    (h3 : xc49rcx = if 2 ^ 63 ≤ x160rcx then 0 else x160rcx) : xc49rcx < 64 := by
  rw [h3]; split
  · omega
  · omega

end Fv256.Amd64.RecipSeg
