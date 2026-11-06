import Fv256.Spec
import Fv256.Util
import Fv256.SpecB
import Fv256.UtilB

/-!
# arm64 `udivrem`: the state at the dispatch point (`Front`) and the final-memory predicate (`FinOK`)

Extraction independent.  `sp` below is the stack pointer after the prologue (`sp0 - 224`).
-/

open Janus Janus.Arm64

namespace Fv256.Arm64.UdivremFront

/-- Memory of `udivrem` after the front part (`dn`, `un` built and spilled, just before `udivremBy1` / `udivremKnuth`). -/
structure Front (sp : Nat) (M0 M5 : Memory) (qp up dp remp L n ulen s x29 x30 : Nat) : Prop where
  hn : 1 ≤ n
  hn4 : n ≤ 4
  hulen : ulen ≤ L
  hnu : n ≤ ulen
  hs : s ≤ 63
  dwv : Fv256.B.wv M0 dp 4 = Fv256.B.wv M0 dp n
  dtop : M0.readLE (dp + 8 * (n - 1)) 8 ≠ 0
  clz : s = clzNat 64 (M0.readLE (dp + 8 * (n - 1)) 8)
  uwv : Fv256.B.wv M0 up L = Fv256.B.wv M0 up ulen
  utop : 0 < ulen → M0.readLE (up + 8 * (ulen - 1)) 8 ≠ 0
  dn : Fv256.B.wv M5 (sp + 160) n = Fv256.B.wv M0 dp n * 2 ^ s
  dntop : 2 ^ 63 ≤ M5.readLE (sp + 160 + 8 * (n - 1)) 8
  un : Fv256.B.wv M5 (sp + 80) (ulen + 1) = Fv256.B.wv M0 up ulen * 2 ^ s
  frame : MemFrame M0 M5 [(sp - 8, sp + 8), (sp + 80, sp + 216), (sp + 232, sp + 240), (sp + 256, sp + 264), (sp + 288, sp + 296)]
  s_rem : M5.readLE (sp + 288) 8 = remp
  s_s : M5.readLE (sp + 208) 8 = s
  s_x29 : M5.readLE (sp - 8) 8 = x29
  s_x30 : M5.readLE sp 8 = x30

/-- The result of `udivrem(quot, u, d, rem)` (`sp0 = sp + 224` the entry stack pointer). -/
def FinOK (L : Nat) (M0 Mf : Memory) (qp up dp remp sp0 : Nat) : Prop :=
  Fv256.B.wv Mf qp L = Fv256.B.wv M0 up L / Fv256.B.wv M0 dp 4 ∧
  (remp ≠ 0 → Fv256.B.wv Mf remp 4 = Fv256.B.wv M0 up L % Fv256.B.wv M0 dp 4) ∧
  (remp = 0 → MemFrame M0 Mf [(qp, qp + 8 * L), (sp0 - 344, sp0 - 8), (sp0 + 8, sp0 + 72)]) ∧
  (remp ≠ 0 → MemFrame M0 Mf [(qp, qp + 8 * L), (remp, remp + 32), (sp0 - 344, sp0 - 8), (sp0 + 8, sp0 + 72)])

end Fv256.Arm64.UdivremFront
