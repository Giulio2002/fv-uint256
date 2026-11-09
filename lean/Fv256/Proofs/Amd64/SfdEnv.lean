import Fv256.Proofs.Amd64.SfdProg
import Fv256.Proofs.Common.Spec
import Fv256.Proofs.Common.Util
import Fv256.Proofs.Common.SumC64

/-!
# Static runtime-model facts for `SetFromDecimal`'s error paths (amd64)

`StaticOK R2 T m`: the facts about the binary's static data that the `strconv.toError` proof reads, stated about a
memory `m`: the `internal/strconv.Error` itab and its type descriptor `T` (regular memory, not a direct interface,
size 8, a descriptor of the interface model `R2`), the `strconv.NumError` type descriptor bytes (`Size_ = 48`, has
pointers), and the readability of the write-barrier flag, `strconv.ErrSyntax` and the itab / constant objects.
`StaticOK.frame`: it survives any `MemFrame` whose ranges avoid `staticRanges T`.
-/

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Spec Janus.Spec.Type

namespace Fv256.Amd64.SfdEnv

abbrev numErrType : Nat := Fv256.Amd64.SfdProg.dataAddr.«type:strconv.NumError#3eb4e62e»
abbrev numErrItab : Nat := Fv256.Amd64.SfdProg.dataAddr.«go:itab.*strconv.NumError,error»
abbrev errItab : Nat := Fv256.Amd64.SfdProg.dataAddr.«go:itab.internal/strconv.Error,error»
abbrev synConst : Nat := Fv256.Amd64.SfdProg.dataAddr.«.rodata#9967e7a3»
abbrev strconvErrSyntax : Nat := Fv256.Amd64.SfdProg.dataAddr.«strconv.ErrSyntax»
abbrev wbFlag : Nat := Fv256.Amd64.SfdProg.dataAddr.«runtime.writeBarrier»

/-- the ranges `[lo, hi)` the static facts read (the descriptor `T` has `typeDescSize = 48` bytes). -/
def staticRanges (T : Nat) : List (Nat × Nat) :=
  [(errItab, errItab + 16), (synConst, synConst + 8), (strconvErrSyntax, strconvErrSyntax + 16), (wbFlag, wbFlag + 4),
    (numErrType, numErrType + 16), (T, T + 48)]

def StaticOK (R2 : IfaceModel) (T : Nat) (m : Janus.Arm64.Memory) : Prop :=
  m.readLE (errItab + 8) 8 = T ∧ R2.IsType T ∧ isRegularMemory m T = true ∧ isDirectIface m T = false ∧
  tySize m T = 8 ∧ m.readLE numErrType 8 = 48 ∧ m.readLE (numErrType + 8) 8 ≠ 0 ∧
  m.accessible wbFlag 4 false = true ∧ m.accessible strconvErrSyntax 16 false = true ∧
  m.accessible errItab 16 false = true ∧ m.accessible synConst 8 false = true ∧ m.accessible numErrType 16 false = true

theorem StaticOK.frame {R2 : IfaceModel} {T : Nat} {m m' : Janus.Arm64.Memory} {ws : List (Nat × Nat)}
    (h : StaticOK R2 T m) (hf : MemFrame m m' ws)
    (ho : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) ws) : StaticOK R2 T m' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩ := h
  have oI := ho (errItab, errItab + 16) (by simp [staticRanges])
  have oS := ho (synConst, synConst + 8) (by simp [staticRanges])
  have oE := ho (strconvErrSyntax, strconvErrSyntax + 16) (by simp [staticRanges])
  have oW := ho (wbFlag, wbFlag + 4) (by simp [staticRanges])
  have oN := ho (numErrType, numErrType + 16) (by simp [staticRanges])
  have oT := ho (T, T + 48) (by simp [staticRanges])
  simp only [Nat.add_sub_cancel_left] at oI oS oE oW oN oT
  refine ⟨?_, h2, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.readLE _ _ (Outside.of_sub oI (by omega) (by omega))]; exact h1
  · simp only [isRegularMemory, tyTFlag] at h3 ⊢
    rw [hf.readLE _ _ (Outside.of_sub oT (by omega) (by omega))]; exact h3
  · simp only [isDirectIface, tyTFlag] at h4 ⊢
    rw [hf.readLE _ _ (Outside.of_sub oT (by omega) (by omega))]; exact h4
  · simp only [tySize] at h5 ⊢
    rw [hf.readLE _ _ (Outside.of_sub oT (by omega) (by omega))]; exact h5
  · rw [hf.readLE _ _ (Outside.of_sub oN (by omega) (by omega))]; exact h6
  · rw [hf.readLE _ _ (Outside.of_sub oN (by omega) (by omega))]; exact h7
  · rw [hf.accessible]; exact h8
  · rw [hf.accessible]; exact h9
  · rw [hf.accessible]; exact h10
  · rw [hf.accessible]; exact h11
  · rw [hf.accessible]; exact h12


open Janus.Contracts

/-- The runtime environment of the error paths, for the absolute stack window `[lo, hi)` the function (and everything it
calls) may use: the interface model `R2`, the live runtime `R` with live set `L` and budget `b`, the static facts, and
the apartness of the window, the live objects, the guard word and the static data from the runtime's ranges. -/
def Env (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat) (s : State) : Prop :=
  lo ≤ (s.regs 4).toNat ∧ (s.regs 4).toNat + 8 ≤ hi ∧ hi ≤ 2 ^ 48 ∧ (s.regs 4).toNat % 8 = 0 ∧
  s.mem.accessible lo (hi - lo) true = true ∧
  (s.regs 14).toNat + 24 ≤ 2 ^ 48 ∧ s.mem.accessible ((s.regs 14).toNat + 16) 8 false = true ∧
  s.mem.readLE ((s.regs 14).toNat + 16) 8 < lo ∧
  Outside lo (hi - lo) R.rt ∧ Outside lo (hi - lo) R2.priv ∧
  Outside ((s.regs 14).toNat + 16) 8 R.rt ∧ Outside ((s.regs 14).toNat + 16) 8 R2.priv ∧
  ((s.regs 14).toNat + 16 + 8 ≤ lo ∨ hi ≤ (s.regs 14).toNat + 16) ∧
  (∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(lo, hi)]) ∧
  StaticOK R2 T s.mem ∧ R2.Env s.mem (s.regs 14) ∧
  R.inv b L (s.regs 14).toNat (view R.rt L s.mem) ∧
  (∀ r ∈ L, Outside r.1 (r.2 - r.1) [(lo, hi)])

/-- `Env` survives a frame that writes the window and one buffer `[z, z+32)` apart from everything the runtime
model looks at (inside the live set or outside `R.rt`), when `RSP` and `g` are unchanged. -/
theorem Env.frame {R : RtInv} {R2 : IfaceModel} (hl : R2.Laws) {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {s s' : State} (h : Env R R2 T b L lo hi s)
    (hsp : lo ≤ (s'.regs 4).toNat ∧ (s'.regs 4).toNat + 8 ≤ hi ∧ (s'.regs 4).toNat % 8 = 0) (hg : s'.regs 14 = s.regs 14)
    {z : Nat} (hf : MemFrame s.mem s'.mem [(lo, hi), (z, z + 32)])
    (hzR : Outside z 32 R.rt ∨ InRanges z 32 L) (hzP : Outside z 32 R2.priv)
    (hzS : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(z, z + 32)])
    (hzg : (s.regs 14).toNat + 16 + 8 ≤ z ∨ z + 32 ≤ (s.regs 14).toNat + 16) : Env R R2 T b L lo hi s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h
  have hgw : Outside ((s.regs 14).toNat + 16) 8 [(lo, hi), (z, z + 32)] := by
    simp only [outside_cons, outside_nil, and_true]; omega
  have hgv : s'.mem.readLE ((s.regs 14).toNat + 16) 8 = s.mem.readLE ((s.regs 14).toNat + 16) 8 :=
    hf.readLE _ _ hgw
  have hstat : ∀ r ∈ staticRanges T, Outside r.1 (r.2 - r.1) [(lo, hi), (z, z + 32)] := by
    intro r hr
    have a := h14 r hr
    have b := hzS r hr
    simp only [outside_cons, outside_nil, and_true] at a b ⊢
    exact ⟨a, b⟩
  unfold Env
  rw [hg]
  rw [hg] at *
  refine ⟨hsp.1, hsp.2.1, h3, hsp.2.2, ?_, h6, ?_, ?_, h9, h10, h11, h12, h13, h14, ?_, ?_, ?_, h18⟩
  · rw [hf.accessible]; exact h5
  · rw [hf.accessible]; exact h7
  · rw [hgv]; exact h8
  · exact StaticOK.frame h15 hf hstat
  · exact hl.env_frame _ _ _ h16 (Janus.Spec.Map.Agrees.of_memFrame hf (by
      intro a ha
      obtain ⟨r, hr, h1, h2⟩ := ha
      have a1 := MemFrame.outside_mem h10 hr
      have a2 := MemFrame.outside_mem hzP hr
      simp only [outside_cons, outside_nil, and_true]
      omega))
  · exact RtInv.inv_frame' hf (by
      intro r hr
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
      rcases hr with rfl | rfl
      · exact Or.inl h9
      · simpa using hzR) h17


/-- `Env.frame` for a frame that only writes the window. -/
theorem Env.frame0 {R : RtInv} {R2 : IfaceModel} (hl : R2.Laws) {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}
    {s s' : State} (h : Env R R2 T b L lo hi s)
    (hsp : lo ≤ (s'.regs 4).toNat ∧ (s'.regs 4).toNat + 8 ≤ hi ∧ (s'.regs 4).toNat % 8 = 0) (hg : s'.regs 14 = s.regs 14)
    (hf : MemFrame s.mem s'.mem [(lo, hi)]) (hw : lo + 32 ≤ hi) : Env R R2 T b L lo hi s' := by
  have h' := h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18⟩ := h'
  refine Env.frame hl h hsp hg (z := lo) (hf.mono (fun a n ha => ?_)) (Or.inl (Outside.of_sub h9 (by omega) (by omega)))
    (Outside.of_sub h10 (by omega) (by omega)) ?_ (by omega)
  · simp only [outside_cons, outside_nil, and_true] at ha ⊢; exact ha.1
  · intro r hr
    have := h14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

theorem Env.shrink {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi lo' hi' : Nat} {s : State}
    (h : Env R R2 T b L lo hi s) (h1 : lo ≤ lo') (h2 : hi' ≤ hi) (h3 : lo' ≤ (s.regs 4).toNat)
    (h4 : (s.regs 4).toNat + 8 ≤ hi') : Env R R2 T b L lo' hi' s := by
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18⟩ := h
  have sub : ∀ rs : List (Nat × Nat), Outside lo (hi - lo) rs → Outside lo' (hi' - lo') rs := fun rs h =>
    Outside.of_sub h (by omega) (by omega)
  refine ⟨h3, h4, by omega, e4, ?_, e6, e7, by omega, sub _ e9, sub _ e10, e11, e12, by omega, ?_, e15, e16, e17, ?_⟩
  · exact Arm64.Memory.accessible_mono _ e5 (by omega) (by omega)
  · intro r hr
    have := e14 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega
  · intro r hr
    have := e18 r hr
    simp only [outside_cons, outside_nil, and_true] at this ⊢
    omega

end Fv256.Amd64.SfdEnv
