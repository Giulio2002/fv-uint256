import Fv256.Proofs.Common.DecProg
import Fv256.Proofs.Common.SpecE
import Fv256.Proofs.Common.UtilE

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.E

namespace Fv256.Amd64.Dec

abbrev smallsDat : Janus.DataSegment := Fv256.DecProg.data[3]

set_option maxRecDepth 100000 in
theorem smalls_base : smallsDat.base = 5176582 := by decide
set_option maxRecDepth 100000 in
theorem smalls_len : smallsDat.bytes.length = 256 := by decide
theorem smalls_mem : smallsDat ∈ Fv256.DecProg.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)

theorem smalls_tab : ∀ d, d < 100 → smallsDat.bytes[2*d]! = 48 + d / 10 ∧ smallsDat.bytes[2*d+1]! = 48 + d % 10 := by
  decide +kernel

theorem smalls_read_loaded {M : Memory} (hd : Fv256.DecProg.program.DataLoaded M) (d : Nat) (hd100 : d < 100) :
    M.readLE (5176582 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (5176582 + 2 * d + 1) 1 = 48 + d % 10 := by
  have h := smalls_tab d hd100
  have b0 := DataLoaded.byte hd smalls_mem (2 * d) (by rw [smalls_len]; omega)
  have b1 := DataLoaded.byte hd smalls_mem (2 * d + 1) (by rw [smalls_len]; omega)
  rw [smalls_base] at b0 b1
  rw [← Nat.add_assoc] at b1
  refine ⟨?_, ?_⟩
  · rw [b0, ← h.1]; exact (getElem!_pos smallsDat.bytes (2*d) (by rw [smalls_len]; omega)).symm
  · rw [b1, ← h.2]; exact (getElem!_pos smallsDat.bytes (2*d+1) (by rw [smalls_len]; omega)).symm


abbrev digitsDat : Janus.DataSegment := Fv256.DecProg.data[1]

set_option maxRecDepth 100000 in
theorem digits_base : digitsDat.base = 5163273 := by decide
set_option maxRecDepth 100000 in
theorem digits_len : digitsDat.bytes.length = 256 := by decide
theorem digits_mem : digitsDat ∈ Fv256.DecProg.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)

theorem digits_tab : ∀ d, d < 10 → digitsDat.bytes[d]! = 48 + d := by
  decide +kernel

theorem digits_read_loaded {M : Memory} (hd : Fv256.DecProg.program.DataLoaded M) (d : Nat) (hd10 : d < 10) :
    M.readLE (5163273 + d) 1 = 48 + d := by
  have b0 := DataLoaded.byte hd digits_mem d (by rw [digits_len]; omega)
  rw [digits_base] at b0
  rw [b0, ← digits_tab d hd10]
  exact (getElem!_pos digitsDat.bytes d (by rw [digits_len]; omega)).symm



/-- What the decimal code needs from the read-only data, and nothing about the regions: the two tables are readable,
hold their bytes, and are not writable (every writable range is apart from both). Unlike `DataLoaded` this survives
a callee's `MemFrame` (the callee's stores are in writable ranges). -/
@[irreducible] def TabsOK (M : Memory) : Prop :=
  M.accessible 5163273 256 false = true ∧ M.accessible 5176582 256 false = true ∧
  (∀ d, d < 10 → M.readLE (5163273 + d) 1 = 48 + d) ∧
  (∀ d, d < 100 → M.readLE (5176582 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (5176582 + 2 * d + 1) 1 = 48 + d % 10) ∧
  (∀ a n, M.accessible a n true = true →
    (a + n ≤ 5163273 ∨ 5163273 + 256 ≤ a) ∧ (a + n ≤ 5176582 ∨ 5176582 + 256 ≤ a))

theorem TabsOK.acc1 {M : Memory} (h : TabsOK M) : M.accessible 5163273 256 false = true := by
  unfold TabsOK at h; exact h.1
theorem TabsOK.acc2 {M : Memory} (h : TabsOK M) : M.accessible 5176582 256 false = true := by
  unfold TabsOK at h; exact h.2.1
theorem TabsOK.dig {M : Memory} (h : TabsOK M) : ∀ d, d < 10 → M.readLE (5163273 + d) 1 = 48 + d := by
  unfold TabsOK at h; exact h.2.2.1
theorem TabsOK.sm {M : Memory} (h : TabsOK M) : ∀ d, d < 100 → M.readLE (5176582 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (5176582 + 2 * d + 1) 1 = 48 + d % 10 := by
  unfold TabsOK at h; exact h.2.2.2.1
theorem TabsOK.ap {M : Memory} (h : TabsOK M) : ∀ a n, M.accessible a n true = true →
    (a + n ≤ 5163273 ∨ 5163273 + 256 ≤ a) ∧ (a + n ≤ 5176582 ∨ 5176582 + 256 ≤ a) := by
  unfold TabsOK at h; exact h.2.2.2.2
theorem TabsOK.intro {M : Memory} (h1 : M.accessible 5163273 256 false = true) (h2 : M.accessible 5176582 256 false = true)
    (h3 : ∀ d, d < 10 → M.readLE (5163273 + d) 1 = 48 + d)
    (h4 : ∀ d, d < 100 → M.readLE (5176582 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (5176582 + 2 * d + 1) 1 = 48 + d % 10)
    (h5 : ∀ a n, M.accessible a n true = true → (a + n ≤ 5163273 ∨ 5163273 + 256 ≤ a) ∧ (a + n ≤ 5176582 ∨ 5176582 + 256 ≤ a)) : TabsOK M := by
  unfold TabsOK; exact ⟨h1, h2, h3, h4, h5⟩

theorem TabsOK.of_loaded {M : Memory} (hd : Fv256.DecProg.program.DataLoaded M) : TabsOK M := by
  refine TabsOK.intro ?_ ?_ (fun d h => digits_read_loaded hd d h) (fun d h => smalls_read_loaded hd d h) ?_
  · have := DataLoaded.accessible hd digits_mem
    rwa [digits_base, digits_len] at this
  · have := DataLoaded.accessible hd smalls_mem
    rwa [smalls_base, smalls_len] at this
  · intro a n hw
    have h1 := dataLoaded_disjoint hd digits_mem hw
    have h2 := dataLoaded_disjoint hd smalls_mem hw
    rw [digits_base, digits_len] at h1
    rw [smalls_base, smalls_len] at h2
    exact ⟨h1, h2⟩

theorem TabsOK.smalls {M : Memory} (h : TabsOK M) (d : Nat) (hd : d < 100) :
    M.readLE (5176582 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (5176582 + 2 * d + 1) 1 = 48 + d % 10 := h.sm d hd

theorem TabsOK.digits {M : Memory} (h : TabsOK M) (d : Nat) (hd : d < 10) : M.readLE (5163273 + d) 1 = 48 + d :=
  h.dig d hd

theorem TabsOK.apart {M : Memory} (h : TabsOK M) {a n : Nat} (hw : M.accessible a n true = true) :
    (a + n ≤ 5163273 ∨ 5163273 + 256 ≤ a) ∧ (a + n ≤ 5176582 ∨ 5176582 + 256 ≤ a) := h.ap a n hw

theorem TabsOK.writeLE {M : Memory} (h : TabsOK M) {a n : Nat} (hw : M.accessible a n true = true) (v : Nat) :
    TabsOK (M.writeLE a n v) := by
  have ha := h.ap _ _ hw
  refine TabsOK.intro (by simpa using h.acc1) (by simpa using h.acc2) (fun d hd => ?_) (fun d hd => ?_) (fun a' n' hw' => ?_)
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h.dig d hd
  · have := h.smalls d hd
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact this
  · simp only [Janus.Arm64.Memory.accessible_writeLE] at hw'
    exact h.ap _ _ hw'

theorem TabsOK.two {M : Memory} (h : TabsOK M) {b n : Nat} (hb : M.accessible b n true = true) {a1 k1 a2 k2 : Nat}
    (h1 : b ≤ a1) (h2 : a1 + k1 ≤ b + n) (h3 : b ≤ a2) (h4 : a2 + k2 ≤ b + n) (v1 v2 : Nat) :
    TabsOK ((M.writeLE a1 k1 v1).writeLE a2 k2 v2) := by
  refine TabsOK.writeLE (TabsOK.writeLE h (accessible_sub hb (Or.inr rfl) h1 h2) _) ?_ _
  simp only [Janus.Arm64.Memory.accessible_writeLE]
  exact accessible_sub hb (Or.inr rfl) h3 h4

theorem outside_of_all (a n : Nat) : ∀ rs : List (Nat × Nat), (∀ r ∈ rs, a + n ≤ r.1 ∨ r.2 ≤ a) → Outside a n rs
  | [], _ => trivial
  | (lo, hi) :: rs, h => ⟨h (lo, hi) (List.mem_cons_self ..), outside_of_all a n rs (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

/-- A callee's frame, whose ranges are writable, keeps the tables. -/
theorem TabsOK.frame {M M' : Memory} (h : TabsOK M) {rs : List (Nat × Nat)} (hf : MemFrame M M' rs)
    (hw : ∀ r ∈ rs, M.accessible r.1 (r.2 - r.1) true = true) : TabsOK M' := by
  have key : ∀ a, (5163273 ≤ a ∧ a < 5163273 + 256) ∨ (5176582 ≤ a ∧ a < 5176582 + 256) →
      M'.readLE a 1 = M.readLE a 1 := by
    intro a ha
    refine hf.readLE a 1 (outside_of_all a 1 rs fun r hr => ?_)
    have := h.ap _ _ (hw r hr)
    omega
  refine TabsOK.intro (by rw [hf.accessible]; exact h.acc1) (by rw [hf.accessible]; exact h.acc2) (fun d hd => ?_) (fun d hd => ?_)
    (fun a n hw' => ?_)
  · rw [key _ (Or.inl ⟨by omega, by omega⟩)]; exact h.dig d hd
  · rw [key _ (Or.inr ⟨by omega, by omega⟩), key _ (Or.inr ⟨by omega, by omega⟩)]; exact h.smalls d hd
  · rw [hf.accessible] at hw'; exact h.ap _ _ hw'


open Lean in
/-- Put the facts about the tables in the context for `janus64_run` (the analogue of `janus64_data`):
both tables are readable and every writable hypothesis is apart from them. -/
macro "tabs_data " h:ident " [" ws:ident,* "]" : tactic => do
  let mut tacs : Array (TSyntax `tactic) := #[← `(tactic| have _ := ($h).acc1), ← `(tactic| have _ := ($h).acc2)]
  for w in ws.getElems do
    tacs := tacs.push (← `(tactic| have _ := ($h).apart $w))
  `(tactic| ($[$tacs]*))

end Fv256.Amd64.Dec
