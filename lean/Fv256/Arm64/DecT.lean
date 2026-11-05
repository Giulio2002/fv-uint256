import Extracted
import Fv256.SpecE
import Fv256.UtilE

open Janus Janus.Tactic Janus.GoABI
open Fv256.E

namespace Fv256.Arm64.Dec


theorem dl_byte {p : Janus.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) (i : Nat) (hi : i < d.bytes.length) : m.readLE (d.base + i) 1 = d.bytes[i] := by
  rw [Janus.Arm64.Memory.readLE_one]; exact (h d hd).2 i hi

theorem dl_acc {p : Janus.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) : m.accessible d.base d.bytes.length false = true := by
  have h1 := (h d hd).1
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
  obtain ⟨r, hr, ⟨⟨⟨h2, h3⟩, h4⟩, _⟩⟩ := h1
  exact Janus.Arm64.Memory.accessible_of_mem m hr h2 h3 h4

theorem dl_disjoint {p : Janus.Program} {m : Janus.Arm64.Memory} (h : p.DataLoaded m) {d : Janus.DataSegment}
    (hd : d ∈ p.data) {a n : Nat} (hw : m.accessible a n true = true) :
    a + n ≤ d.base ∨ d.base + d.bytes.length ≤ a := by
  obtain ⟨hreg, _⟩ := h d hd
  simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hreg
  obtain ⟨r, hr, ⟨⟨⟨hb, he⟩, _⟩, hro⟩⟩ := hreg
  simp only [Janus.Arm64.Memory.accessible, Bool.and_eq_true, Bool.not_true, Bool.false_or,
    List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hw
  rcases hw.2 r hr with (h1 | h1) | h1
  · rw [hro] at h1; cases h1
  · omega
  · omega

abbrev smallsDat : Janus.DataSegment := Extracted.data[4]

set_option maxRecDepth 100000 in
theorem smalls_base : smallsDat.base = 1002589 := by decide
set_option maxRecDepth 100000 in
theorem smalls_len : smallsDat.bytes.length = 256 := by decide
theorem smalls_mem : smallsDat ∈ Extracted.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)

theorem smalls_tab : ∀ d, d < 100 → smallsDat.bytes[2*d]! = 48 + d / 10 ∧ smallsDat.bytes[2*d+1]! = 48 + d % 10 := by
  decide +kernel

theorem smalls_read_loaded {M : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded M) (d : Nat) (hd100 : d < 100) :
    M.readLE (1002589 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (1002589 + 2 * d + 1) 1 = 48 + d % 10 := by
  have h := smalls_tab d hd100
  have b0 := dl_byte hd smalls_mem (2 * d) (by rw [smalls_len]; omega)
  have b1 := dl_byte hd smalls_mem (2 * d + 1) (by rw [smalls_len]; omega)
  rw [smalls_base] at b0 b1
  rw [← Nat.add_assoc] at b1
  refine ⟨?_, ?_⟩
  · rw [b0, ← h.1]; exact (getElem!_pos smallsDat.bytes (2*d) (by rw [smalls_len]; omega)).symm
  · rw [b1, ← h.2]; exact (getElem!_pos smallsDat.bytes (2*d+1) (by rw [smalls_len]; omega)).symm


abbrev digitsDat : Janus.DataSegment := Extracted.data[2]

set_option maxRecDepth 100000 in
theorem digits_base : digitsDat.base = 989280 := by decide
set_option maxRecDepth 100000 in
theorem digits_len : digitsDat.bytes.length = 256 := by decide
theorem digits_mem : digitsDat ∈ Extracted.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)

theorem digits_tab : ∀ d, d < 10 → digitsDat.bytes[d]! = 48 + d := by
  decide +kernel

theorem digits_read_loaded {M : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded M) (d : Nat) (hd10 : d < 10) :
    M.readLE (989280 + d) 1 = 48 + d := by
  have b0 := dl_byte hd digits_mem d (by rw [digits_len]; omega)
  rw [digits_base] at b0
  rw [b0, ← digits_tab d hd10]
  exact (getElem!_pos digitsDat.bytes d (by rw [digits_len]; omega)).symm



/-- What the decimal code needs from the read-only data, and nothing about the regions: the two tables are readable,
hold their bytes, and are not writable (every writable range is apart from both). Unlike `DataLoaded` this survives
a callee's `MemFrame` (the callee's stores are in writable ranges). -/
structure TabsOK (M : Janus.Arm64.Memory) : Prop where
  acc1 : M.accessible 989280 256 false = true
  acc2 : M.accessible 1002589 256 false = true
  dig : ∀ d, d < 10 → M.readLE (989280 + d) 1 = 48 + d
  sm : ∀ d, d < 100 → M.readLE (1002589 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (1002589 + 2 * d + 1) 1 = 48 + d % 10
  ap : ∀ a n, M.accessible a n true = true →
    (a + n ≤ 989280 ∨ 989280 + 256 ≤ a) ∧ (a + n ≤ 1002589 ∨ 1002589 + 256 ≤ a)

theorem TabsOK.of_loaded {M : Janus.Arm64.Memory} (hd : Extracted.program.DataLoaded M) : TabsOK M := by
  refine ⟨?_, ?_, fun d h => digits_read_loaded hd d h, fun d h => smalls_read_loaded hd d h, ?_⟩
  · have := dl_acc hd digits_mem
    rwa [digits_base, digits_len] at this
  · have := dl_acc hd smalls_mem
    rwa [smalls_base, smalls_len] at this
  · intro a n hw
    have h1 := dl_disjoint hd digits_mem hw
    have h2 := dl_disjoint hd smalls_mem hw
    rw [digits_base, digits_len] at h1
    rw [smalls_base, smalls_len] at h2
    exact ⟨h1, h2⟩

theorem TabsOK.smalls {M : Janus.Arm64.Memory} (h : TabsOK M) (d : Nat) (hd : d < 100) :
    M.readLE (1002589 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (1002589 + 2 * d + 1) 1 = 48 + d % 10 := h.sm d hd

theorem TabsOK.digits {M : Janus.Arm64.Memory} (h : TabsOK M) (d : Nat) (hd : d < 10) : M.readLE (989280 + d) 1 = 48 + d :=
  h.dig d hd

theorem TabsOK.apart {M : Janus.Arm64.Memory} (h : TabsOK M) {a n : Nat} (hw : M.accessible a n true = true) :
    (a + n ≤ 989280 ∨ 989280 + 256 ≤ a) ∧ (a + n ≤ 1002589 ∨ 1002589 + 256 ≤ a) := h.ap a n hw

theorem TabsOK.writeLE {M : Janus.Arm64.Memory} (h : TabsOK M) {a n : Nat} (hw : M.accessible a n true = true) (v : Nat) :
    TabsOK (M.writeLE a n v) := by
  have ha := h.apart hw
  refine ⟨by simpa using h.acc1, by simpa using h.acc2, fun d hd => ?_, fun d hd => ?_, fun a' n' hw' => ?_⟩
  · rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]; exact h.digits d hd
  · have := h.smalls d hd
    rw [Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega), Janus.Arm64.Memory.readLE_writeLE_of_disjoint _ _ (by omega)]
    exact this
  · simp only [Janus.Arm64.Memory.accessible_writeLE] at hw'
    exact h.apart hw'

theorem TabsOK.two {M : Janus.Arm64.Memory} (h : TabsOK M) {b n : Nat} (hb : M.accessible b n true = true) {a1 k1 a2 k2 : Nat}
    (h1 : b ≤ a1) (h2 : a1 + k1 ≤ b + n) (h3 : b ≤ a2) (h4 : a2 + k2 ≤ b + n) (v1 v2 : Nat) :
    TabsOK ((M.writeLE a1 k1 v1).writeLE a2 k2 v2) := by
  refine TabsOK.writeLE (TabsOK.writeLE h (accessible_sub hb (Or.inr rfl) h1 h2) _) ?_ _
  simp only [Janus.Arm64.Memory.accessible_writeLE]
  exact accessible_sub hb (Or.inr rfl) h3 h4

theorem outside_of_all (a n : Nat) : ∀ rs : List (Nat × Nat), (∀ r ∈ rs, a + n ≤ r.1 ∨ r.2 ≤ a) → Outside a n rs
  | [], _ => trivial
  | (lo, hi) :: rs, h => ⟨h (lo, hi) (List.mem_cons_self ..), outside_of_all a n rs (fun r hr => h r (List.mem_cons_of_mem _ hr))⟩

/-- A callee's frame, whose ranges are writable, keeps the tables. -/
theorem TabsOK.frame {M M' : Janus.Arm64.Memory} (h : TabsOK M) {rs : List (Nat × Nat)} (hf : MemFrame M M' rs)
    (hw : ∀ r ∈ rs, M.accessible r.1 (r.2 - r.1) true = true) : TabsOK M' := by
  have key : ∀ a, (989280 ≤ a ∧ a < 989280 + 256) ∨ (1002589 ≤ a ∧ a < 1002589 + 256) →
      M'.readLE a 1 = M.readLE a 1 := by
    intro a ha
    refine hf.readLE a 1 (outside_of_all a 1 rs fun r hr => ?_)
    have := h.apart (hw r hr)
    omega
  refine ⟨by rw [hf.accessible]; exact h.acc1, by rw [hf.accessible]; exact h.acc2, fun d hd => ?_, fun d hd => ?_,
    fun a n hw' => ?_⟩
  · rw [key _ (Or.inl ⟨by omega, by omega⟩)]; exact h.digits d hd
  · rw [key _ (Or.inr ⟨by omega, by omega⟩), key _ (Or.inr ⟨by omega, by omega⟩)]; exact h.smalls d hd
  · rw [hf.accessible] at hw'; exact h.apart hw'


open Lean in
/-- Put the facts about the tables in the context for `janus64_run` (the analogue of `janus64_data`):
both tables are readable and every writable hypothesis is apart from them. -/
macro "tabs_data " h:ident " [" ws:ident,* "]" : tactic => do
  let mut tacs : Array (TSyntax `tactic) := #[← `(tactic| have _ := ($h).acc1), ← `(tactic| have _ := ($h).acc2)]
  for w in ws.getElems do
    tacs := tacs.push (← `(tactic| have _ := ($h).apart $w))
  `(tactic| ($[$tacs]*))

end Fv256.Arm64.Dec
