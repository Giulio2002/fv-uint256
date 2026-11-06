import Fv256.Arm64.PrettyProg
import Fv256.Arm64.P.T

open Janus Janus.Tactic Janus.GoABI
open Fv256.Arm64.P

namespace Fv256.Arm64.Pd

abbrev digitsDat : Janus.DataSegment := Fv256.Arm64.PrettyProg.data[2]
abbrev smallsDat : Janus.DataSegment := Fv256.Arm64.PrettyProg.data[3]
abbrev zeroDat : Janus.DataSegment := Fv256.Arm64.PrettyProg.data[1]

set_option maxRecDepth 100000 in
theorem digits_base : digitsDat.base = 989280 := by decide
set_option maxRecDepth 100000 in
theorem digits_len : digitsDat.bytes.length = 256 := by decide
theorem digits_mem : digitsDat ∈ Fv256.Arm64.PrettyProg.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)
theorem digits_tab : ∀ d, d < 10 → digitsDat.bytes[d]! = 48 + d := by decide +kernel

set_option maxRecDepth 100000 in
theorem smalls_base : smallsDat.base = 1002456 := by decide
set_option maxRecDepth 100000 in
theorem smalls_len : smallsDat.bytes.length = 389 := by decide
theorem smalls_mem : smallsDat ∈ Fv256.Arm64.PrettyProg.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)
theorem smalls_tab : ∀ d, d < 100 → smallsDat.bytes[133 + 2*d]! = 48 + d / 10 ∧ smallsDat.bytes[133 + 2*d+1]! = 48 + d % 10 := by
  decide +kernel
/-- the 133 zero characters that initialise `out` -/
theorem zeros_tab : ∀ i, i < 133 → smallsDat.bytes[i]! = 48 := by decide +kernel

theorem digits_read_loaded {M : Janus.Arm64.Memory} (hd : Fv256.Arm64.PrettyProg.program.DataLoaded M) (d : Nat) (hd10 : d < 10) :
    M.readLE (989280 + d) 1 = 48 + d := by
  have b0 := dl_byte hd digits_mem d (by rw [digits_len]; omega)
  rw [digits_base] at b0
  rw [b0, ← digits_tab d hd10]
  exact (getElem!_pos digitsDat.bytes d (by rw [digits_len]; omega)).symm

theorem smalls_read_loaded {M : Janus.Arm64.Memory} (hd : Fv256.Arm64.PrettyProg.program.DataLoaded M) (d : Nat) (hd100 : d < 100) :
    M.readLE (1002589 + 2 * d) 1 = 48 + d / 10 ∧ M.readLE (1002589 + 2 * d + 1) 1 = 48 + d % 10 := by
  have h := smalls_tab d hd100
  have b0 := dl_byte hd smalls_mem (133 + 2 * d) (by rw [smalls_len]; omega)
  have b1 := dl_byte hd smalls_mem (133 + 2 * d + 1) (by rw [smalls_len]; omega)
  rw [smalls_base] at b0 b1
  rw [← Nat.add_assoc] at b1
  rw [show 1002456 + (133 + 2 * d) = 1002589 + 2 * d by omega] at b0
  rw [show 1002456 + (133 + 2 * d) + 1 = 1002589 + 2 * d + 1 by omega] at b1
  refine ⟨?_, ?_⟩
  · rw [b0, ← h.1]; exact (getElem!_pos smallsDat.bytes (133 + 2*d) (by rw [smalls_len]; omega)).symm
  · rw [b1, ← h.2]; exact (getElem!_pos smallsDat.bytes (133 + 2*d+1) (by rw [smalls_len]; omega)).symm

theorem TabsOK.of_loaded {M : Janus.Arm64.Memory} (hd : Fv256.Arm64.PrettyProg.program.DataLoaded M) : TabsOK M := by
  refine TabsOK.intro ?_ ?_ (fun d h => digits_read_loaded hd d h) (fun d h => smalls_read_loaded hd d h) ?_
  · have := dl_acc hd digits_mem
    rwa [digits_base, digits_len] at this
  · have := dl_acc hd smalls_mem
    have h2 := accessible_sub this (Or.inl rfl) (a := 1002589) (n := 256) (by rw [smalls_base]; omega) (by rw [smalls_base, smalls_len]; omega)
    exact h2
  · intro a n hw
    have h1 := dl_disjoint hd digits_mem hw
    have h2 := dl_disjoint hd smalls_mem hw
    rw [digits_base, digits_len] at h1
    rw [smalls_base, smalls_len] at h2
    exact ⟨h1, by omega⟩

/-- the zero string that `out` is initialised from -/
theorem zeros_read_loaded {M : Janus.Arm64.Memory} (hd : Fv256.Arm64.PrettyProg.program.DataLoaded M) (i : Nat) (hi : i < 133) :
    M.readLE (1002456 + i) 1 = 48 := by
  have b0 := dl_byte hd smalls_mem i (by rw [smalls_len]; omega)
  rw [smalls_base] at b0
  rw [b0, ← zeros_tab i hi]
  exact (getElem!_pos smallsDat.bytes i (by rw [smalls_len]; omega)).symm

set_option maxRecDepth 100000 in
theorem zeroDat_base : zeroDat.base = 960826 := by decide
set_option maxRecDepth 100000 in
theorem zeroDat_len : zeroDat.bytes.length = 256 := by decide
theorem zeroDat_mem : zeroDat ∈ Fv256.Arm64.PrettyProg.program.data := List.getElem_mem (by set_option maxRecDepth 100000 in decide)
set_option maxRecDepth 100000 in
theorem zeroDat_b0 : zeroDat.bytes[0]! = 48 := by decide +kernel

theorem zeroStr_read {M : Janus.Arm64.Memory} (hd : Fv256.Arm64.PrettyProg.program.DataLoaded M) :
    M.readLE 960826 1 = 48 ∧ M.accessible 960826 1 false = true := by
  have b0 := dl_byte hd zeroDat_mem 0 (by rw [zeroDat_len]; omega)
  rw [zeroDat_base] at b0
  refine ⟨?_, ?_⟩
  · rw [Nat.add_zero] at b0
    rw [b0]
    have := zeroDat_b0
    simpa [getElem!_pos zeroDat.bytes 0 (by rw [zeroDat_len]; omega)] using this
  · have := dl_acc hd zeroDat_mem
    rw [zeroDat_base, zeroDat_len] at this
    exact accessible_sub this (Or.inl rfl) (by omega) (by omega)

end Fv256.Arm64.Pd
