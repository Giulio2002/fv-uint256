import Janus
open Janus
example (m : Janus.Arm64.Memory) (p : Nat) (w : Bool) : m.accessible p 0 w = true := by
  simp [Janus.Arm64.Memory.accessible]
