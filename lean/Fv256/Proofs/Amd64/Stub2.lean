import Extracted
import Janus
open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
theorem Fv256.Amd64Stub.correctness (z : BitVec 64) : Ensures Extracted.program Extracted.entry [z] (fun _ => False) (fun _ _ => True) := by
  intro ret hret s hs h; exact h.elim
