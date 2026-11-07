import Janus
import Fv256.SpecC
import Fv256.SpecFormat

/-!
# `(*uint256.Int).Format`, fast path (ii), arm64: shared definitions (Extracted-free)

arm64 twin of `Fv256.FormatFastDefs`.  Frame of `Format`: `SP` after the prologue (`str x30,[sp,#-80]!; stur x29,[sp,#-8]`),
the saved `x30` is `[SP]`, the saved `x29` is `[SP-8]`; the spills are `[SP+88] = z`, `[SP+96] = tab`, `[SP+104] = data`,
`[SP+112] = ch` (4 bytes).
-/

open Janus Janus.Arm64

namespace Fv256.FormatFastA64

/-- ordinary steps from `S` reach one of the listed addresses with the paired predicate (arm64) -/
def RT (p : Janus.Program) (S : State) (T : List (Nat × (State → Prop))) : Prop :=
  ∃ k S', Janus.Program.Steps p S k S' ∧ ∃ t ∈ T, S'.pc = BitVec.ofNat 64 t.1 ∧ t.2 S'

theorem RT.of_reachesRet {p : Janus.Program} {S : State} {pc : Nat} {Q : State → Prop}
    (h : Janus.Tactic.ReachesRet p (BitVec.ofNat 64 pc) S Q) : RT p S [(pc, Q)] := by
  obtain ⟨k, S', hs, hr, hq⟩ := h
  exact ⟨k, S', hs, (pc, Q), List.mem_singleton_self _, hr, hq⟩

theorem RT.trans {p : Janus.Program} {S : State} {T T' : List (Nat × (State → Prop))}
    (h : RT p S T)
    (hk : ∀ t ∈ T, ∀ S', S'.pc = BitVec.ofNat 64 t.1 → t.2 S' → RT p S' T') : RT p S T' := by
  obtain ⟨k, S', hs, t, ht, hr, hq⟩ := h
  obtain ⟨j, S'', hs2, r⟩ := hk t ht S' hr hq
  exact ⟨k + j, S'', hs.trans hs2, r⟩

theorem RT.widen {p : Janus.Program} {S : State} {T T' : List (Nat × (State → Prop))}
    (h : RT p S T)
    (hT : ∀ t ∈ T, ∃ t' ∈ T', t'.1 = t.1 ∧ ∀ s, t.2 s → t'.2 s) : RT p S T' := by
  obtain ⟨k, S', hs, t, ht, hr, hq⟩ := h
  obtain ⟨t', ht', h1, h2⟩ := hT t ht
  exact ⟨k, S', hs, t', ht', by rw [h1]; exact hr, h2 _ hq⟩

theorem RT.here {p : Janus.Program} {S : State} {T : List (Nat × (State → Prop))}
    (t : Nat × (State → Prop)) (ht : t ∈ T) (hr : S.pc = BitVec.ofNat 64 t.1) (hq : t.2 S) : RT p S T :=
  ⟨0, S, .refl S, t, ht, hr, hq⟩

/-- a run keeps the memory regions: attach it to every exit -/
theorem RT.regions {p : Janus.Program} {S : State} {T : List (Nat × (State → Prop))}
    (h : RT p S T) :
    RT p S (T.map fun t => (t.1, fun s => t.2 s ∧ s.mem.regions = S.mem.regions)) := by
  obtain ⟨k, S', hs, t, ht, hr, hq⟩ := h
  exact ⟨k, S', hs, (t.1, fun s => t.2 s ∧ s.mem.regions = S.mem.regions), List.mem_map_of_mem ht, hr,
    hq, Janus.Program.Steps.regions hs⟩

/-- the frame list of the fast path: the callee windows below the saved slots `[r - stack, r - 8)` and the argument area
`[r + 8, r + 40)` and the spill slots `[r + 88, r + 116)` (the saved `x29` at `r - 8` and `x30` at `r` are outside) -/
def FL (rt : List (Nat × Nat)) (r stack : Nat) : List (Nat × Nat) :=
  rt ++ [(r - stack, r - 8), (r + 8, r + 40), (r + 88, r + 116)]

open Janus.Contracts.ICall Janus.Spec in
/-- the standing precondition of the fast path, at the state `S0` just after the `z != 0` split (`Format+0x44`, arm64):
`SP` is the local frame (entry SP - 80); `[SP+96] = tab`, `[SP+104] = data` are the spilled interface words -/
def FPre (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (fW fP fF fWr : Nat) (S0 : State) : Prop :=
  S0.regs 0 = z ∧ S0.regs 1 = tab ∧ S0.regs 2 = data ∧ S0.regs 29 = S0.sp - 8#64 ∧
  S0.sp.toNat % 16 = 0 ∧ 8 ≤ stack ∧ 8 + stack ≤ S0.sp.toNat ∧ S0.sp.toNat + 0x78 ≤ 2 ^ 48 ∧
  S0.mem.accessible (S0.sp.toNat - stack) (stack + 0x78) true = true ∧
  Outside (S0.sp.toNat - stack) (stack + 0x78) rt ∧
  S0.mem.readLE (S0.sp.toNat + 96) 8 = tab.toNat ∧ S0.mem.readLE (S0.sp.toNat + 104) 8 = data.toNat ∧
  CodePtrOK fW ∧ CodePtrOK fP ∧ CodePtrOK fF ∧ CodePtrOK fWr ∧
  tab.toNat + 0x38 ≤ 2 ^ 48 ∧ S0.mem.accessible (tab.toNat + 0x18) 32 false = true ∧
  S0.mem.readLE (tab.toNat + 0x18) 8 = fF ∧ S0.mem.readLE (tab.toNat + 0x20) 8 = fP ∧
  S0.mem.readLE (tab.toNat + 0x28) 8 = fW ∧ S0.mem.readLE (tab.toNat + 0x30) 8 = fWr ∧
  Outside (tab.toNat + 0x18) 32 rt ∧
  (tab.toNat + 0x38 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ tab.toNat + 0x18) ∧
  Ptr32 S0.mem z false ∧ Outside z.toNat 32 rt ∧
  (z.toNat + 32 ≤ S0.sp.toNat - stack ∨ S0.sp.toNat + 0x78 ≤ z.toNat)

/-- the invariant between the sites: `SP`, `x29`, `x28`, `x18` kept, memory changed only in `FL`, the spills hold `z, tab, data, ch` -/
def FInv (rt : List (Nat × Nat)) (stack : Nat) (z tab data : BitVec 64) (ch32 : Nat) (S0 S : State) : Prop :=
  S.sp = S0.sp ∧ S.regs 29 = S0.regs 29 ∧ S.regs 28 = S0.regs 28 ∧ S.regs 18 = S0.regs 18 ∧
  MemFrame S0.mem S.mem (FL rt S0.sp.toNat stack) ∧
  S.mem.readLE (S0.sp.toNat + 88) 8 = z.toNat ∧ S.mem.readLE (S0.sp.toNat + 96) 8 = tab.toNat ∧
  S.mem.readLE (S0.sp.toNat + 104) 8 = data.toNat ∧ S.mem.readLE (S0.sp.toNat + 112) 4 = ch32


/-- the runtime invariant of `R2` survives from `S` to `S'` (for every budget and live set), the goroutine register being `S.regs 28` -/
def RPres (R2 : Janus.Contracts.RtInv) (S S' : State) : Prop :=
  ∀ b L, R2.inv b L (S.regs 28).toNat (Janus.Contracts.view R2.rt L S.mem) →
    R2.inv b L (S.regs 28).toNat (Janus.Contracts.view R2.rt L S'.mem)

theorem RPres.refl (R2 : Janus.Contracts.RtInv) (S : State) : RPres R2 S S := fun _ _ h => h

theorem RPres.trans {R2 : Janus.Contracts.RtInv} {S1 S2 S3 : State} (h12 : RPres R2 S1 S2) (h23 : RPres R2 S2 S3)
    (e : S2.regs 28 = S1.regs 28) : RPres R2 S1 S3 := by
  intro b L h
  have := h12 b L h
  rw [← e] at this ⊢
  exact h23 b L this

theorem RPres.of_mem {R2 : Janus.Contracts.RtInv} {S S' : State} (hm : S'.mem = S.mem) : RPres R2 S S' := by
  intro b L h; rw [hm]; exact h

/-- the `preserves` fact of an icall (call state `sc`, same goroutine and same view as `S`), as `RPres` -/
theorem rpres_call {R2 : Janus.Contracts.RtInv} {S S' sc : State} {m : Memory}
    (hpr : Janus.Contracts.ICall.RtPreserves R2 sc m) (hsc28 : sc.regs 28 = S.regs 28)
    (hv : ∀ L, Janus.Contracts.view R2.rt L sc.mem = Janus.Contracts.view R2.rt L S.mem)
    (hm : S'.mem = m) : RPres R2 S S' := by
  intro b L h
  rw [hm]
  have := hpr b L (by rw [hsc28, hv]; exact h)
  rw [hsc28] at this
  exact this


theorem rr_mono {p : Janus.Program} {ret : BitVec 64} {S : State} {Q Q' : State → Prop}
    (h : Janus.Tactic.ReachesRet p ret S Q) (hQ : ∀ S', Q S' → Q' S') : Janus.Tactic.ReachesRet p ret S Q' := by
  obtain ⟨k, s', hs, hr, hq⟩ := h
  exact ⟨k, s', hs, hr, hQ s' hq⟩

theorem rr_trans {p : Janus.Program} {ret mid : BitVec 64} {S : State} {Q Qmid : State → Prop}
    (h1 : Janus.Tactic.ReachesRet p mid S Qmid)
    (h2 : ∀ S', S'.pc = mid → Qmid S' → Janus.Tactic.ReachesRet p ret S' Q) :
    Janus.Tactic.ReachesRet p ret S Q := by
  obtain ⟨k, s', hs, hr, hq⟩ := h1
  obtain ⟨j, s'', hs2, hr2, hq2⟩ := h2 s' hr hq
  exact ⟨k + j, s'', hs.trans hs2, hr2, hq2⟩

open Janus.Tactic in
/-- one query site of the chain: the call returns (`hcall`), then either the plain continuation `cont` or the big path `big`,
by the test `ok` on the result registers `x0, x1`; the two exits carry the history `H`, the result relation `A` and the answer's side -/
theorem site_rt {p : Janus.Program} {S : State} {ret cont big : Nat} {Qi : State → Prop} (A : W64 → W64 → W64 → Prop)
    (ok : W64 → W64 → Prop) (H : Prop) (hH : H)
    (hcall : ReachesRet p (BitVec.ofNat 64 ret) S
      (fun S' => Qi S' ∧ ∃ j0 j1 j2, A j0 j1 j2 ∧ S'.regs 0 = j0 ∧ S'.regs 1 = j1))
    (hc : ∀ S', S'.pc = BitVec.ofNat 64 ret → Qi S' → ok (S'.regs 0) (S'.regs 1) →
      ReachesRet p (BitVec.ofNat 64 cont) S' Qi)
    (hb : ∀ S', S'.pc = BitVec.ofNat 64 ret → Qi S' → ¬ ok (S'.regs 0) (S'.regs 1) →
      ReachesRet p (BitVec.ofNat 64 big) S' Qi) :
    RT p S [(cont, fun S' => Qi S' ∧ H ∧ ∃ j0 j1 j2, A j0 j1 j2 ∧ ok j0 j1),
            (big, fun S' => Qi S' ∧ H ∧ ∃ j0 j1 j2, A j0 j1 j2 ∧ ¬ ok j0 j1)] := by
  refine RT.trans (RT.of_reachesRet hcall) ?_
  intro t ht S' hr hq
  simp only [List.mem_singleton] at ht
  subst ht
  obtain ⟨hi2, j0, j1, j2, hR, h0, h1⟩ := hq
  by_cases hk : ok j0 j1
  · have k1 : ReachesRet p (BitVec.ofNat 64 cont) S'
        (fun S'' => Qi S'' ∧ H ∧ ∃ j0 j1 j2, A j0 j1 j2 ∧ ok j0 j1) :=
      rr_mono (hc S' hr hi2 (by rw [h0, h1]; exact hk)) (fun S'' h => ⟨h, hH, j0, j1, j2, hR, hk⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_self .., rfl, fun _ h => h⟩
  · have k1 : ReachesRet p (BitVec.ofNat 64 big) S'
        (fun S'' => Qi S'' ∧ H ∧ ∃ j0 j1 j2, A j0 j1 j2 ∧ ¬ ok j0 j1) :=
      rr_mono (hb S' hr hi2 (by rw [h0, h1]; exact hk)) (fun S'' h => ⟨h, hH, j0, j1, j2, hR, hk⟩)
    refine RT.widen (RT.of_reachesRet k1) ?_
    intro t ht
    simp only [List.mem_singleton] at ht
    subst ht
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), rfl, fun _ h => h⟩


open Janus.Contracts.ICall in
/-- the `Width` call answered with the `ok` result `j1` (low bit of `x1`) -/
def WRes (RW : Res) (data : BitVec 64) (fW : Nat) (r3 j1 : BitVec 64) : Prop :=
  ∃ j0 j2, RW data (BitVec.ofNat 64 fW) data r3 j0 j1 j2

open Janus.Contracts.ICall in
/-- the `Precision` call answered with an `ok` result `j1` satisfying `p` -/
def PRes (RP : Res) (data : BitVec 64) (fP : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r2 r3 j0 j1 j2, RP data (BitVec.ofNat 64 fP) r2 r3 j0 j1 j2 ∧ p j1

open Janus.Contracts.ICall in
/-- the `Flag(c)` call answered with a result `x0 = j0` satisfying `p j0` -/
def FRes (RF : Res) (data : BitVec 64) (fF c : Nat) (p : BitVec 64 → Prop) : Prop :=
  ∃ r3 j0 j1 j2, RF data (BitVec.ofNat 64 c) (BitVec.ofNat 64 fF) r3 j0 j1 j2 ∧ p j0

open Janus.Contracts.ICall in
/-- every query answered "plain": no width, no precision, none of the five flags (the machine tests bit 0 of the result) -/
def PlainHist (RW RP RF : Res) (data : BitVec 64) (fW fP fF : Nat) (r3 j1 : BitVec 64) : Prop :=
  ((((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x23 (fun j => j.toNat % 2 = 0)

open Janus.Contracts.ICall in
/-- the answers the machine acted on when it left the query chain for the big path (first non-plain answer, or a verb outside `d v s x`) -/
def NotPlain (RW RP RF : Res) (data : BitVec 64) (fW fP fF : Nat) (r3 : BitVec 64) (ch : Nat) : Prop :=
  (∃ j1, WRes RW data fW r3 j1 ∧ j1.toNat % 2 ≠ 0) ∨
  (∃ j1, (WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, ((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, (((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, ((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, (((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, ((((((WRes RW data fW r3 j1 ∧ j1.toNat % 2 = 0) ∧ PRes RP data fP (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2b (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x20 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x2d (fun j => j.toNat % 2 = 0)) ∧ FRes RF data fF 0x30 (fun j => j.toNat % 2 = 0)) ∧
    FRes RF data fF 0x23 (fun j => j.toNat % 2 ≠ 0)) ∨
  (∃ j1, PlainHist RW RP RF data fW fP fF r3 j1 ∧ ch ≠ 100 ∧ ch ≠ 115 ∧ ch ≠ 118 ∧ ch ≠ 120)

/-- the call-site property of the fast path's `Write(p []byte)` call: the receiver data word, the slice `(ptr, len, cap)` whose
first `len` bytes are readable and equal `bs`, and `len ≤ cap` -/
def FastWP (data : BitVec 64) (bs : List Nat) (sc : State) : Prop :=
  sc.regs 0 = data ∧ Janus.Contracts.StrOut sc.mem (sc.regs 1).toNat (sc.regs 2).toNat bs ∧
    (sc.regs 2).toNat ≤ (sc.regs 3).toNat

end Fv256.FormatFastA64
