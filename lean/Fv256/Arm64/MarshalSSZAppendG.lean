import Extracted

open Janus Janus.Arm64 Janus.GoABI Janus.Tactic Janus.Spec Janus.Contracts

namespace Fv256.Arm64.MarshalSSZAppendG

/-- the element type of the byte slice, an argument of every `growslice` call -/
abbrev u8T : Nat := Extracted.dataAddr.«type:uint8#6a8c7679»

/-- The cost bound of one `growslice` call made with `newLen ≤ len0 + 32`. -/
def Kc (len0 : Nat) : Nat := 2 * (2 * (len0 + 32) + 192) + 24

theorem cost_le (len0 len cc b : Nat) (h1 : len + 8 ≤ len0 + 32) (h2 : cc < len + 8) (hb : Kc len0 ≤ b) :
    roundupsize (nextslicecap (len + 8) cc) true ≤ b := by
  have h3 := nextslicecap_le (len + 8) cc h2
  have h4 := roundupsize_le (nextslicecap (len + 8) cc) true
  unfold Kc at hb
  omega

/-- The invariant at the start of a block: the slice `(P, l, C)` (so `l + 8` is what the next append needs), the
frame of the function, the memory facts, the runtime's invariant for the live set `L` and the budget `b`. -/
structure BI (R : RtInv) (s S : State) (z : BitVec 64) (ret dp len0 cap0 : Nat) (len pp cc : BitVec 64) (b : Nat)
    (L : List (Nat × Nat)) : Prop where
  sp : S.sp = s.sp - 128#64
  r0 : S.regs 0 = z
  r1 : S.regs 1 = pp
  r3 : S.regs 3 = cc
  r5 : S.regs 5 = len + 8#64
  r18 : S.regs 18 = s.regs 18
  r28 : S.regs 28 = s.regs 28
  r29 : S.regs 29 = s.sp - 136#64
  rd1 : S.mem.readLE (s.sp.toNat - 128) 8 = ret
  rd2 : S.mem.readLE (s.sp.toNat - 136) 8 = (s.regs 29).toNat
  rd3 : S.mem.readLE (s.sp.toNat + 8) 8 = z.toNat
  hd : Extracted.program.DataLoaded S.mem
  hw : S.mem.accessible (s.sp.toNat - 4232) (4232 + 40) true = true
  frame : MemFrame s.mem S.mem (R.rt ++ [(s.sp.toNat - 4232, s.sp.toNat + 40)])
  zsame : ∀ i, i < 32 → S.mem.bytes (z.toNat + i) = s.mem.bytes (z.toNat + i)
  inv : R.inv b L (s.regs 28).toNat (view R.rt L S.mem)
  hLs : ∀ r ∈ L, Outside r.1 (r.2 - r.1) [(s.sp.toNat - 4232, s.sp.toNat + 40)]
  hzL : InRanges z.toNat 32 L ∨ Outside z.toNat 32 R.rt
  lge : len0 ≤ len.toNat
  lle : len.toNat + 8 ≤ len0 + 32
  lc : len.toNat ≤ cc.toNat
  Cb : cc.toNat < 2 ^ 40
  Pb : pp.toNat + cc.toNat ≤ 2 ^ 48
  hdj : Apart pp.toNat cc.toNat (s.sp.toNat - 4232) 4272
  room : len.toNat + 8 ≤ cc.toNat → S.mem.accessible pp.toNat cc.toNat true = true ∧ (InRanges pp.toNat cc.toNat L ∨ Outside pp.toNat cc.toNat R.rt)
  grow : cc.toNat < len.toNat + 8 → (0 < len.toNat → S.mem.accessible pp.toNat len.toNat false = true)
  bud : Kc len0 ≤ b
  who : (pp.toNat = dp ∧ cc.toNat = cap0) ∨ InRanges pp.toNat cc.toNat R.rt
  pre : ∀ i, i < len0 → S.mem.bytes (pp.toNat + i) = s.mem.bytes (dp + i)
  mid : S.mem.readLE (pp.toNat + len0) (len.toNat - len0) = s.mem.readLE z.toNat (len.toNat - len0)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem blk0 (impl : List Segment) (R : RtInv) (ret : Nat)
    (hret : RetAddr (Extracted.program.link impl) ret)
    (hg : RtLiveContract (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.growslice") 4096 R growsliceSpec growsliceLive)
    (hok : ∀ p n c, R.ok (Extracted.program.contractAddr "runtime.growslice") [p, n, c, 8, u8T])
    (s S : State) (z : BitVec 64) (dp len0 cap0 b : Nat) (len pp cc : BitVec 64) (L : List (Nat × Nat))
    (Q : Outcome → Prop)
    (hal : s.sp.toNat % 16 = 0) (hb' : 4232 ≤ s.sp.toNat) (ha : s.sp.toNat + 40 ≤ 2 ^ 48)
    (hg1 : (s.regs 28).toNat + 24 ≤ 2 ^ 48) (hg2 : s.mem.accessible ((s.regs 28).toNat + 16) 8 false = true)
    (hg3 : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4224 < s.sp.toNat)
    (hzp : s.mem.accessible z.toNat 32 false = true) (hz48 : z.toNat + 32 ≤ 2 ^ 48)
    (hzd : Disjoint z.toNat 32 (s.sp.toNat - 4232) 4272)
    (hout : Outside (s.sp.toNat - 4232) 4272 R.rt)
    (hga : Apart ((s.regs 28).toNat + 16) 8 (s.sp.toNat - 4232) 4272)
    (hgr : Outside ((s.regs 28).toNat + 16) 8 R.rt)
    (hdt : Apart u8T 16 (s.sp.toNat - 4232) 4272)
    (hpc : S.pc = BitVec.ofNat 64 (Extracted.entry + 0x24))
    (hI : BI R s S z ret dp len0 cap0 len pp cc b L)
    (hcont : ∀ (S' : State) (pp' cc' : BitVec 64) (b' : Nat) (L' : List (Nat × Nat)),
      S'.pc = BitVec.ofNat 64 (Extracted.entry + 0x70) →
      BI R s S' z ret dp len0 cap0 (len + 8#64) pp' cc' b' L' → b - Kc len0 ≤ b' →
      Reaches ((Extracted.program.link impl).withExit ret) S' Q) :
    Reaches ((Extracted.program.link impl).withExit ret) S Q := by
  obtain ⟨hsp, h0, h1, h3, h5, h18, h28, h29, hrd1, hrd2, hrd3, hd, hw, hfr, hzs, hinv, hLs, hzL, hlge, hlle, hlc, hC, hPb,
    hdj, hroom, hgrow, hbud, hwho, hpre, hmid⟩ := hI
  have hlen8 : (len + 8#64).toNat = len.toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  by_cases hl : len.toNat + 8 ≤ cc.toNat
  · obtain ⟨hacc, hdest⟩ := hroom hl
    janus_data hd [hw, hacc]
    janus_run until [Extracted.entry + 0x70]
    all_goals (trace_state; fail "probe-fast")
  · obtain ⟨hrd⟩ := (⟨hgrow (by omega)⟩ : Nonempty _)
    have hcost := cost_le len0 len.toNat cc.toNat b hlle (by omega) hbud
    -- U-ACCSUB workaround: the engine states this goal about the entry memory `s.mem`
    have hrd' : 0 < len.toNat → s.mem.accessible pp.toNat len.toNat false = true := fun h => by
      rw [← hfr.accessible]; exact hrd h
    have hg3' : s.mem.readLE ((s.regs 28).toNat + 16) 8 + 4096 < s.sp.toNat - 128 := by omega
    janus_data hd [hw]
    janus_run until [Extracted.entry + 0x70] calls [hg]
    all_goals (trace_state; fail "probe-grow")

end Fv256.Arm64.MarshalSSZAppendG
