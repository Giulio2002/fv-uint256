import Fv256.Amd64.ErlpDefs

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic Janus.Contracts Janus.Contracts.ICall Fv256.Rlp

namespace Fv256.Amd64.EncodeRLP

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- the path `1 ≤ bitlen ≤ 7`: one `newobject([1]byte)`, the byte `z[0]`, the `Write` -/
theorem erlp_p1 (impl : List Amd64.Segment) (rt : List (Nat × Nat)) (H : RtReady) (fn stack : Nat) (R : Res)
    (z tab w : BitVec 64) (ret : Nat) (hret : RetAddr (Extracted.program.link impl) ret)
    (hnew : NewobjectContract64 (Extracted.program.link impl)
      (Extracted.program.contractAddr "runtime.newobject") rt 4096 H)
    (hw : ICallContract64 (Extracted.program.link impl) fn 4 stack 56 rt (fun _ => []) R (WP z w))
    (s S : State) (h4104 : 4104 ≤ stack) (hfn : fn < 2 ^ 47)
    (hwb : 56 + stack ≤ (s.regs 4).toNat) (hwn : (s.regs 4).toNat + 32 ≤ 2 ^ 48)
    (hwa : s.mem.accessible ((s.regs 4).toNat - (56 + stack)) (56 + stack + 32) true = true)
    (hout : Outside ((s.regs 4).toNat - 56 - stack) (stack + 88) rt)
    (htb : tab.toNat + 32 ≤ 2 ^ 48) (htr : Outside (tab.toNat + 24) 8 rt) (hfn' : s.mem.readLE (tab.toNat + 24) 8 = fn)
    (hta : s.mem.accessible (tab.toNat + 24) 8 false = true)
    (htd : (tab.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ tab.toNat + 24))
    (hH2 : H [tyOne] (s.regs 14).toNat ((s.regs 4).toNat - 56) (rtView rt s.mem))
    (hd : Extracted.program.DataLoaded s.mem) (hal : (s.regs 4).toNat % 8 = 0) (hr : s.mem.readLE (s.regs 4).toNat 8 = ret)
    (hzo : Outside z.toNat 32 rt) (hzd : z.toNat + 32 ≤ (s.regs 4).toNat - 56 - stack ∨ (s.regs 4).toNat + 32 ≤ z.toNat)
    (hzn : z.toNat ≠ 0) (hzb : z.toNat + 32 ≤ 2 ^ 48) (hza : s.mem.accessible z.toNat 32 false = true) (bl : Nat) (hbl : Spec.bitLen (s.mem.readLE z.toNat 32) = bl) (hb1 : bl ≠ 0) (hb7 : bl ≤ 7)
    (hJ : EJ z tab w s S bl) :
    Reaches ((Extracted.program.link impl).withExit ret) S
      (IsReturn fun s' => ABIReturn s s' ∧ EPost rt stack R z w s s') := by
  obtain ⟨hpc, h0, h2, h4, h5, h14, hx, hdf, hfr, hreg, m16, m24, m8⟩ := hJ
  have hrv : rtView rt S.mem = rtView rt s.mem := by
    refine Janus.Contracts.Stack.rtView_eq_of_frame hfr hreg (fun a ha => ?_)
    have hd := InRanges.disjoint ha hout
    simp only [outside_cons, outside_nil]
    refine ⟨?_, ?_, trivial⟩ <;> omega
  have hv0 : s.mem.readLE z.toNat 32 ≠ 0 := fun h => by simp [Spec.bitLen, h] at hbl; omega
  have hv7 := bitLen_le7_lt _ hv0 (by omega)
  have hv8 : s.mem.readLE z.toNat 8 = s.mem.readLE z.toNat 32 := by
    have := Janus.Arm64.Memory.readLE_mod s.mem z.toNat 32 8 (by omega)
    omega
  have hrb := rlpBytes_small _ hv0 (by omega)
  have hS8 : S.mem.readLE z.toNat 8 = s.mem.readLE z.toNat 8 :=
    hfr.readLE z.toNat 8 (by simp only [outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> omega)
  have hS32 : S.mem.readLE z.toNat 32 = s.mem.readLE z.toNat 32 :=
    hfr.readLE z.toNat 32 (by simp only [outside_cons, outside_nil]; refine ⟨?_, ?_, trivial⟩ <;> omega)
  janus_eval_nat h_to : tyOne
  rw [h_to] at hH2
  rw [← hrv] at hH2
  janus64_data hd [hwa]
  janus64_run until [Extracted.entry + 0x166] calls [hnew.pos, hw]
  janus_grab InRanges as hin
  have hdj := InRanges.disjoint hin hout
  have hdt := InRanges.disjoint hin htr
  have hdz := InRanges.disjoint hin hzo
  janus_grab 4096 as hfn
  have hzr := hfn.readLE z.toNat 32 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (Nat.le_refl _))
  have hzr8 := hfn.readLE z.toNat 8 (out_z hzo hzd h4104 hwb (Nat.le_refl _) (off_ok0 _))
  simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, hS8, hS32] at hzr hzr8
  have hza8 : s.mem.accessible z.toNat 8 false = true :=
    Janus.Arm64.Memory.accessible_mono _ hza (Nat.le_refl _) (by omega)
  have hzacc := hfn.accessible z.toNat 8 false
  simp only [Janus.Arm64.Memory.accessible_writeLE, hfr.accessible, hza8] at hzacc
  have hmod : s.mem.readLE z.toNat 32 % 256 = s.mem.readLE z.toNat 32 := Nat.mod_eq_of_lt (by omega)
  janus64_run [rlpVal, hzr, hzr8, hzacc, hv8, hrb, hmod, hzn, strBytes_write1, List.length_singleton] calls [hnew.pos, hw]
  refine ⟨?_, ?_⟩
  · simp only [hx]
  · apply epost_of (z := z) (hzo := hzo) (hzd := hzd)
    · apply epost_ex
      · assumption
      · rfl
      · rfl
    · janus_frame

end Fv256.Amd64.EncodeRLP
