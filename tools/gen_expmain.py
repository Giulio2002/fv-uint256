import re,sys
# builds the top-k odd block for ExpMain from the top0 template
src=open('/srv/fv-uint256-wf/lean/Fv256/Amd64/ExpMain.lean').read()
EP="BitVec.toNat (s.regs 1)"
def E(k): return "(Arm64.Memory.readLE s.mem (%s + %d) 8)"%(EP,8*k) if k else "(Arm64.Memory.readLE s.mem (%s) 8)"%EP
def block_entry(k, names, c, extra_inv_tail):
    Ek=E(k)
    NN=f"(63 - Janus.Arm64.clzNat 64 {Ek} + {c})"
    B32="(Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 32)"
    B8="(Arm64.Memory.readLE s.mem (BitVec.toNat (s.regs 3)) 8)"
    Z="(BitVec.toNat (s.regs 0))"; EPN=f"({EP})"
    out=f"""  · rename_i {names}
    have hcl := (Fv256.B.clz_norm {Ek} {'e%dnz'%k} (Fv256.Util.readLE8_lt _ _)).1
    have hn0 : {NN} < 2 ^ 20 := by omega_e
    refine Fv256.Amd64.ExpLoop1.loop1 s _ {NN} {Z} {EPN} {B8} hn0 (by omega_e) hnw hacc (min {NN} 64) 0 1 {B32} {E(0)} _ (by omega_e) ?inv{k} ?hex{k}
    · unfold Fv256.Amd64.ExpLoop1.Inv1
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [setRegF, Fv256.Amd64.ExpLoop1.head1, Extracted.entry]
      · omega_e
      · decide
      · have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 32
        simpa using this
      · exact Fv256.Util.readLE8_lt _ _
      · exact Fv256.Util.readLE8_lt _ _
      · simp [setRegF]
      · simp [setRegF]; exact Fv256.F.nbvk _ {c}
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF]
      · simp [setRegF, setXmmF, hx15]
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 104 + 16 = BitVec.toNat (s.regs 4) - 88 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        try simp
      · simp only []
        rw [Janus.Arm64.Memory.readLE_add _ _ 16 16]
        have e1 : BitVec.toNat (s.regs 4) - 72 + 16 = BitVec.toNat (s.regs 4) - 56 := by omega_e
        rw [e1]
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        rw [Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3)) 16; simpa using this),
          Nat.mod_eq_of_lt (by have := Janus.Arm64.Memory.readLE_lt s.mem (BitVec.toNat (s.regs 3) + 16) 16; simpa using this),
          ← Janus.Arm64.Memory.readLE_add]
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 0).isLt
        simp only [Nat.reducePow, Nat.reducePow] at this ⊢
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 1).isLt
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        omega_e
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := Fv256.Util.readLE8_lt s.mem (BitVec.toNat (s.regs 3))
        omega_e
      · rfl
      · rfl
      · simp only []
        simp (disch := omega) only [Janus.Arm64.Memory.readLE_writeLE_of_disjoint, Janus.Arm64.Memory.readLE_writeLE_self]
        have := (s.regs 5).isLt
        omega_e
      · janus_frame
"""
    return out
if __name__=='__main__':
    print(block_entry(1,"g1 e3z e2z e1nz",65,""))
