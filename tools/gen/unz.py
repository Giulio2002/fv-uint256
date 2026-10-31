import sys, subprocess
# unz.py isa Fn op wexpr tail : writer of a constant (no source operand). Derived from un2 output by text edits.
isa,fn,op,wexpr=sys.argv[1:5]; tail=sys.argv[5]
s=subprocess.check_output(['python3','-I','/srv/fv-uint256/build/gen/un2.py',isa,fn,op,wexpr,tail]).decode()
R=[
 ("(*uint256.Int).%s(x *Int) *Int"%fn,"(*uint256.Int).%s() *Int"%fn),
 ("`z = Fv256.Spec.%s x`"%op,"`z = Fv256.Spec.%s`"%op),
 ("theorem correctness (z x : BitVec 64)","theorem correctness (z : BitVec 64)"),
 ("[z, x]","[z]"),
 ("Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x","Ptr32 s.mem z true"),
 ("Spec.%s (val256 s.mem x.toNat)"%op,"Spec.%s"%op),
 ("Spec.%s (valueAt s x 32)"%op,"Spec.%s"%op),
 ("⟨⟨hz, hz'⟩, ⟨hx, hx'⟩, hzx⟩","⟨hz, hz'⟩"),
 ("  rcases hzx with rfl | hzx\n  all_goals simp only [Disjoint] at *\n  all_goals first | (exfalso; omega) | (janus_run;","  all_goals first | (exfalso; omega) | (janus_run;"),
 ("⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, hds, hzx⟩","⟨⟨_, hnw, hacc⟩, ⟨hzw, hz⟩, hds⟩"),
 ("  rcases hzx with rfl | hzx\n  all_goals first | (exfalso; omega) | (janus64_run","  all_goals first | (exfalso; omega) | (janus64_run"),
 ("Buffer s z 32 true ∧ Buffer s x 32 false ∧\n        Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x)","Buffer s z 32 true ∧\n        Disjoint z 32 (s.regs regSP) 8)"),
 ("def x : BitVec 64 := BitVec.ofNat 64 (DST + 32)\n",""),
 ("if i = 0 then z else if i = 1 then x\n      else if i = 28","if i = 0 then z\n      else if i = 28"),
 ("if i = 0 then z else if i = 3 then x else if i = 4","if i = 0 then z else if i = 4"),
 ("intro i h; simp at h\n    rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl <;> rfl","intro i h; simp at h; subst h; rfl"),
 ("theorem hpre : Ptr32 s0.mem z true ∧ Ptr32 s0.mem x false ∧ Aliasing z x :=\n  ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, Or.inr (by unfold Disjoint32 Disjoint z x; decide)⟩","theorem hpre : Ptr32 s0.mem z true :=\n  ⟨by decide, by decide⟩"),
 ("∃ (ret : Nat) (s : State) (z x : BitVec 64)","∃ (ret : Nat) (s : State) (z : BitVec 64)"),
 ("(Ptr32 s.mem z true ∧ Ptr32 s.mem x false ∧ Aliasing z x) :=\n  ⟨ret, s0, z, x, hret, setup, hpre⟩","Ptr32 s.mem z true :=\n  ⟨ret, s0, z, hret, setup, hpre⟩"),
 ("correctness z x ret hret s0 setup hpre","correctness z ret hret s0 setup hpre"),
 ("⟨ret, s0, z, x, hret, setup, hpre⟩","⟨ret, s0, z, hret, setup, hpre⟩"),
 ("theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Buffer s0 x 32 false ∧\n    Disjoint z 32 (s0.regs regSP) 8 ∧ Alias z x :=\n  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,\n    by unfold Disjoint; decide, Or.inr (by unfold Disjoint; decide)⟩","theorem hpre : StackWritable s0 0 8 ∧ Buffer s0 z 32 true ∧ Disjoint z 32 (s0.regs regSP) 8 :=\n  ⟨⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩, by unfold Disjoint; decide⟩"),
 ("(StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Buffer s x 32 false ∧\n      Disjoint z 32 (s.regs regSP) 8 ∧ Alias z x) :=\n  ⟨ret, s0, z, x, hret, setup, hpre⟩","(StackWritable s 0 8 ∧ Buffer s z 32 true ∧ Disjoint z 32 (s.regs regSP) 8) :=\n  ⟨ret, s0, z, hret, setup, hpre⟩"),
 ("simp only [valueAt, Disjoint, Alias] at *","simp only [valueAt, Disjoint] at *"),
 ("/-- equal or disjoint 32-byte objects -/\ndef Alias (p q : BitVec 64) : Prop := p = q ∨ Disjoint p 32 q 32\n\n",""),
]
for a,b in R:
    s=s.replace(a,b)
print(s)
