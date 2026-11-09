#!/usr/bin/env python3 -I
# sb_ensures_arm.py N... : rewrites lean/Fv256/Proofs/Arm64/SetBytes<N>.lean so that `correctness` is an `Ensures` statement
# (the case len >= N) and the bounds-check panic (len < N) is the separate theorem `panics`; the proof body is the former
# `correctness`, now `core`.
import os, re, sys
ROOT = os.environ.get('FV_ROOT') or os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
for n in map(int, sys.argv[1:]):
    p = f"{ROOT}/lean/Fv256/Proofs/Arm64/SetBytes{n}.lean"
    s = open(p).read()
    if "theorem core" in s: continue
    m = re.search(r"StackOK s (\d+) (\d+)\)", s); B, A = m.group(1), m.group(2)
    s = s.replace("theorem correctness (z ptr len cap : BitVec 64) (ret : Nat)", "theorem core (z ptr len cap : BitVec 64) (ret : Nat)", 1)
    i = s.index("namespace Witness")
    wrap = f'''theorem correctness (z ptr len cap : BitVec 64) :
    Ensures Extracted.program Extracted.entry [z, ptr, len, cap]
      (fun s => GuardOK s 0 ∧ StackOK s {B} {A} ∧ {n} ≤ len.toNat ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr {n} false ∧
        Disjoint z.toNat 32 ptr.toNat {n} ∧ Disjoint z.toNat 32 (s.sp.toNat - {B}) {int(B)+int(A)} ∧
        Disjoint ptr.toNat {n} (s.sp.toNat - {B}) {int(B)+int(A)})
      (fun s s' => s'.regs 0 = z ∧
        val256 s'.mem z.toNat = Spec.fromBE (fun i => s.mem.readLE (ptr.toNat + i) 1) {n} ∧
        Util.OnlyWrites2 s.mem s'.mem z.toNat 32 (s.sp.toNat - {B}) {int(B)+int(A)}) := by
  intro ret hret s hs ⟨hg, hst, hl, h1, h2, h3, h4, h5⟩
  exact (core z ptr len cap ret hret s hs hg hst).1 hl h1 h2 h3 h4 h5

/-- The bounds check: with fewer than {n} bytes the call reaches the panic stub. -/
theorem panics (z ptr len cap : BitVec 64) (ret : Nat)
    (hret : RetAddr Extracted.program ret) (s : State)
    (hs : CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s)
    (hg : GuardOK s 0) (hst : StackOK s {B} {A}) :
    len.toNat < {n} → Ptr32 s.mem z true → Panics (Extracted.program.withExit ret) s :=
  (core z ptr len cap ret hret s hs hg hst).2

'''
    s = s[:i] + wrap + s[i:]
    a = s.index("theorem nonvacuous"); b = s.index("theorem returns")
    s = s[:a] + f'''theorem nonvacuous : ∃ (ret : Nat) (s : State) (z ptr len cap : BitVec 64), RetAddr Extracted.program ret ∧
    CallSetup (Extracted.program.withExit ret) Extracted.entry [z, ptr, len, cap] s ∧
    (GuardOK s 0 ∧ StackOK s {B} {A} ∧ {n} ≤ len.toNat ∧ Ptr32 s.mem z true ∧ Ptr s.mem ptr {n} false ∧
      Disjoint z.toNat 32 ptr.toNat {n} ∧ Disjoint z.toNat 32 (s.sp.toNat - {B}) {int(B)+int(A)} ∧
      Disjoint ptr.toNat {n} (s.sp.toNat - {B}) {int(B)+int(A)}) :=
  ⟨ret, s0, z, ptr, {n}, {n}, hret, setup, hg, hst, hpre⟩

''' + s[b:]
    s = s.replace(f"(correctness z ptr {n} {n} ret hret s0 setup hg hst).1", f"(core z ptr {n} {n} ret hret s0 setup hg hst).1")
    open(p, "w").write(s)
    print("ok", n)
