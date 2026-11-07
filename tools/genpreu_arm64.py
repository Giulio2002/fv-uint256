#!/usr/bin/env python3
# generates the PreUS structure / PreU conj def / PreU.toS for arm64 UnmarshalSpec
F = [
("r0","s.regs 0 = z"),
("r1","s.regs 1 = pI"),
("r2","s.regs 2 = nI"),
("mod","Mod C R R2 T L"),
("env","Env C R R2 T b L lo hi s"),
("lo4","lo + 4640 ≤ s.sp.toNat"),
("hi4","s.sp.toNat + 24 ≤ hi"),
("okH","R.ok sb [s.sp.toNat - 72, pI.toNat, nI.toNat]"),
("okD","R.ok sb [s.sp.toNat - 40, pI.toNat, nI.toNat]"),
("cost","roundupsize nI.toNat true ≤ b"),
("stWin","Outside st 2048 [(lo, hi)]"),
("stRt","Outside st 2048 R.rt"),
("stPriv","Outside st 2048 R2.priv"),
("stZ","Outside st 2048 [(z.toNat, z.toNat + 32)]"),
("mult","MultOK C z.toNat lo hi s.mem"),
("multRt","Outside C.mulTab 40 R.rt"),
("multK","∀ k, 1 ≤ k → k ≤ 4 → Outside (s.mem.readLE (C.mulTab + 8 * k) 8) 32 R.rt"),
("eofA","s.mem.accessible C.ioEOF 16 false = true"),
("eofW","Outside C.ioEOF 16 [(lo, hi), (z.toNat, z.toNat + 32)]"),
("eofR","Outside C.ioEOF 16 R.rt"),
("bigA","s.mem.accessible C.errBig 16 false = true"),
("bigW","Outside C.errBig 16 [(lo, hi), (z.toNat, z.toNat + 32)]"),
("bigR","Outside C.errBig 16 R.rt"),
("init","Fv256.Arm64.UnmarshalSpec.InitDone C R2 s.mem"),
("maxA","s.mem.accessible C.maxStr 78 false = true"),
("maxW","Outside C.maxStr 78 [(lo, hi), (z.toNat, z.toNat + 32)]"),
("maxR","Outside C.maxStr 78 R.rt"),
("maxB","∀ k, k < 78 → s.mem.readLE (C.maxStr + k) 1 = maxDigit k"),
("zbuf","Ptr32 s.mem z true"),
("zwin","z.toNat + 32 ≤ lo ∨ hi ≤ z.toNat"),
("zR","Outside z.toNat 32 R.rt ∨ InRanges z.toNat 32 L"),
("zP","Outside z.toNat 32 R2.priv"),
("zS","∀ r ∈ staticRanges C T, Outside r.1 (r.2 - r.1) [(z.toNat, z.toNat + 32)]"),
("zg","(s.regs 28).toNat + 16 + 8 ≤ z.toNat ∨ z.toNat + 32 ≤ (s.regs 28).toNat + 16"),
("ibuf","Ptr s.mem pI nI.toNat false"),
("iwin","pI.toNat + nI.toNat ≤ lo ∨ hi ≤ pI.toNat"),
("chunk","∀ sl, 1 ≤ sl → sl ≤ 19 → sl ≤ nI.toNat → R.ok C.mallocgc [sl, 0, 0] ∧ (∀ q p, R.ok C.memmove [q, p, sl]) ∧ blockSize sl true + blockSize 48 false ≤ b - roundupsize nI.toNat true"),
]
sig = "(sb st : Nat) (R : RtInv) (R2 : IfaceModel) (T b : Nat) (L : List (Nat × Nat)) (lo hi : Nat)\n    (z pI nI : BitVec 64) (s : State)"
print("structure PreUS %s : Prop where" % sig)
for n,t in F: print("  %s : %s" % (n,t))
print()
print("def PreU %s : Prop :=" % sig)
print("  " + " ∧\n  ".join("(%s)" % t for n,t in F))
print()
names = ", ".join(n for n,t in F)
print("theorem PreU.toS {sb st : Nat} {R : RtInv} {R2 : IfaceModel} {T b : Nat} {L : List (Nat × Nat)} {lo hi : Nat}\n    {z pI nI : BitVec 64} {s : State} (h : PreU C sb st R R2 T b L lo hi z pI nI s) :\n    PreUS C sb st R R2 T b L lo hi z pI nI s := by")
print("  obtain ⟨%s⟩ := h" % names)
print("  exact ⟨%s⟩" % names)
