import Fv256.Proofs.Amd64.R4Arith
import Fv256.Proofs.Amd64.R4Branch
import Fv256.Proofs.Amd64.R4LinkA
import Fv256.Proofs.Amd64.R4G.C_1cd_4ac

open Janus Janus.Amd64 Janus.Amd64.GoABI Janus.Amd64.Tactic
open Fv256.Amd64.ReduceSpec Fv256.Amd64.ReduceSegA

set_option exponentiation.threshold 700
namespace Fv256.Amd64.R4Seg

theorem readLE_40' (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 40 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 + 2 ^ 256 * m.readLE (a + 32) 8 := by
  rw [show 40 = 32 + 8 from rfl, Janus.Arm64.Memory.readLE_add, Fv256.Util.readLE_32]

theorem readLE_64' (m : Janus.Arm64.Memory) (a : Nat) :
    m.readLE a 64 = m.readLE a 8 + 2 ^ 64 * m.readLE (a + 8) 8 + 2 ^ 128 * m.readLE (a + 16) 8 + 2 ^ 192 * m.readLE (a + 24) 8 +
      2 ^ 256 * m.readLE (a + 32) 8 + 2 ^ 320 * m.readLE (a + 40) 8 + 2 ^ 384 * m.readLE (a + 48) 8 + 2 ^ 448 * m.readLE (a + 56) 8 := by
  rw [show 64 = 32 + 32 from rfl, Janus.Arm64.Memory.readLE_add, Fv256.Util.readLE_32, Fv256.Util.readLE_32 m (a + 32)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  omega

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 200000 in
theorem reduce4_machine (s : State) (hpc : s.rip = BitVec.ofNat 64 r4Entry) (hpre : R4Pre s) :
    ReachesRet Fv256.ReduceProg.program (retAddrOf s) s (R4Post s) := by
  have hpre0 := hpre
  obtain ⟨⟨hra1, hra2⟩, hsp, hg, ⟨hlow, hnw, hacc⟩, ⟨hzw, hz⟩, ⟨hxw, hx⟩, ⟨hmw, hm⟩, ⟨hux, hu⟩, hdz, hdx, hdm, hdu, hdg, hm3, hmu⟩ := hpre0
  refine Fv256.SegCompose.seg_trans (segA s hpc hpre) ?_
  intro S1 hpc1 hA
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, x1cdrax, x1cdrdx, x1cdrsi, x1cdrdi, x1cdr8, x1cdr9, x1cdr10, x1cdr11, x1cdr13, x1cdr15, x1cdm0, x1cdm8, x1cdm10, x1cdm18, x1cdm20, x1cdm28, x1cdm40, x1cdm48, x1cdm50, x1cdm58, x1cdm60, x1cdm68, x1cdm70, x1cdm78, x1cdm80, x1cdm88, x1cdm90, x1cdm98, x1cdma0, x1cdma8, x1cdmb0, x1cdmb8, x1cdmc0, x1cdmc8, x1cdmd0, x1cdmd8, x1cdme0, x1cdme8, x1cdmf0, x1cdmf8, x1cdm100, x1cdm108, x1cdm110, x1cdm128, hh⟩ := linkA s S1 hA
  obtain ⟨hL, hR1, hM1, hLE⟩ := hh
  obtain ⟨hxeq, hveq⟩ := hLE
  obtain ⟨hx_x1cdrax, hx_x1cdrdx, hx_x1cdrsi, hx_x1cdrdi, hx_x1cdr8, hx_x1cdr9, hx_x1cdr10, hx_x1cdr11, hx_x1cdr13, hx_x1cdr15, hx_x1cdm0, hx_x1cdm8, hx_x1cdm10, hx_x1cdm18, hx_x1cdm20, hx_x1cdm28, hx_x1cdm40, hx_x1cdm48, hx_x1cdm50, hx_x1cdm58, hx_x1cdm60, hx_x1cdm68, hx_x1cdm70, hx_x1cdm78, hx_x1cdm80, hx_x1cdm88, hx_x1cdm90, hx_x1cdm98, hx_x1cdma0, hx_x1cdma8, hx_x1cdmb0, hx_x1cdmb8, hx_x1cdmc0, hx_x1cdmc8, hx_x1cdmd0, hx_x1cdmd8, hx_x1cdme0, hx_x1cdme8, hx_x1cdmf0, hx_x1cdmf8, hx_x1cdm100, hx_x1cdm108, hx_x1cdm110, hx_x1cdm128⟩ := hxeq
  obtain ⟨hv_v0, hv_v1, hv_v2, hv_v3, hv_v4, hv_v5, hv_v6, hv_v7, hv_v8, hv_v9, hv_v10, hv_v11, hv_v12, hv_v13, hv_v14, hv_v15, hv_v16, hv_v17, hv_v18, hv_v19, hv_v20, hv_v21, hv_v22, hv_v23, hv_v24, hv_v25, hv_v26, hv_v27, hv_v28, hv_v29, hv_v30, hv_v31, hv_v32, hv_v33, hv_v34, hv_v35, hv_v36, hv_v37, hv_v38, hv_v39, hv_v40, hv_v41, hv_v42, hv_v43, hv_v44, hv_v45, hv_v46⟩ := hveq
  refine Fv256.SegCompose.seg_trans (c_1cd_4ac s S1 hpc1 hpre hR1 hM1 x1cdrax x1cdrdx x1cdrsi x1cdrdi x1cdr8 x1cdr9 x1cdr10 x1cdr11 x1cdr13 x1cdr15 x1cdm0 x1cdm8 x1cdm10 x1cdm18 x1cdm20 x1cdm28 x1cdm40 x1cdm48 x1cdm50 x1cdm58 x1cdm60 x1cdm68 x1cdm70 x1cdm78 x1cdm80 x1cdm88 x1cdm90 x1cdm98 x1cdma0 x1cdma8 x1cdmb0 x1cdmb8 x1cdmc0 x1cdmc8 x1cdmd0 x1cdmd8 x1cdme0 x1cdme8 x1cdmf0 x1cdmf8 x1cdm100 x1cdm108 x1cdm110 x1cdm128 hL) ?_
  intro S2 hpc2 hq
  unfold PC_1cd_4ac at hq
  obtain ⟨x1d9r13, x1d9r15, x1f2rcx, x1f2r13, x1f2r15, x20crcx, x20cr12, x20cr13, x236rcx, x236r12, x236r13, x236r15, x25brbx, x25br12, x25br13, x25br15, x290rcx, x290rbx, x290r12, x290r13, x290r15, x2b5rcx, x2b5rbx, x2b5r11, x2b5r13, x2b5r15, x2e0rcx, x2e0rbx, x2e0rsi, x2e0r8, x2e0r9, x2f8rax, x2f8rcx, x2f8rdx, x2f8r8, x2f8r10, x33erax, x33erbx, x33ersi, x33er9, x33er11, x33er12, x33er13, x33er15, x33em20, x33em28, x38bm30, x38bme8, x38bmf0, x38bmf8, x38bm100, x38bm108, x38bm110, x3earax, x3earcx, x3eardx, x3earbx, x3earsi, x3ear8, x3eamc8, x3eamd0, x3eamd8, x3eame0, x429r10, x429r11, x429r13, x46brcx, x46br9, x46br11, x46br13, x47frax, x47frsi, x47fr8, x47fr11, x4acrcx, x4acrdx, x4acrbx, x4acrsi, x4acr8, x4acr9, hq2⟩ := hq
  obtain ⟨hLz, hEz, hRz, hMz⟩ := hq2
  obtain ⟨h_x1d9r13, h_x1d9r15, h_x1f2rcx, h_x1f2r13, h_x1f2r15, h_x20crcx, h_x20cr12, h_x20cr13, h_x236rcx, h_x236r12, h_x236r13, h_x236r15, h_x25brbx, h_x25br12, h_x25br13, h_x25br15, h_x290rcx, h_x290rbx, h_x290r12, h_x290r13, h_x290r15, h_x2b5rcx, h_x2b5rbx, h_x2b5r11, h_x2b5r13, h_x2b5r15, h_x2e0rcx, h_x2e0rbx, h_x2e0rsi, h_x2e0r8, h_x2e0r9, h_x2f8rax, h_x2f8rcx, h_x2f8rdx, h_x2f8r8, h_x2f8r10, h_x33erax, h_x33erbx, h_x33ersi, h_x33er9, h_x33er11, h_x33er12, h_x33er13, h_x33er15, h_x33em20, h_x33em28, h_x38bm30, h_x38bme8, h_x38bmf0, h_x38bmf8, h_x38bm100, h_x38bm108, h_x38bm110, h_x3earax, h_x3earcx, h_x3eardx, h_x3earbx, h_x3earsi, h_x3ear8, h_x3eamc8, h_x3eamd0, h_x3eamd8, h_x3eame0, h_x429r10, h_x429r11, h_x429r13, h_x46brcx, h_x46br9, h_x46br11, h_x46br13, h_x47frax, h_x47frsi, h_x47fr8, h_x47fr11, h_x4acrcx, h_x4acrdx, h_x4acrbx, h_x4acrsi, h_x4acr8, h_x4acr9⟩ := hEz
  have hz : x1cdm128 = (s.regs 0).toNat := by rw [hx_x1cdm128, hv_v13]; exact Nat.mod_eq_of_lt (s.regs 0).isLt
  refine Fv256.SegCompose.seg_trans (branch s hpre S2 hpc2 hRz hMz x4acrcx x4acrdx x4acrbx x4acrsi x1cdrdi x4acr8 x4acr9 x47fr11 x33er12 x1cdm60 x1cdm68 x1cdm128 hLz hz) ?_
  intro S3 hpc3 hb
  obtain ⟨d0, d1, d2, d3, d4, hTI, hdsum⟩ := hb
  have hM3 : 1 ≤ (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) := Nat.one_le_iff_ne_zero.mpr hm3
  have hRW : Fv256.F.RecipWeak ((s.mem.readLE (BitVec.toNat (s.regs 1)) 8) + 18446744073709551616 * (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8) + 340282366920938463463374607431768211456 * (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8) + 6277101735386680763835789423207666416102355444464034512896 * (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8)) ((s.mem.readLE (BitVec.toNat (s.regs 7)) 8) + 18446744073709551616 * (s.mem.readLE (BitVec.toNat (s.regs 7) + 8) 8) + 340282366920938463463374607431768211456 * (s.mem.readLE (BitVec.toNat (s.regs 7) + 16) 8) + 6277101735386680763835789423207666416102355444464034512896 * (s.mem.readLE (BitVec.toNat (s.regs 7) + 24) 8) + 115792089237316195423570985008687907853269984665640564039457584007913129639936 * (s.mem.readLE (BitVec.toNat (s.regs 7) + 32) 8)) := by
    have := hmu
    rw [Fv256.Util.readLE_32, readLE_40'] at this
    exact this
  have harith := reduce4_arith (s.mem.readLE (BitVec.toNat (s.regs 3)) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 8) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 24) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 32) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 40) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 48) 8) (s.mem.readLE (BitVec.toNat (s.regs 3) + 56) 8) (s.mem.readLE (BitVec.toNat (s.regs 7)) 8) (s.mem.readLE (BitVec.toNat (s.regs 7) + 8) 8) (s.mem.readLE (BitVec.toNat (s.regs 7) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 7) + 24) 8) (s.mem.readLE (BitVec.toNat (s.regs 7) + 32) 8) (s.mem.readLE (BitVec.toNat (s.regs 1)) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 8) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 16) 8) (s.mem.readLE (BitVec.toNat (s.regs 1) + 24) 8) (BitVec.toNat (s.regs 0)) v0 v2 v4 v5 v6 v7 v8 v9 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 x1cdrax x1cdrdx x1cdrsi x1cdrdi x1cdr8 x1cdr9 x1cdr10 x1cdr11 x1cdr13 x1cdr15 x1cdm0 x1cdm8 x1cdm10 x1cdm18 x1cdm20 x1cdm28 x1cdm40 x1cdm48 x1cdm50 x1cdm58 x1cdm60 x1cdm68 x1cdm70 x1cdm78 x1cdm80 x1cdm88 x1cdm90 x1cdm98 x1cdma0 x1cdma8 x1cdmb0 x1cdmb8 x1cdmc0 x1cdmc8 x1cdmd0 x1cdmd8 x1cdme0 x1cdme8 x1cdmf0 x1cdmf8 x1cdm100 x1cdm108 x1cdm110 x1cdm128 x1d9r13 x1d9r15 x1f2rcx x1f2r13 x1f2r15 x20crcx x20cr12 x20cr13 x236rcx x236r12 x236r13 x236r15 x25brbx x25br12 x25br13 x25br15 x290rcx x290rbx x290r12 x290r13 x290r15 x2b5rcx x2b5rbx x2b5r11 x2b5r13 x2b5r15 x2e0rcx x2e0rbx x2e0rsi x2e0r8 x2e0r9 x2f8rax x2f8rcx x2f8rdx x2f8r8 x2f8r10 x33erax x33erbx x33ersi x33er9 x33er11 x33er12 x33er13 x33er15 x33em20 x33em28 x38bm30 x38bme8 x38bmf0 x38bmf8 x38bm100 x38bm108 x38bm110 x3earax x3earcx x3eardx x3earbx x3earsi x3ear8 x3eamc8 x3eamd0 x3eamd8 x3eame0 x429r10 x429r11 x429r13 x46brcx x46br9 x46br11 x46br13 x47frax x47frsi x47fr8 x47fr11 x4acrcx x4acrdx x4acrbx x4acrsi x4acr8 x4acr9 d0 d1 d2 d3 d4 (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) (Util.readLE8_lt s.mem _) hM3 hRW hv_v0 hv_v2 hv_v4 hv_v5 hv_v6 hv_v7 hv_v8 hv_v9 hv_v11 hv_v12 hv_v13 hv_v14 hv_v15 hv_v16 hv_v17 hv_v18 hv_v19 hv_v20 hv_v21 hv_v22 hv_v23 hv_v24 hv_v25 hv_v26 hv_v27 hv_v28 hv_v29 hv_v30 hv_v31 hv_v32 hv_v33 hv_v34 hv_v35 hv_v36 hv_v37 hv_v38 hv_v39 hv_v40 hv_v41 hv_v42 hv_v43 hv_v44 hv_v45 hv_v46 hx_x1cdrax hx_x1cdrdx hx_x1cdrsi hx_x1cdrdi hx_x1cdr8 hx_x1cdr9 hx_x1cdr10 hx_x1cdr11 hx_x1cdr13 hx_x1cdr15 hx_x1cdm0 hx_x1cdm8 hx_x1cdm10 hx_x1cdm18 hx_x1cdm20 hx_x1cdm28 hx_x1cdm40 hx_x1cdm48 hx_x1cdm50 hx_x1cdm58 hx_x1cdm60 hx_x1cdm68 hx_x1cdm70 hx_x1cdm78 hx_x1cdm80 hx_x1cdm88 hx_x1cdm90 hx_x1cdm98 hx_x1cdma0 hx_x1cdma8 hx_x1cdmb0 hx_x1cdmb8 hx_x1cdmc0 hx_x1cdmc8 hx_x1cdmd0 hx_x1cdmd8 hx_x1cdme0 hx_x1cdme8 hx_x1cdmf0 hx_x1cdmf8 hx_x1cdm100 hx_x1cdm108 hx_x1cdm110 hx_x1cdm128 h_x1d9r13 h_x1d9r15 h_x1f2rcx h_x1f2r13 h_x1f2r15 h_x20crcx h_x20cr12 h_x20cr13 h_x236rcx h_x236r12 h_x236r13 h_x236r15 h_x25brbx h_x25br12 h_x25br13 h_x25br15 h_x290rcx h_x290rbx h_x290r12 h_x290r13 h_x290r15 h_x2b5rcx h_x2b5rbx h_x2b5r11 h_x2b5r13 h_x2b5r15 h_x2e0rcx h_x2e0rbx h_x2e0rsi h_x2e0r8 h_x2e0r9 h_x2f8rax h_x2f8rcx h_x2f8rdx h_x2f8r8 h_x2f8r10 h_x33erax h_x33erbx h_x33ersi h_x33er9 h_x33er11 h_x33er12 h_x33er13 h_x33er15 h_x33em20 h_x33em28 h_x38bm30 h_x38bme8 h_x38bmf0 h_x38bmf8 h_x38bm100 h_x38bm108 h_x38bm110 h_x3earax h_x3earcx h_x3eardx h_x3earbx h_x3earsi h_x3ear8 h_x3eamc8 h_x3eamd0 h_x3eamd8 h_x3eame0 h_x429r10 h_x429r11 h_x429r13 h_x46brcx h_x46br9 h_x46br11 h_x46br13 h_x47frax h_x47frsi h_x47fr8 h_x47fr11 h_x4acrcx h_x4acrdx h_x4acrbx h_x4acrsi h_x4acr8 h_x4acr9 hdsum
  have hpos : 0 < x1cdm60 + 2 ^ 64 * x1cdm68 + 2 ^ 128 * x33er12 + 2 ^ 192 * x1cdrdi := by
    have h3 : 1 ≤ x1cdrdi := by
      have := harith.1
      omega
    omega
  refine Fv256.SegCompose.seg_mono (tail4 s hpre _ d0 d1 d2 d3 d4 x1cdm60 x1cdm68 x33er12 x1cdrdi S3 rfl hpos hTI) ?_
  intro S' h
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := h
  refine ⟨a1, a2, a3, a4, a5, a6, a7, ?_, a9⟩
  rw [a8, readLE_64', Fv256.Util.readLE_32]
  have h2 := harith.2
  rw [harith.1] at h2
  rw [harith.1]
  exact h2

end Fv256.Amd64.R4Seg
