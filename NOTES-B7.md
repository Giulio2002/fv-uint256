# NOTES-B7 (FV-B7, arm64 SetFromDecimal: fromDecimal loop + top level) -- worktree /srv/fv-uint256-wB7, branch fv/wb7 (off fv/wi4 75df2ff)

Split agreed with FV-I4 (a6fa3045cf5aa5e10): FV-I4 keeps te_sum0/te_sum1/te_sum/pw_sum (Arm64/SfdPw.lean, PwSum hypothesis);
I own NEW files Arm64/SfdFd*.lean (fromDecimal loop), Arm64/SfdTop*.lean (SetFromDecimal top, then Extracted correctness + witness).
Build: lean/ lakefile pinned to /srv/janus-fvA-pin655 @655a23fa; build with ../build_lb.sh <Module> (lake build, log build/lb-<Module>.log, ENDMARK).

## Done
- lean/Fv256/SfdFdMath.lean, SfdFdLem.lean: copied verbatim from /srv/fv-uint256-wi (FV-I2, ISA independent; untracked there; identical content merges).
- Arm64/SfdFdSpec.lean: FdPre/FdPost/FdSum statement (arm64 analogue of amd64 SfdFd): mulTab = 0x1b6540 (multipliers),
  ioEOF = 0x1b5c10, frame 160 bytes, window lo+4440 <= SP, SP+32 <= hi, GuardOK s 32.

## arm64 fromDecimal facts (fd = 0xb8b50; go tool objdump of harness-arm64; listing in `go tool objdump -s 'uint256.\(\*Int\).fromDecimal$'`)
- entry: stack check (16(R28) vs SP-32), frame 160 (pre-index store of x30 at SP-160, x29 at SP-8 rel. new SP...), spill pS to 176(SP'), zero z (2 STP), CBZ nS -> EOF path (0xb8bc0: LDP io.EOF -> R0,R1, ret).
- else: z -> 168(SP'), pS -> 176(SP'), copy multipliers (40 bytes at 0x1b6540) to 112..152(SP'); R3 = i = 0, R4 = len = nS; JMP head.
- HEAD = fd + 0x9c (0xb8bec): R0 = z, R1 = pS, R2 = remaining (signed, nS-19i), R3 = i, R4 = len(bs) (= R2 whenever R2 > 0), exit by
  CMP $5,R3 BGE -> return nil (0xb8d40), CMP $0,R2 BLE -> return nil (0xb8d2c).
- round: spill i->56, mult[i]->104, len->64, rem->48 (all SP'-relative). rem>19: bounds check rem<=len, ParseUint(pS+rem-19, 19, 10, 64); else ParseUint(pS, len,..).
  After: CBNZ R1 (err itab) -> return (R0,R1)=(R1,R2) of ParseUint (0xb8d18). i==0: store (num,0,0,0) to z; else tmp Int at 72(SP') = {num,0,0,0}, Mul(tmp,tmp,mult[i]) (R0=R1=tmp, R2=W),
  then z += *R0 (ADDS/ADCS x4 at 0xb8ca4..0xb8cec), then loop increment at 0xb8bd8 (R3 = i+1, R2 = rem-19), chop bs (bounds check len >= rem-19 at 0xb8d04, BCS back).
- SetFromDecimal (sfd = 0xb89b0): '+' skip, zero-skip loop with runtime.decoderune for bytes >= 0x80 (at 0xb8ab8..), len compare vs 78 with runtime.cmpstring against the
  digits of 2^256-1 (rodata at ADRP+2315), error return LDP from 0x1b5bc0-ish, then call fromDecimal (0xb8a70 / 0xb8a98).

## TODO (in order)
1. compile SfdFdSpec (lake build Fv256.Arm64.SfdFdSpec), commit.
2. FdInv at HEAD, fd_next / fd_round (call PwSum via ReachesRet.call, Mul via mul_sum, inline add, bounds checks), prologue, exits; amd64 SfdFdLoop.lean (FV-I2) is the template but is itself unfinished (ends in `trace_state; sorry`).
3. SfdTop: plus skip, zero loop (decoderune_sum), cmpstring contract, call fd_sum; Extracted correctness + Witness.nonvacuous; ONE verify.
