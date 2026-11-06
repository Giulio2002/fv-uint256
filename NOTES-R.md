# EncodeRLP (FV-H2, branch fv/wr, worktree /srv/fv-uint256-wr) -- STATE 2026-11-07
Pin: /srv/janus-wr-pin = agent/icall 38396fec (closed-term keep/P allowed), lakefile rev 38396fec17595aeb499b931f5332a1cbdd57edd2, own jcache /srv/fv-uint256-wr/jcache.
Spec: lean/Fv256/RlpSpec.lean (rlpBytes, rlpVal; nil z encodes as 0 => [0x80]).
Extractions: build/ex-{amd64,arm64}-EncodeRLP (--contract runtime.newobject); amd64 581 B @0x4b3200, arm64 149 words @0xb7880, data 448 B (tyBig=base, tyOne=base+0xC0).
Statement: lean/Fv256/Amd64/EncodeRLP.lean (hyps hnew:NewobjectContract64, hw:ICallContract64 ... fn 4 stack 56 rt (fun _=>[]) R P; P pins StrOut of rlpBytes + cap=len before the call; Outside rt of frame [rsp-56-stack, rsp+32); z disjoint from spills; Outside tab+24 rt).
Frame facts: call-site SP = entry rsp - 56 (push BP 8 + sub 0x28 + CALL ret 8); spills at rsp+16 (tab), rsp+24 (w); 4 newobject sites: nil (0x4b33d3), nBits=0 (0x4b339a), nBits<=7 (0x4b335a), multi (0x4b32b8).
DONE (amd64, in workspace check build/lre.sh Amd64): z=0 path fully closes (newobject -> Write call, P proved, janus_frame). z!=0 prefix reaches 9 goals at the newobject calls with `¬z.toNat = 0` pruning.
LEARNED: (1) after a newobject return, rename_i the 16 anon hyps then InRanges.disjoint hin hout / htr, else reads of spills are stuck; (2) never use ‹InRanges ..› (minutes); (3) put RlpSpec lemmas inside the EncodeRLP file for workspace iteration (RlpSpec olean is stale); (4) ICallContract needs Extracted.program.link impl and keep a closed term on 38396fec.
TODO: z!=0 paths: per size class (nBits=0: limbs zero -> [0x80]; <=7: store CL byte, P by bytes_write1 with z[0]; multi: BSWAP stores, bytes at offset o>=1 = v/256^(32-o)%256, slice start 32-nBytes), then arm64 twin, Witness (>= multi-byte branch; toy newobject + toy Write), verify both ISAs with correctness+Witness in one run; then re-verify on batch-15 pin.
Scripts: build/vre.sh Amd64|Arm64 (verify, keeps workspace), build/lre.sh (fast check; WS path in build/ws-Amd64.txt must be updated after each fresh verify), build/ws-*.txt.

## Segmentation plan (coordinator, 2026-11-07) -- NOT yet implemented
(a) prefix: entry -> pc entry+0xa0 (join after the BSR chain; DX = nBits, SI clobbered, AX = z): one lemma, post-state facts (rax=z ptr, rdx=ofNat nb with nb = bitLen(rlpVal), rsp-48, rbp=rsp-8, stack saves, MemFrame s.mem S.mem [(rsp-48,rsp+32)]); 4 limb cases (use nibble/clz_bl lemmas as in Hex).
(b) one file per path starting from that state: nil (done inline, entry pc), nBits=0, 1<=nBits<=7, nBits>=8 (BSWAP stores). Each: newobject (hnew.pos; rename via janus_grab, never positional/‹›), then Write icall (hw), conclude via janus_frame.
(c) tiny composing file. Byte lemma (byte at offset o>=1 of the BSWAP'd object is v/256^(32-o)%256) in its own Extracted-free file. Model: /srv/fv-uint256-wB7 Arm64 SfdFd*.
Audit stub check: build/vre-audit.sh (copy of lean/ in lean-audit/ with the proof replaced by sorry); result in build/vre-audit.log.
