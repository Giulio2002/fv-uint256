# NOTES-B7 (SPEC-B7 progress; deleted at merge)
Batch: Bytes Bytes20 Bytes32 PaddedBytes PutUint256 WriteToArray20 WriteToArray32 WriteToSlice HashTreeRoot FromBig MustFromBig SetFromBig
ToBig IntoBig CmpBig MarshalSSZ MarshalSSZAppend MarshalSSZInto SizeSSZ UnmarshalSSZ EncodeRLP Value.
Tooling (outside repo): /srv/janus-ops/spec-b7/{gen.py,rows.py,verify.sh,equiv/} -- gen.py reads OLD statement from git 4e3e1be7, writes
lean/Fv256/<Isa>/<Fn>.lean (claim), lean/Fv256/Proofs/<Isa>/<Fn>Bridge.lean (post_iff : OLD_POST <-> NEW_POST), renames correctness->correctness_proof,
Witness->Wit in the proof module, and writes equiv/Equiv<Isa><Fn>.lean. Row data in rows.py. Verify: /srv/janus-ops/spec-b7/verify.sh <tag> <isa|both> Fn...
Shared lemma modules: Proofs/Common/BytesBridge.lean (fromBE/readLE <-> beBytes/leBytes), Proofs/Common/BigBridge.lean (big.Int).
Pure specs: Spec/{BigEndian,BigInt,Bytes32,Bytes20,Bytes,PaddedBytes,PutUint256,WriteToArray20/32,WriteToSlice,HashTreeRoot,SizeSSZ,MarshalSSZ,SetFromBig,CmpBig,FromBig,MustFromBig}.lean
Core.lean edit: removed sizeSSZ (now Spec/SizeSSZ.lean), added import.
DON'T edit a module imported by a running verify (log-<tag>.txt) -- source hashes are checked.
Status: see git log + /srv/janus-ops/spec-b7/log-*.txt

## FINAL (SPEC-B7b)
All 22 fns x 2 ISAs converted; verify PASS (t2/t3/t4/t5 logs in /srv/janus-ops/spec-b7); 44/44 equivalence checks PASS (equiv-ea/eb.marks);
check-spec-closure OK (44 rows); make build OK; lint_source OK (whitelist hash WARNs only). IntoBig converted via generator edits (no TB/FM output change).
