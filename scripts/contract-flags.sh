# sourced by verify-all.sh and tools/v.sh: `contract_flags Fn` prints the extra `janus extract` flags a function needs
# (runtime calls that are not extracted but covered by a pinned Janus contract, or omitted unpinned callees on error paths)
contract_flags() {
  case "$1" in
    Clone|NewInt|FromBig|MustFromBig|Bytes|FromHex|MustFromHex|SetFromHex) echo "--contract runtime.newobject";;
    IntoBig|ToBig) echo "--contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier2 --contract runtime.newobject";;
    DivMod) echo "--contract runtime.newobject";;
    Value) echo "--contract runtime.convTstring --contract runtime.slicebytetostring --contract runtime.growslice --contract runtime.gopanic";;
    Hex) echo "--contract runtime.slicebytetostring";;
    Dec|String|PrettyDec) echo "--contract runtime.slicebytetostring --contract runtime.growslice --contract runtime.gopanic";;
    Format) echo "--contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier2 --contract runtime.newobject --contract runtime.slicebytetostring --contract runtime.growslice --contract runtime.gopanic --contract fmt.Fprint --contract math/big.(*Int).Format --contract runtime.stringtoslicebyte --contract runtime.typeAssert";;
    MarshalSSZ|PaddedBytes) echo "--contract runtime.makeslice";;
    SetFromDecimal) echo "--contract runtime.cmpstring --contract runtime.ifaceeq --contract runtime.mallocgc --contract runtime.memmove --contract runtime.newobject --contract runtime.gcWriteBarrier1 --contract runtime.gcWriteBarrier2 --contract runtime.gcWriteBarrier3 --contract runtime.growslice --contract runtime.slicebytetostring --contract runtime.concatstring2";;
    MarshalSSZAppend) echo "--contract runtime.growslice";;
    MarshalSSZInto|UnmarshalSSZ) echo "--contract runtime.convT64 --contract fmt.errorf --contract runtime.newobject";;
    *) echo "";;
  esac
}
