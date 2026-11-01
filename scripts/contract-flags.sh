# sourced by verify-all.sh and tools/v.sh: `contract_flags Fn` prints the extra `janus extract` flags a function needs
# (runtime calls that are not extracted but covered by a pinned Janus contract, or omitted unpinned callees on error paths)
contract_flags() {
  case "$1" in
    Clone|NewInt|FromBig|MustFromBig|Bytes) echo "--contract runtime.newobject";;
    MarshalSSZ) echo "--contract runtime.makeslice";;
    MarshalSSZAppend) echo "--contract runtime.growslice";;
    MarshalSSZInto|UnmarshalSSZ) echo "--contract runtime.convT64 --contract fmt.errorf --contract runtime.newobject";;
    *) echo "";;
  esac
}
