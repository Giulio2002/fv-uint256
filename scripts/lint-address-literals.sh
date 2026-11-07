#!/usr/bin/env bash
# Guard: proofs of functions that touch link-time data must not hard-code layout-dependent addresses
# (data addresses, code addresses, ADRP/RIP targets, return addresses). Such literals move whenever the harness
# binary changes (the SSZ Main proofs timed out at 5400 s that way). Take addresses symbolically:
# Extracted.dataAddr.*, Extracted.entry + k, adrpLdTarget / ripTarget of the extracted words.
# Flags a numeric literal (decimal or 0x hex) that falls inside the address range where the harness binary's text/data
# live: arm64 [0x80000, 0x200000), amd64 [0x400000, 0x600000) -- in files under */Arm64/ or */Amd64/ respectively.
# A line carrying `-- addr-ok` is exempt (deliberate witness-model addresses, checked disjoint from the data).
# usage: scripts/lint-address-literals.sh [FILE ...]   (default: all lean/Fv256/{Arm64,Amd64}/*.lean); exit 1 if flagged
cd "$(dirname "${BASH_SOURCE[0]}")/.."
files=("$@"); [ ${#files[@]} -gt 0 ] || files=(lean/Fv256/Arm64/*.lean lean/Fv256/Amd64/*.lean)
bad=0
for f in "${files[@]}"; do
  [ -f "$f" ] || continue
  case "$f" in */Arm64/*) lo=524288; hi=2097152;; */Amd64/*) lo=4194304; hi=6291456;; *) continue;; esac
  out=$(awk -v lo=$lo -v hi=$hi '
    /addr-ok/ { next }
    /^[ \t]*--/ { next }
    { line=$0
      while (match(line, /(0x[0-9a-fA-F]+|[0-9]+)/)) {
        tok=substr(line, RSTART, RLENGTH); pre=(RSTART>1)?substr(line,RSTART-1,1):" "
        line=substr(line, RSTART+RLENGTH)
        if (pre ~ /[A-Za-z_.0-9]/) continue
        v=(tok ~ /^0x/)? strtonum(tok) : tok+0
        if (v>=lo && v<hi && length(tok)>=5) print NR": "$0
      } }' "$f" | awk '!seen[$0]++' | grep -v -E 'maxHeartbeats|maxRecDepth|2 \^' || true)
  [ -n "$out" ] && { echo "== $f"; echo "$out" | cut -c1-180; bad=1; }
done
exit $bad
