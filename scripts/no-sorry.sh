#!/usr/bin/env bash
# Fails if any .lean file under lean/Fv256 contains the token `sorry` (outside `--` comments), except files listed in
# WIP-SORRY.txt (format: path<TAB>owner<TAB>note). The allowlist MUST be empty at the final release (RELEASE=1 enforces it).
# Run before every merge:  scripts/no-sorry.sh
set -uo pipefail
root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"; cd "$root"
allow="WIP-SORRY.txt"
[ -f "$allow" ] || { echo "missing $allow"; exit 2; }
declare -A ok=()
nok=0
while IFS=$'\t' read -r path owner note; do
  case "$path" in ''|\#*) continue;; esac
  [ -n "$owner" ] || { echo "FAIL: $allow entry '$path' has no owner"; exit 1; }
  [ -f "$path" ] || { echo "FAIL: $allow lists missing file $path"; exit 1; }
  ok["$path"]=1; nok=$((nok+1))
done < "$allow"
if [ -n "${RELEASE:-}" ] && [ "$nok" -gt 0 ]; then echo "FAIL (RELEASE): $allow is not empty ($nok entries)"; exit 1; fi
fail=0
while IFS= read -r f; do
  # (not `grep -q` in a pipe: with pipefail an early-exiting grep SIGPIPEs sed and the test would falsely say 'no sorry' on big files)
  if [ "$(sed 's/--.*$//' "$f" | grep -cw 'sorry')" -gt 0 ]; then
    if [ -n "${ok[$f]+x}" ]; then echo "allowed (WIP): $f"; else echo "FAIL: sorry in $f (not in $allow)"; fail=1; fi
  elif [ -n "${ok[$f]+x}" ]; then echo "note: $f is in $allow but no longer contains sorry (remove it)"; fi
done < <(find lean/Fv256 -name '*.lean' | sort)
[ $fail = 0 ] && echo "no-sorry: OK" || echo "no-sorry: FAILED"
exit $fail
