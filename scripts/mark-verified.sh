#!/usr/bin/env bash
# mark-verified.sh Fn [Fn...]  : set both ISA columns of the Fn rows in COVERAGE.md to `verified`
cd "$(dirname "$0")/.."
for f in "$@"; do
  sed -i "s#^| \`(\*uint256.Int).$f\` | [a-z-]* | [a-z-]* | .*#| \`(*uint256.Int).$f\` | verified | verified | lean/Fv256/{Arm64,Amd64}/$f.lean |#" COVERAGE.md
  sed -i "s#^| \`uint256.$f\` | [a-z-]* | [a-z-]* | .*#| \`uint256.$f\` | verified | verified | lean/Fv256/{Arm64,Amd64}/$f.lean |#" COVERAGE.md
done
