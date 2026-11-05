#!/bin/bash
# print Lean errors (first 70 lines) or Verified line
f=$1
if grep -q "^Verified" $f; then grep -n "^Verified\|Axioms" $f; else sed -n '/^Lean errors/,/Stage:/p' $f | grep -v "^\s*$" | cut -c1-220 | head -${2:-30}; head -3 $f | cut -c1-250; fi
