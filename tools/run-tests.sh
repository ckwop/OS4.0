#!/bin/sh
# Feed each tests/*.in to a Forth system on stdin and diff its output against tests/*.out.
# Usage: tools/run-tests.sh "<command that runs Forth, reading stdin>"
set -u

cmd=$1
timeout_secs=${TEST_TIMEOUT:-10}
pass=0
fail=0

for input in tests/*.in; do
  [ -e "$input" ] || continue
  name=${input%.in}
  timeout "$timeout_secs" $cmd < "$input" > "$name.actual" 2>&1
  if diff -u "$name.out" "$name.actual"; then
    pass=$((pass + 1))
  else
    fail=$((fail + 1))
    echo "FAIL: $name"
  fi
done

echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
