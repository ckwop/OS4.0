#!/bin/sh
# Feed each <dir>/*.in to a Forth system on stdin and diff its output against <dir>/*.out.
# If <dir>/<name>.filter exists, it is a sed script applied to the output first,
# to mask values that change from build to build (such as code addresses).
# Usage: tools/run-tests.sh "<command that runs Forth, reading stdin>" [dir ...]
set -u

cmd=$1
shift
[ $# -gt 0 ] || set -- tests
timeout_secs=${TEST_TIMEOUT:-10}
pass=0
fail=0

for dir in "$@"; do
  for input in "$dir"/*.in; do
    [ -e "$input" ] || continue
    name=${input%.in}
    timeout "$timeout_secs" $cmd < "$input" > "$name.actual" 2>&1
    if [ -e "$name.filter" ]; then
      sed -i -f "$name.filter" "$name.actual"
    fi
    if diff -u "$name.out" "$name.actual"; then
      pass=$((pass + 1))
    else
      fail=$((fail + 1))
      echo "FAIL: $name"
    fi
  done
done

echo "$pass passed, $fail failed"
[ "$fail" -eq 0 ]
