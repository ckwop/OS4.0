#!/bin/sh
# Boot the OS on a TAP device and ping it from this container: the milestone 6
# acceptance test, with the real ping command. The container needs
#   docker run --cap-add NET_ADMIN --device /dev/net/tun ...
# Usage: tools/ping-check.sh "<qemu command using -netdev tap,ifname=tap0>"
set -eu

sh "$(dirname "$0")/tap-up.sh"
trap 'ip link del tap0 2>/dev/null || true' EXIT

console=$(mktemp)
mkfifo "$console.in"
sh -c "$1" < "$console.in" > "$console" 2>&1 &
qemu=$!
exec 3> "$console.in"                    # hold the console's input open

i=0
until grep -q "OS 4.0" "$console"; do
  i=$((i + 1)); [ "$i" -lt 120 ] || { echo "no banner"; cat "$console"; exit 1; }
  sleep 1
done

ping -c 3 -W 2 10.0.2.15 && result=0 || result=$?

printf 'bye\r' >&3
wait "$qemu" || true
exit "$result"
