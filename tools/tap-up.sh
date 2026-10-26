#!/bin/sh
# Create tap0 as 10.0.2.2/24, the host side of the OS's network, unless it
# exists. The container needs: docker run --cap-add NET_ADMIN --device /dev/net/tun
set -eu
ip link show tap0 >/dev/null 2>&1 && exit 0
ip tuntap add tap0 mode tap
ip addr add 10.0.2.2/24 dev tap0
ip link set tap0 up
