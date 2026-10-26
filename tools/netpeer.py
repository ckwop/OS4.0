#!/usr/bin/env python3
"""A host on a network test's private LAN: 10.0.2.2, MAC 52:55:0a:00:02:02.

Exchanges raw Ethernet frames with the OS as UDP datagrams on 127.0.0.1, one
frame per datagram: the format of QEMU's "dgram" network backend and of the
hosted build's network HAL. It answers ARP requests and pings for its own
address throughout, and runs a script against the OS at 10.0.2.15, printing
what it finds. It runs until terminated.

It also runs a UDP echo service on its port 7.

Usage: netpeer.py --port PORT --os-port PORT SCRIPT
Scripts:
  ping   ARP for the OS, then ping it three times and check each reply
  udp    use the OS's UDP echo service (port 7) with several sizes, with and
         without a checksum, then send to a closed port (9) and expect ICMP
         port unreachable
"""

import argparse
import queue
import socket
import struct
import sys
import threading
import time

PEER_MAC = bytes.fromhex("52550a000202")
PEER_IP = bytes([10, 0, 2, 2])
OS_IP = bytes([10, 0, 2, 15])
BROADCAST = b"\xff" * 6
ETH_IP, ETH_ARP = 0x0800, 0x0806


def checksum(data):
    if len(data) % 2:
        data += b"\0"
    total = sum(struct.unpack(f"!{len(data) // 2}H", data))
    while total >> 16:
        total = (total & 0xFFFF) + (total >> 16)
    return ~total & 0xFFFF


def ip_text(addr):
    return ".".join(str(b) for b in addr)


def mac_text(mac):
    return ":".join(f"{b:02x}" for b in mac)


class Peer:
    def __init__(self, port, os_port):
        self.sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        self.sock.bind(("127.0.0.1", port))
        self.os_addr = ("127.0.0.1", os_port)
        self.os_mac = None
        self.arp_replies = queue.Queue()
        self.echo_replies = queue.Queue()
        self.udp_replies = queue.Queue()
        self.unreachables = queue.Queue()
        self.ident = 0x7E57
        threading.Thread(target=self.receive, daemon=True).start()

    def send(self, dst_mac, eth_type, payload):
        self.sock.sendto(dst_mac + PEER_MAC + struct.pack("!H", eth_type) + payload, self.os_addr)

    def send_ip(self, protocol, payload):
        header = struct.pack("!BBHHHBBH4s4s", 0x45, 0, 20 + len(payload), 1, 0, 64,
                             protocol, 0, PEER_IP, OS_IP)
        header = header[:10] + struct.pack("!H", checksum(header)) + header[12:]
        self.send(self.os_mac, ETH_IP, header + payload)

    def udp_segment(self, sport, dport, data, src=PEER_IP, dst=OS_IP, with_checksum=True):
        segment = struct.pack("!HHHH", sport, dport, 8 + len(data), 0) + data
        if with_checksum:
            pseudo = src + dst + struct.pack("!BBH", 0, 17, len(segment))
            value = checksum(pseudo + segment) or 0xFFFF
            segment = segment[:6] + struct.pack("!H", value) + segment[8:]
        return segment

    def arp(self, oper, target_mac, target_ip):
        return struct.pack("!HHBBH6s4s6s4s", 1, ETH_IP, 6, 4, oper,
                           PEER_MAC, PEER_IP, target_mac, target_ip)

    def receive(self):
        while True:
            frame = self.sock.recv(4096)
            src, eth_type, body = frame[6:12], struct.unpack("!H", frame[12:14])[0], frame[14:]
            if eth_type == ETH_ARP and len(body) >= 28:
                oper, sha, spa, tpa = struct.unpack("!6xH6s4s6x4s", body[:28])
                if tpa != PEER_IP:
                    continue
                if oper == 1:
                    self.send(sha, ETH_ARP, self.arp(2, sha, spa))
                elif oper == 2:
                    self.arp_replies.put((sha, spa))
            elif eth_type == ETH_IP and len(body) >= 20:
                ihl = (body[0] & 15) * 4
                total = struct.unpack("!H", body[2:4])[0]
                protocol, dst = body[9], body[16:20]
                if dst != PEER_IP:
                    continue
                packet, message = body[:total], body[ihl:total]
                if protocol == 1 and message[0] == 8:          # echo request: answer it
                    self.os_mac = self.os_mac or src
                    reply = b"\0\0\0\0" + message[4:]
                    reply = reply[:2] + struct.pack("!H", checksum(reply)) + reply[4:]
                    self.send_ip(1, reply)
                elif protocol == 1 and message[0] == 0:        # echo reply: for the script
                    self.echo_replies.put((packet, ihl, message))
                elif protocol == 1 and message[0] == 3:        # destination unreachable
                    self.unreachables.put((packet, ihl, message))
                elif protocol == 17 and len(message) >= 8:
                    sport, dport = struct.unpack("!HH", message[:4])
                    if dport == 7:                             # our echo service
                        self.os_mac = self.os_mac or src
                        self.send_ip(17, self.udp_segment(7, sport, message[8:]))
                    else:
                        self.udp_replies.put((packet, ihl, message))

    def find_os(self):
        deadline = time.time() + 20
        while self.os_mac is None and time.time() < deadline:
            self.send(BROADCAST, ETH_ARP, self.arp(1, b"\0" * 6, OS_IP))
            try:
                sha, spa = self.arp_replies.get(timeout=1)
                if spa == OS_IP:
                    self.os_mac = sha
            except queue.Empty:
                pass
        return self.os_mac is not None

    def script_udp(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)                       # let the console start the echo service
        cases = [(0, True), (1, True), (100, True), (1472, True), (37, False)]
        for size, with_checksum in cases:
            data = bytes((i * 7 + size) & 255 for i in range(size))
            self.send_ip(17, self.udp_segment(40000, 7, data, with_checksum=with_checksum))
            label = f"udp echo of {size} bytes" + ("" if with_checksum else ", no checksum")
            try:
                packet, ihl, message = self.udp_replies.get(timeout=5)
            except queue.Empty:
                print(f"peer: {label}: no reply", flush=True)
                continue
            problems = []
            if checksum(packet[:ihl]):
                problems.append("bad IP checksum")
            sport, dport, length, csum = struct.unpack("!HHHH", message[:8])
            pseudo = packet[12:16] + packet[16:20] + struct.pack("!BBH", 0, 17, length)
            if csum and checksum(pseudo + message[:length]):
                problems.append("bad UDP checksum")
            if not csum:
                problems.append("no UDP checksum")
            if (sport, dport) != (7, 40000):
                problems.append(f"ports {sport}->{dport}")
            if message[8:length] != data:
                problems.append("wrong data")
            print(f"peer: {label}: {', '.join(problems) or 'ok'}", flush=True)

        burst = 48                          # more than one poll's worth with 8 receive buffers
        for i in range(burst):
            self.send_ip(17, self.udp_segment(40002, 7, f"burst {i}".encode()))
        echoed = set()
        deadline = time.time() + 10
        while len(echoed) < burst and time.time() < deadline:
            try:
                packet, ihl, message = self.udp_replies.get(timeout=1)
            except queue.Empty:
                continue
            if struct.unpack("!H", message[2:4])[0] == 40002:
                echoed.add(message[8:])
        print(f"peer: udp burst of {burst} datagrams: {len(echoed)} echoed", flush=True)

        self.send_ip(17, self.udp_segment(40001, 9, b"anyone there?"))
        deadline = time.time() + 5
        while True:                         # skip reports about other datagrams
            try:
                packet, ihl, message = self.unreachables.get(timeout=max(0.1, deadline - time.time()))
            except queue.Empty:
                print("peer: udp to closed port 9: no ICMP reply", flush=True)
                break
            quoted = message[8:]
            qihl = (quoted[0] & 15) * 4
            sport, dport = struct.unpack("!HH", quoted[qihl:qihl + 4])
            if sport != 40001:
                continue
            ok = message[1] == 3 and not checksum(message) and dport == 9
            print(f"peer: udp to closed port 9: ICMP port unreachable "
                  f"{'ok' if ok else f'wrong: code {message[1]}, port {dport}'}", flush=True)
            break

    def script_ping(self):
        deadline = time.time() + 20
        while self.os_mac is None and time.time() < deadline:
            self.send(BROADCAST, ETH_ARP, self.arp(1, b"\0" * 6, OS_IP))
            try:
                sha, spa = self.arp_replies.get(timeout=1)
                if spa == OS_IP:
                    self.os_mac = sha
            except queue.Empty:
                pass
        if self.os_mac is None:
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        print(f"peer: {ip_text(OS_IP)} is at {mac_text(self.os_mac)}", flush=True)

        data = bytes(range(32))
        for seq in (1, 2, 3):
            request = struct.pack("!BBHHH", 8, 0, 0, self.ident, seq) + data
            request = request[:2] + struct.pack("!H", checksum(request)) + request[4:]
            self.send_ip(1, request)
            try:
                packet, ihl, message = self.echo_replies.get(timeout=5)
            except queue.Empty:
                print(f"peer: no echo reply {seq}", flush=True)
                continue
            problems = []
            if checksum(packet[:ihl]):
                problems.append("bad IP checksum")
            if checksum(message):
                problems.append("bad ICMP checksum")
            ident, rseq = struct.unpack("!HH", message[4:8])
            if (ident, rseq) != (self.ident, seq):
                problems.append(f"wrong id/seq {ident:#x}/{rseq}")
            if message[8:] != data:
                problems.append("wrong data")
            verdict = ", ".join(problems) or "data and checksums ok"
            print(f"peer: echo reply {seq} from {ip_text(packet[12:16])}: {verdict}", flush=True)


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--port", type=int, required=True)
    p.add_argument("--os-port", type=int, required=True)
    p.add_argument("script", choices=["ping", "udp"])
    args = p.parse_args()
    peer = Peer(args.port, args.os_port)
    getattr(peer, "script_" + args.script)()
    while True:                     # keep answering until terminated
        time.sleep(1)


if __name__ == "__main__":
    sys.exit(main())
