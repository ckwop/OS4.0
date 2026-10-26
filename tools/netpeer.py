#!/usr/bin/env python3
"""A host on a network test's private LAN: 10.0.2.2, MAC 52:55:0a:00:02:02.

Exchanges raw Ethernet frames with the OS as UDP datagrams on 127.0.0.1, one
frame per datagram: the format of QEMU's "dgram" network backend and of the
hosted build's network HAL. It answers ARP requests and pings for its own
address throughout, and runs a script against the OS at 10.0.2.15, printing
what it finds. It runs until terminated.

Usage: netpeer.py --port PORT --os-port PORT SCRIPT
Scripts:
  ping   ARP for the OS, then ping it three times and check each reply
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
        self.ident = 0x7E57
        threading.Thread(target=self.receive, daemon=True).start()

    def send(self, dst_mac, eth_type, payload):
        self.sock.sendto(dst_mac + PEER_MAC + struct.pack("!H", eth_type) + payload, self.os_addr)

    def send_ip(self, protocol, payload):
        header = struct.pack("!BBHHHBBH4s4s", 0x45, 0, 20 + len(payload), 1, 0, 64,
                             protocol, 0, PEER_IP, OS_IP)
        header = header[:10] + struct.pack("!H", checksum(header)) + header[12:]
        self.send(self.os_mac, ETH_IP, header + payload)

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
    p.add_argument("script", choices=["ping"])
    args = p.parse_args()
    peer = Peer(args.port, args.os_port)
    getattr(peer, "script_" + args.script)()
    while True:                     # keep answering until terminated
        time.sleep(1)


if __name__ == "__main__":
    sys.exit(main())
