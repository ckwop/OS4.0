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
  tcp    32 clients at once of the OS's line echo server on port 5000: each
         sends ten lines, checks every echo, and closes. One drops a segment
         from the OS, one sends out of order, one's sequence numbers wrap, one sends
         all its lines in a single segment. Then a SYN to closed port 4999
         must be reset
  repl   telnet sessions with the network REPL: two sandbox sessions at once
         on port 4000, a full-Forth session on 4001, and a client that hangs
         up in the middle of a line. Prints what each session showed
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
        self.tcp_queues = {}            # our TCP port -> queue of (packet, segment)
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
                elif protocol == 6 and len(message) >= 20:
                    dport = struct.unpack("!H", message[2:4])[0]
                    q = self.tcp_queues.get(dport)
                    if q:
                        q.put((packet, message))
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

    def script_tcp(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)                       # let the console start the server
        clients = [TcpClient(self, 50000 + i, dport=5000) for i in range(32)]
        clients[0].drop_first_data = True   # the OS must resend what we "lost"
        clients[1].out_of_order = True     # the OS sees a gap, then the rest
        clients[2].iss = 0xFFFFFFF0         # sequence numbers wrap
        clients[3].batched = True           # all lines in one segment
        threads = [threading.Thread(target=c.run) for c in clients]
        for t in threads:
            t.start()
        for t in threads:
            t.join(60)
        connected = sum(c.connected for c in clients)
        echoed = sum(c.echoed for c in clients)
        closed = sum(c.closed for c in clients)
        print(f"peer: tcp: {connected} of 32 clients connected, {echoed} of 320 lines echoed, "
              f"{closed} closed cleanly", flush=True)
        for c in clients:
            for problem in c.problems:
                print(f"peer: tcp client {c.sport - 50000}: {problem}", flush=True)
        print(f"peer: tcp: OS retransmitted a dropped segment: "
              f"{'yes' if clients[0].saw_retransmit else 'no'}", flush=True)

        refused = TcpClient(self, 49999, dport=4999)
        print(f"peer: tcp to closed port 4999: {refused.expect_reset()}", flush=True)

    def script_repl(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)
        a, b = TcpClient(self, 51000, dport=4000), TcpClient(self, 51001, dport=4000)
        admin = TcpClient(self, 51002, dport=4001)
        quitter = TcpClient(self, 51003, dport=4000)
        sessions = [("sandbox A", a), ("sandbox B", b), ("full Forth", admin), ("hang-up", quitter)]
        for _, c in sessions[:2]:
            if c.connect():
                c.connected = True
                c.wait_for_text("leave.\r\n")
            else:
                c.problems.append("no SYN-ACK")
        steps = [(a, "2 3 + .", "ok"), (a, "hex ff .", "ok"), (b, "ff .", "?"),
                 (a, "decimal 1 2 3", "ok"), (b, ".s", "ok"), (a, ".s", "ok"),
                 (a, "here .", "?"), (a, ": sq dup * ;", "?"), (a, "words", "ok"),
                 (a, "bye", "ok"), (b, "bye", "ok")]
        for c, line, end in steps:
            if c.connected and not c.problems:
                c.send_reliably(line.encode() + b"\r\n")
                c.wait_for_text(end + "\r\n")
        if admin.connect():
            admin.wait_for_text("leave.\r\n")
            for line in [": sq dup * ; 7 sq .", "here 0<> .", "bye"]:
                admin.send_reliably(line.encode() + b"\r\n")
                admin.wait_for_text("ok\r\n")
        if quitter.connect():                   # a partial line, then hang up
            quitter.wait_for_text("leave.\r\n")
            quitter.send_reliably(b"1 2 + .")
            time.sleep(0.5)
        for _, c in sessions:
            c.wait_for(lambda: c.fin_received, 10)
            c.close()
        for name, c in sessions:
            for line in c.transcript().rstrip("\n").split("\n"):
                print(f"peer: {name}| {line}", flush=True)
            print(f"peer: {name}: {'closed' if c.closed else 'not closed'}", flush=True)
            for problem in c.problems:
                print(f"peer: {name}: {problem}", flush=True)

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


MOD32 = 1 << 32
FIN, SYN, RST, PSH, ACK = 1, 2, 4, 8, 16


class TcpClient:
    """One scripted client of the OS's line echo server: connect, send ten
    lines and check each comes back, then close. Sequence numbers are kept as
    unbounded counts and wrapped only on the wire. Retransmits go-back-N after a
    second without progress."""

    def __init__(self, peer, sport, dport=4000):
        self.peer, self.sport, self.dport = peer, sport, dport
        self.q = queue.Queue()
        peer.tcp_queues[sport] = self.q
        self.iss = (sport * 7919 * 65537) % MOD32
        self.drop_first_data = self.out_of_order = self.batched = False
        self.saw_retransmit = False
        self.connected = self.closed = False
        self.echoed = 0
        self.problems = []
        self.received = b""
        self.fin_received = False
        self.reset = False
        self.seen_seqs = set()
        self.peer_mss = None

    # ---- segments

    def send_seg(self, flags, seq, data=b"", options=b""):
        hlen = 20 + len(options)
        ack = self.rcv_nxt % MOD32 if flags & ACK else 0
        seg = struct.pack("!HHIIHHHH", self.sport, self.dport, seq % MOD32, ack,
                          (hlen // 4) << 12 | flags, 65535, 0, 0) + options + data
        pseudo = PEER_IP + OS_IP + struct.pack("!BBH", 0, 6, len(seg))
        seg = seg[:16] + struct.pack("!H", checksum(pseudo + seg)) + seg[18:]
        self.peer.send_ip(6, seg)

    def handle(self, packet, seg):
        """Take in one segment from the OS."""
        pseudo = packet[12:16] + packet[16:20] + struct.pack("!BBH", 0, 6, len(seg))
        if checksum(pseudo + seg):
            self.problems.append("bad TCP checksum")
            return
        seq, ack, off_flags, wnd = struct.unpack("!IIHH", seg[4:16])
        flags, hlen = off_flags & 0x3F, (off_flags >> 12) * 4
        data = seg[hlen:]
        if flags & RST:
            self.reset = True
            return
        if flags & ACK:
            delta = (ack - self.snd_una) % MOD32
            if delta < 1 << 31:
                self.snd_una += delta
        if flags & SYN:
            return
        if data:
            if seq in self.seen_seqs:
                self.saw_retransmit = True
            self.seen_seqs.add(seq)
            if self.drop_first_data:
                self.drop_first_data = False  # pretend it never arrived
                return
        offset = (seq - self.rcv_nxt) % MOD32
        if data and offset == 0:
            self.received += data
            self.rcv_nxt += len(data)
        if flags & FIN and (seq + len(data) - self.rcv_nxt) % MOD32 == 0 and not self.fin_received:
            self.fin_received = True
            self.rcv_nxt += 1
        if data or flags & FIN:
            self.send_seg(ACK, self.snd_nxt)

    def pump(self, timeout):
        try:
            packet, seg = self.q.get(timeout=timeout)
        except queue.Empty:
            return False
        self.handle(packet, seg)
        return True

    # ---- the script

    def connect(self):
        self.snd_una = self.snd_nxt = self.iss
        self.rcv_nxt = 0
        for _ in range(5):
            self.send_seg(SYN, self.iss, options=struct.pack("!BBH", 2, 4, 1460))
            deadline = time.time() + 1
            while time.time() < deadline:
                try:
                    packet, seg = self.q.get(timeout=max(0.01, deadline - time.time()))
                except queue.Empty:
                    break
                seq, ack, off_flags = struct.unpack("!IIH", seg[4:14])
                if off_flags & (SYN | ACK) == SYN | ACK and ack == (self.iss + 1) % MOD32:
                    hlen = (off_flags >> 12) * 4
                    if hlen >= 24 and seg[20:22] == b"\x02\x04":
                        self.peer_mss = struct.unpack("!H", seg[22:24])[0]
                    self.rcv_nxt = seq + 1
                    self.snd_una = self.snd_nxt = self.iss + 1
                    self.send_seg(ACK, self.snd_nxt)
                    return True
        return False

    def send_reliably(self, data):
        """Send data, resending until the OS acknowledges it."""
        start = self.snd_nxt
        self.snd_nxt += len(data)
        if self.out_of_order:               # the second half first: it must be dropped
            self.out_of_order = False
            half = len(data) // 2
            self.send_seg(ACK | PSH, start + half, data[half:])
        tries = 0
        while self.snd_una < self.snd_nxt and not self.reset:
            if tries == 8:
                self.problems.append(f"no ACK for data at {start - self.iss - 1}")
                return False
            self.send_seg(ACK | PSH, start, data)
            tries += 1
            deadline = time.time() + 1
            while self.snd_una < self.snd_nxt and time.time() < deadline:
                self.pump(0.05)
        return not self.reset

    def wait_for(self, predicate, seconds):
        deadline = time.time() + seconds
        while not predicate() and time.time() < deadline and not self.reset:
            self.pump(0.05)
        return predicate()

    def run(self):
        try:
            self.script()
        except Exception as e:                  # report, don't hang the test
            self.problems.append(f"exception {e!r}")

    def script(self):
        if not self.connect():
            self.problems.append("no SYN-ACK")
            return
        self.connected = True
        if self.peer_mss != 1460:
            self.problems.append(f"MSS option {self.peer_mss}")
        n = self.sport - 50000
        lines = [f"client {n} line {j}: " + "x" * (j * 3) for j in range(10)]
        expected = b""
        if self.batched:
            batch = b"".join(line.encode() + b"\r\n" for line in lines)
            if not self.send_reliably(batch):
                return
            expected = batch
            if self.wait_for(lambda: self.received.startswith(expected), 10):
                self.echoed = 10
        else:
            for line in lines:
                if not self.send_reliably(line.encode() + b"\r\n"):
                    break
                expected += line.encode() + b"\r\n"
                if not self.wait_for(lambda: len(self.received) >= len(expected), 10):
                    self.problems.append(f"no echo of {line!r}")
                    break
                if self.received != expected:
                    self.problems.append(f"echo of {line!r} was {self.received[-60:]!r}")
                    break
                self.echoed += 1
        if self.received != expected:
            self.problems.append("extra or wrong data")
        self.close()

    def close(self):
        """Our FIN, then wait for it to be acknowledged and for theirs."""
        fin_seq = self.snd_nxt
        self.snd_nxt += 1
        for _ in range(8):
            self.send_seg(FIN | ACK, fin_seq)
            if self.wait_for(lambda: self.snd_una == self.snd_nxt and self.fin_received, 1):
                break
        if self.reset:
            self.problems.append("reset by the OS")
        elif self.snd_una == self.snd_nxt and self.fin_received:
            self.closed = True
        else:
            self.problems.append("did not close")

    # ---- a terminal session

    def wait_for_text(self, marker, seconds=10):
        """Wait until marker arrives after the last one waited for."""
        m = marker.encode()
        start = getattr(self, "mark", 0)
        if not self.wait_for(lambda: m in self.received[start:], seconds):
            self.problems.append(f"no {marker!r}")
            return False
        self.mark = self.received.index(m, start) + len(m)
        return True

    def transcript(self):
        """What the OS sent, without telnet commands, with LF line ends."""
        out, data, i = bytearray(), self.received, 0
        while i < len(data):
            if data[i] != 255:
                out.append(data[i])
                i += 1
            elif i + 1 < len(data) and data[i + 1] == 255:
                out.append(255)
                i += 2
            elif i + 1 < len(data) and 251 <= data[i + 1] <= 254:
                i += 3
            else:
                i += 2
        return out.replace(b"\r\n", b"\n").decode(errors="replace")

    def expect_reset(self):
        self.snd_una = self.snd_nxt = self.iss
        self.rcv_nxt = 0
        self.send_seg(SYN, self.iss)
        try:
            packet, seg = self.q.get(timeout=5)
        except queue.Empty:
            return "no reply"
        seq, ack, off_flags = struct.unpack("!IIH", seg[4:14])
        ok = off_flags & (RST | ACK) == RST | ACK and ack == (self.iss + 1) % MOD32
        return "reset ok" if ok else f"wrong reply: flags {off_flags & 0x3F:#x}, ack {ack:#x}"


def main():
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--port", type=int, required=True)
    p.add_argument("--os-port", type=int, required=True)
    p.add_argument("script", choices=["ping", "udp", "tcp", "repl"])
    args = p.parse_args()
    peer = Peer(args.port, args.os_port)
    getattr(peer, "script_" + args.script)()
    while True:                     # keep answering until terminated
        time.sleep(1)


if __name__ == "__main__":
    sys.exit(main())
