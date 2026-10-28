#!/usr/bin/env python3
"""A host on a network test's private LAN: 10.0.2.2, MAC 52:55:0a:00:02:02.

Exchanges raw Ethernet frames with the OS as UDP datagrams on 127.0.0.1, one
frame per datagram: the format of QEMU's "dgram" network backend and of the
hosted build's network HAL. It answers ARP requests and pings for its own
address throughout, and runs a script against the OS at 10.0.2.15, printing
what it finds. It runs until terminated.

It also runs a UDP echo service on its port 7.

Usage: netpeer.py --port PORT --os-port PORT SCRIPT [ARG ...]
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
  repl   telnet sessions with the network REPL: port 4001 before an admin
         password is set; two sandbox sessions at once and a third the full
         door turns away; a full-Forth session after a wrong password; an idle
         session the OS ends; and a client that hangs up in the middle of a
         line. Prints what each session showed
  hostile  malformed frames at every layer (Ethernet, ARP, IP, ICMP, UDP, TCP),
         then hundreds of random ones, checking after each batch that the OS
         still answers a ping; telnet sessions with a slow typist and with
         rubbish of every kind; finally TCP and UDP echoes must still work
  soak   five rounds of four telnet sessions and four TCP echo clients at
         once, pings and UDP echoes; after each the OS reports, once its
         connections are gone, how much memory and its pools grew
  tcp-attack  an off-path attacker against the echo server on port 5000: a SYN
         flood beyond the OS's cap on half-open connections, then a real
         client; forged resets in and out of the window, a SYN and an
         acknowledgement of unsent data on an open connection (each must be
         answered by a challenge ACK or ignored, the connection kept); a client
         whose MSS option is 0; finally an exact reset, which must close it
  connect PORT [LINE ...]  for an app's tests: connect to the OS's TCP port
         (retrying while nothing listens), send each LINE with CR LF, then
         print what the OS sent until it closed the connection
  players PORT FILE  for an app's tests: several telnet clients at once,
         driven by the steps in FILE (see script_players), printing what
         each one sends and receives; clients can reconnect after a reboot
"""

import argparse
import queue
import random
import socket
import struct
import sys
import threading
import time

PEER_MAC = bytes.fromhex("52550a000202")
PEER_IP = bytes([10, 0, 2, 2])
OS_IP = bytes([10, 0, 2, 15])
BROADCAST = b"\xff" * 6
MULTICAST = bytes.fromhex("01005e000001")
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


# ---- Packets built field by field, any of which may be wrong on purpose

def ip_packet(payload, protocol=1, version=4, ihl=5, total=None, frag=0, src=PEER_IP, dst=OS_IP,
              options=b"", good_checksum=True):
    header = struct.pack("!BBHHHBBH4s4s", version << 4 | ihl, 0,
                         20 + len(options) + len(payload) if total is None else total,
                         1, frag, 64, protocol, 0, src, dst) + options
    value = checksum(header) if good_checksum else 0x1234
    return header[:10] + struct.pack("!H", value) + header[12:] + payload


def icmp_message(message):
    """An ICMP message with its checksum filled in, if it is long enough to have one."""
    if len(message) < 4:
        return message
    message = message[:2] + b"\0\0" + message[4:]
    return message[:2] + struct.pack("!H", checksum(message)) + message[4:]


def echo_request(ident, seq, data, reply=False):
    return icmp_message(struct.pack("!BBHHH", 0 if reply else 8, 0, 0, ident, seq) + data)


def arp_packet(htype=1, ptype=ETH_IP, hlen=6, plen=4, oper=1, sha=PEER_MAC, spa=PEER_IP,
               tha=bytes(6), tpa=OS_IP):
    return struct.pack("!HHBBH6s4s6s4s", htype, ptype, hlen, plen, oper, sha, spa, tha, tpa)


def tcp_segment(sport, dport, flags, seq=1000, ack=0, offset=None, options=b"", data=b"",
                src=PEER_IP, dst=OS_IP, good_checksum=True):
    hlen = 20 + len(options)
    words = hlen // 4 if offset is None else offset
    seg = struct.pack("!HHIIHHHH", sport, dport, seq, ack, words << 12 | flags, 65535, 0, 0) + options + data
    pseudo = src + dst + struct.pack("!BBH", 0, 6, len(seg))
    value = checksum(pseudo + seg) if good_checksum else 0x1234
    return seg[:16] + struct.pack("!H", value) + seg[18:]


def fix_checksum(protocol, body, src=PEER_IP, dst=OS_IP):
    """Random bytes with a right checksum, so that they get past it."""
    where = {1: 2, 6: 16, 17: 6}[protocol]
    body = body[:where] + b"\0\0" + body[where + 2:]
    if protocol == 17:
        body = body[:4] + struct.pack("!H", len(body)) + body[6:]
    pseudo = b"" if protocol == 1 else src + dst + struct.pack("!BBH", 0, protocol, len(body))
    return body[:where] + struct.pack("!H", checksum(pseudo + body) or 0xFFFF) + body[where + 2:]


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
        self.misaddressed = 0           # IP packets for us sent to some other MAC
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
            try:
                self.take(frame)
            except (IndexError, struct.error):      # a frame too short to make sense of
                pass

    def take(self, frame):
        src, eth_type, body = frame[6:12], struct.unpack("!H", frame[12:14])[0], frame[14:]
        if eth_type == ETH_ARP and len(body) >= 28:
            oper, sha, spa, tpa = struct.unpack("!6xH6s4s6x4s", body[:28])
            if tpa != PEER_IP:
                return
            if oper == 1:
                self.send(sha, ETH_ARP, self.arp(2, sha, spa))
            elif oper == 2:
                self.arp_replies.put((sha, spa))
        elif eth_type == ETH_IP and len(body) >= 20:
            ihl = (body[0] & 15) * 4
            total = struct.unpack("!H", body[2:4])[0]
            protocol, dst = body[9], body[16:20]
            if dst != PEER_IP:
                return
            if frame[:6] != PEER_MAC:
                self.misaddressed += 1
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
        start = time.time()
        for c in clients:
            threading.Thread(target=c.run, daemon=True).start()
        for c in clients:
            c.done.wait(max(0, start + 100 - time.time()))  # report before the console gives up
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

    def script_tcp_attack(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)                       # let the console start the server
        flood = [TcpClient(self, 52000 + i, dport=5000) for i in range(40)]
        for c in flood:                     # SYNs, never completed
            c.snd_una = c.snd_nxt = c.iss
            c.rcv_nxt = 0
            c.send_seg(SYN, c.iss, options=struct.pack("!BBH", 2, 4, 1460))
        def answered():                     # flood clients that have had a SYN-ACK
            for c in flood:
                while c.pump(0):
                    pass
            return sum(any(e[0] == SYN | ACK for e in c.log) for c in flood)
        deadline = time.time() + 15         # the OS may be slow under load: wait for the
        while answered() < 16 and time.time() < deadline:   # cap's worth, then a while for more
            time.sleep(0.1)
        time.sleep(1)
        answered()
        isns = [e[1] for c in flood for e in c.log[:1] if e[0] == SYN | ACK]
        print(f"peer: syn flood: {len(isns)} of 40 answered", flush=True)
        spread = all(min((a - b) % MOD32, (b - a) % MOD32) > 1 << 16 for a, b in zip(isns, isns[1:]))
        print(f"peer: initial sequence numbers unrelated: {'yes' if spread else 'no'}", flush=True)
        time.sleep(4)                       # the half-open connections time out

        c = TcpClient(self, 53000, dport=5000)
        if not c.connect():
            print("peer: after the flood: no SYN-ACK", flush=True)
            return
        print(f"peer: after the flood: echo {'ok' if c.echo(b'hello') else 'failed'}", flush=True)
        tests = [("reset in the window", lambda: c.send_seg(RST, c.snd_nxt + 1000)),
                 ("SYN on an open connection", lambda: c.send_seg(SYN, c.snd_nxt + 5)),
                 ("data acknowledging unsent bytes",
                  lambda: c.send_seg(ACK | PSH, c.snd_nxt, b"forged\r\n", ack=c.rcv_nxt + 100000))]
        for name, forge in tests:
            print(f"peer: {name}: {'challenge ACK' if c.challenged(forge) else 'no challenge ACK'}", flush=True)
        c.send_seg(RST, c.snd_nxt + 0x40000000)  # far outside the window: ignored
        c.drain(0.5)
        print(f"peer: reset outside the window: {'ignored' if not c.reset else 'reset'}", flush=True)
        print(f"peer: connection still works: {'yes' if c.echo(b'still here') else 'no'}", flush=True)
        c.send_seg(RST, c.snd_nxt)
        time.sleep(0.5)

        small = TcpClient(self, 53001, dport=5000)
        small.mss_option = 0
        if small.connect():
            line = b"y" * 150
            print(f"peer: client with MSS 0: echo {'ok' if small.echo(line) else 'failed'}", flush=True)
            small.close()

        stalled = TcpClient(self, 53002, dport=5000)  # sends, but never takes the echoes
        if stalled.connect():
            stalled.window = 0
            for j in range(100):
                if not stalled.send_reliably(f"stalled line {j:3} ".encode() + b"z" * 80 + b"\r\n"):
                    break
            reset = stalled.wait_for(lambda: stalled.reset, 40)
            print(f"peer: reader that never reads: {'reset by the OS' if reset else 'not reset'}", flush=True)
        for client in (c, small):
            for problem in client.problems:
                print(f"peer: client {client.sport}: {problem}", flush=True)

    def script_repl(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)
        probe = TcpClient(self, 51004, dport=4001)    # before the console sets a password
        a, b = TcpClient(self, 51000, dport=4000), TcpClient(self, 51001, dport=4000)
        full = TcpClient(self, 51005, dport=4000)     # the door allows two
        admin = TcpClient(self, 51002, dport=4001)
        idle = TcpClient(self, 51006, dport=4000)
        quitter = TcpClient(self, 51003, dport=4000)
        sessions = [("no password", probe), ("sandbox A", a), ("sandbox B", b), ("door full", full),
                    ("full Forth", admin), ("idle", idle), ("hang-up", quitter)]
        if probe.connect():
            probe.wait_for(lambda: probe.fin_received, 10)
        for _, c in sessions[1:3]:
            if c.connect():
                c.connected = True
                c.wait_for_text("leave.\r\n")
            else:
                c.problems.append("no SYN-ACK")
        if full.connect():
            full.wait_for(lambda: full.fin_received, 10)
        steps = [(a, "2 3 + .", "ok"), (a, "hex ff .", "ok"), (b, "ff .", "?"),
                 (a, "decimal 1 2 3", "ok"), (b, ".s", "ok"), (a, ".s", "ok"),
                 (a, "here .", "?"), (a, ": sq dup * ;", "?"), (a, "words", "ok"),
                 (a, "bye", "ok"), (b, "bye", "ok")]
        for c, line, end in steps:
            if c.connected and not c.problems:
                c.send_reliably(line.encode() + b"\r\n")
                c.wait_for_text(end + "\r\n")
        for c in (a, b):
            c.wait_for(lambda: c.fin_received, 10)
        if idle.connect():                      # says nothing: the OS ends it
            idle.wait_for_text("leave.\r\n")
        for attempt in range(20):               # the console may not have set it yet
            if admin.connect():
                admin.wait_for(lambda: b"Password: " in admin.received or admin.fin_received, 10)
                if b"Password: " in admin.received:
                    break
                admin.close()
            time.sleep(1)
            admin = TcpClient(self, 51010 + attempt, dport=4001)
        sessions[4] = ("full Forth", admin)
        if b"Password: " in admin.received:     # a wrong password, then the right one
            admin.wait_for_text("Password: ")
            admin.send_reliably(b"wrong\r\n")
            admin.wait_for_text("Password: ")
            admin.send_reliably(b"secret\r\n")
            admin.wait_for_text("leave.\r\n")
            for line in [": sq dup * ; 7 sq .", "here 0<> .", "bye"]:
                admin.send_reliably(line.encode() + b"\r\n")
                admin.wait_for_text("ok\r\n")
        if quitter.connect():                   # a partial line, then hang up
            quitter.wait_for_text("leave.\r\n")
            quitter.send_reliably(b"1 2 + .")
            quitter.close()                     # the OS runs what it has, then closes
        for _, c in sessions:
            if not c.closed:
                c.wait_for(lambda: c.fin_received, 20)
                c.close()
        for name, c in sessions:
            for line in c.transcript().rstrip("\n").split("\n"):
                print(f"peer: {name}| {line}", flush=True)
            print(f"peer: {name}: {'closed' if c.closed else 'not closed'}", flush=True)
            for problem in c.problems:
                print(f"peer: {name}: {problem}", flush=True)

    def script_connect(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        port, lines = int(self.args[0]), self.args[1:]
        c = TcpClient(self, 51000, dport=port)
        if not c.connect():
            print(f"peer: no connection to port {port}", flush=True)
            return
        for line in lines:
            c.send_reliably(line.encode() + b"\r\n")
        if not c.wait_for(lambda: c.fin_received, 30):
            c.problems.append("the OS did not close")
        c.close()
        for line in c.transcript().rstrip("\n").split("\n"):
            print(f"peer: {port}| {line}", flush=True)
        print(f"peer: {port}: {'closed' if c.closed else 'not closed'}", flush=True)
        for problem in c.problems:
            print(f"peer: {port}: {problem}", flush=True)

    def script_players(self):
        """Several telnet clients driven by a script file, one step a line:
        NAME connect [PORT], NAME> TEXT (send a line), NAME? TEXT (wait for it),
        NAME close, NAME gone (wait for the OS to close), sleep SECONDS, and
        # comments. A client that connects again gets a fresh port, so it can
        come back after the OS reboots. What each client receives is printed
        when a step waits on it, up to the end of what it waited for."""
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        port, path = int(self.args[0]), self.args[1]
        with open(path) as f:
            steps = [line.rstrip("\n") for line in f]
        clients, sport = {}, 52000

        def say(name, text):
            for line in text.split("\n"):
                print(f"peer: {name}| {line}", flush=True)

        def show(name, c, upto=None):      # what arrived since last shown, up to upto
            upto = len(c.received) if upto is None else upto
            text = telnet_text(c.received[c.shown:upto]).replace("\x1b", "\\e")
            c.shown = max(c.shown, upto)
            if text:
                say(name, text[:-1] if text.endswith("\n") else text)

        def problems(name, c):
            for problem in c.problems:
                print(f"peer: {name}: {problem}", flush=True)
            c.problems = []

        for step in steps:
            if not step.strip() or step.startswith("#"):
                continue
            head, _, rest = step.partition(" ")
            if head == "sleep":
                time.sleep(float(rest))
                continue
            if head[-1:] in (">", "?"):
                name, action = head[:-1], head[-1]
            else:
                name, (action, _, rest) = head, rest.partition(" ")
            c = clients.get(name)
            if action == "connect":            # NAME connect [PORT]
                c = clients[name] = TcpClient(self, sport, dport=int(rest) if rest else port)
                c.shown = 0
                sport += 1
                print(f"peer: {name} {'connected' if c.connect() else 'could not connect'}", flush=True)
            elif c is None:
                print(f"peer: {name}: no such client for {step!r}", flush=True)
            elif action == ">":
                print(f"peer: {name}> {rest}", flush=True)
                c.send_reliably(rest.encode() + b"\r\n")
            elif action == "?":
                if c.wait_for(lambda: rest.encode() in c.received[c.shown:], 20):
                    show(name, c, c.received.index(rest.encode(), c.shown) + len(rest))
                else:
                    show(name, c)
                    print(f"peer: {name}: no {rest!r}", flush=True)
            elif action == "close":
                c.close()
                show(name, c)
                print(f"peer: {name} {'closed' if c.closed else 'not closed'}", flush=True)
            elif action == "gone":
                c.wait_for(lambda: c.fin_received, 20)
                c.close()
                show(name, c)
                print(f"peer: {name} {'closed by the OS' if c.closed else 'not closed'}", flush=True)
            else:
                print(f"peer: unknown step {step!r}", flush=True)
            if c is not None:
                problems(name, c)
        print("peer: done", flush=True)

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

    # ---- hostile input

    def raw(self, frame):
        """Any bytes at all, as one frame."""
        self.sock.sendto(frame, self.os_addr)

    def alive(self):
        """The OS still answers a ping (three tries)."""
        for _ in range(3):
            self.alive_seq = getattr(self, "alive_seq", 1000) + 1
            self.send_ip(1, echo_request(self.ident, self.alive_seq, b"still there?"))
            deadline = time.time() + 5
            while time.time() < deadline:
                try:
                    packet, ihl, message = self.echo_replies.get(timeout=max(0.01, deadline - time.time()))
                except queue.Empty:
                    break
                if message[4:8] == struct.pack("!HH", self.ident, self.alive_seq):
                    return True
        return False

    def script_hostile(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)                       # let the console start the servers
        print(f"peer: before: {'answering' if self.alive() else 'not answering'}", flush=True)
        rng = random.Random(4)
        os_mac = self.os_mac
        eth = lambda eth_type, body: os_mac + PEER_MAC + struct.pack("!H", eth_type) + body
        echo = echo_request(0x4242, 1, b"x" * 8)
        arp = lambda **f: arp_packet(**f)
        def tcp(dport=5000, **f):
            f.setdefault("sport", 60000 + rng.randrange(999))
            return tcp_segment(dport=dport, **f)

        layers = [
            ("ethernet", [b"\x01", os_mac, os_mac + PEER_MAC, eth(ETH_IP, b"")[:13],
                          eth(ETH_IP, b""), eth(ETH_ARP, b""), eth(0x86DD, bytes(40)),
                          eth(0, b"zero"), eth(ETH_IP, b"\xff" * 1500), eth(ETH_ARP, bytes(1586)),
                          os_mac + BROADCAST + eth(ETH_IP, ip_packet(echo))[12:],
                          os_mac + MULTICAST + eth(ETH_IP, ip_packet(echo))[12:]]),
            ("arp", [eth(ETH_ARP, p) for p in [
                b"", arp()[:8], arp()[:27], arp(htype=6), arp(ptype=0x86DD), arp(hlen=0),
                arp(plen=0), arp(hlen=255, plen=255), arp(oper=99),
                arp(spa=OS_IP), arp(spa=b"\xff" * 4), arp(spa=bytes([224, 0, 0, 1])), arp(spa=bytes(4))]
                + [arp(sha=bytes([2, 0, 0, 0, 0, i]), spa=bytes([10, 0, 2, 100 + i])) for i in range(50)]
                + [arp(sha=BROADCAST), arp(sha=MULTICAST)]]),
            ("ip", [eth(ETH_IP, p) for p in [
                ip_packet(echo, version=6), ip_packet(echo, version=0)]
                + [ip_packet(echo, ihl=n) for n in range(5)]
                + [ip_packet(echo, ihl=15), ip_packet(echo, total=10), ip_packet(echo, total=0),
                   ip_packet(echo, total=19), ip_packet(echo, total=200), ip_packet(echo, total=0xFFFF),
                   ip_packet(echo, good_checksum=False), ip_packet(echo, frag=0x2000),
                   ip_packet(echo, frag=0x0010), ip_packet(echo, src=OS_IP),
                   ip_packet(echo, src=b"\xff" * 4), ip_packet(echo, src=bytes([224, 0, 0, 1])),
                   ip_packet(echo, dst=bytes([10, 0, 2, 99])), ip_packet(b"???", protocol=99),
                   ip_packet(b"???", protocol=99, dst=b"\xff" * 4),
                   ip_packet(echo, options=b"\x01\x01\x01\x00"), ip_packet(b"")[:19]]]),
            ("icmp", [eth(ETH_IP, ip_packet(m)) for m in
                      [icmp_message(bytes(n)) for n in range(8)]
                      + [echo[:2] + b"\0\0" + echo[4:], icmp_message(b"\x0d" + bytes(19)),
                         icmp_message(b"\x03\x03" + bytes(6)), icmp_message(b"\x05\x01" + bytes(30)),
                         echo_request(0x4F53, 7, b"", reply=True)]]),
            ("udp", [eth(ETH_IP, ip_packet(p, protocol=17)) for p in [
                b"", struct.pack("!HH", 40000, 7), struct.pack("!HHHH", 40000, 7, 0, 0),
                struct.pack("!HHHH", 40000, 7, 7, 0) + b"x", struct.pack("!HHHH", 40000, 7, 9, 0),
                struct.pack("!HHHH", 40000, 7, 0xFFFF, 0) + b"x",
                self.udp_segment(40000, 7, b"bad checksum")[:6] + b"\x12\x34" + b"bad checksum"]]
                + [eth(ETH_IP, ip_packet(self.udp_segment(40000, 9, b"to all", dst=b"\xff" * 4),
                                         protocol=17, dst=b"\xff" * 4))]),
            ("tcp", [eth(ETH_IP, ip_packet(p, protocol=6, dst=d)) for p, d in [
                (b"", OS_IP), (tcp(flags=SYN)[:10], OS_IP), (tcp(flags=SYN)[:19], OS_IP),
                (tcp(flags=SYN, offset=0), OS_IP), (tcp(flags=SYN, offset=1), OS_IP),
                (tcp(flags=SYN, offset=4), OS_IP), (tcp(flags=SYN, offset=15), OS_IP),
                (tcp(flags=SYN, offset=6), OS_IP),
                (tcp(flags=SYN, options=b"\x02\x00\x05\xb4"), OS_IP),
                (tcp(flags=SYN, options=b"\x02\x01\x05\xb4"), OS_IP),
                (tcp(flags=SYN, options=b"\x02\xff\x05\xb4"), OS_IP),
                (tcp(flags=SYN, options=b"\x01\x01\x02\x04"), OS_IP),
                (tcp(flags=SYN, options=b"\x01" * 40), OS_IP),
                (tcp(flags=SYN, options=b"\x1e\x0a" + bytes(10)), OS_IP),
                (tcp(flags=0x3F), OS_IP), (tcp(flags=SYN | FIN), OS_IP), (tcp(flags=SYN | RST), OS_IP),
                (tcp(flags=0), OS_IP), (tcp(flags=FIN), OS_IP), (tcp(flags=0x20), OS_IP),
                (tcp(dport=4999, flags=SYN | FIN, data=b"data with a SYN"), OS_IP),
                (tcp(flags=SYN, good_checksum=False), OS_IP),
                (tcp(flags=SYN, sport=60999, dst=b"\xff" * 4), b"\xff" * 4)]]),
        ]
        to_all = self.tcp_queues[60999] = queue.Queue()     # for the SYN to the broadcast address
        for name, frames in layers:
            for frame in frames:
                self.raw(frame)
            time.sleep(0.5)
            print(f"peer: malformed {name}: {len(frames)} frames, "
                  f"{'still answering' if self.alive() else 'not answering'}", flush=True)

        print(f"peer: SYN to the broadcast address: {'ignored' if to_all.empty() else 'answered'}", flush=True)
        print(f"peer: replies sent to a forged group MAC: {self.misaddressed}", flush=True)

        big = echo_request(self.ident, 77, bytes(range(256)) * 5 + bytes(192))   # 1472 bytes of data
        self.send_ip(1, big)
        try:
            while True:
                packet, ihl, message = self.echo_replies.get(timeout=5)
                if message[4:8] == big[4:8]:
                    break
            print(f"peer: largest ping: {'ok' if message[8:] == big[8:] else 'wrong data'}", flush=True)
        except queue.Empty:
            print("peer: largest ping: no reply", flush=True)

        frames = []                         # junk, then junk behind good headers so it reaches the parsers
        for _ in range(200):
            body = bytes(rng.randrange(256) for _ in range(rng.randrange(1, 300)))
            frames.append(eth(rng.choice([ETH_IP, ETH_ARP, rng.randrange(65536)]), body))
        for _ in range(400):
            protocol = rng.choice([1, 6, 17, rng.randrange(256)])
            body = bytes(rng.randrange(256) for _ in range(rng.randrange(0, 300)))
            if rng.random() < 0.5 and protocol in (1, 6, 17) and len(body) >= 20:
                body = fix_checksum(protocol, body)
            frames.append(eth(ETH_IP, ip_packet(body, protocol=protocol)))
        for frame in frames:
            self.raw(frame)
        time.sleep(0.5)
        print(f"peer: random bytes: {len(frames)} frames, "
              f"{'still answering' if self.alive() else 'not answering'}", flush=True)

        self.hostile_telnet()

        self.send_ip(17, self.udp_segment(40005, 5002, b"spin"))  # a handler that never returns
        time.sleep(1)
        print(f"peer: a UDP handler that never returns: "
              f"{'still answering' if self.alive() else 'not answering'}", flush=True)

        last = TcpClient(self, 61000, dport=5000)
        if last.connect():
            print(f"peer: afterwards: tcp echo {'ok' if last.echo(b'after it all') else 'failed'}", flush=True)
            last.close()
        else:
            print("peer: afterwards: no SYN-ACK", flush=True)
        self.send_ip(17, self.udp_segment(40003, 7, b"udp after it all"))
        try:
            got = self.udp_replies.get(timeout=5)[2][8:]
            print(f"peer: afterwards: udp echo {'ok' if got == b'udp after it all' else 'wrong'}", flush=True)
        except queue.Empty:
            print("peer: afterwards: no udp echo", flush=True)
        print(f"peer: afterwards: {'answering' if self.alive() else 'not answering'}", flush=True)
        for _ in range(5):                  # tell the console we are done
            self.send_ip(17, self.udp_segment(40004, 5001, b"done"))
            time.sleep(0.2)

    def script_soak(self):
        if not self.find_os():
            print("peer: no ARP reply from 10.0.2.15", flush=True)
            return
        time.sleep(1)                       # let the console start the servers
        problems = []
        for r in range(1, 6):
            telnet = [TcpClient(self, 62000 + 20 * r + i, dport=4000) for i in range(4)]
            echo = [TcpClient(self, 62010 + 20 * r + i, dport=5000) for i in range(4)]
            for c in telnet + echo:         # all open at once: each round peaks the same
                if not c.connect():
                    problems.append(f"round {r}: {c.sport} no SYN-ACK")
            for i, c in enumerate(telnet):
                c.wait_for_text("leave.\r\n")
                c.send_reliably(f"{r} {i + 2} * .\r\n".encode())
                c.wait_for_text(f"{r * (i + 2)}  ok\r\n")
            for c in echo:
                for j in range(2):
                    if not c.echo(f"round {r} line {j}".encode()):
                        problems.append(f"round {r}: {c.sport} no echo")
            if not self.alive():
                problems.append(f"round {r}: no ping reply")
            self.send_ip(17, self.udp_segment(40011, 7, f"round {r}".encode()))
            for c in telnet:
                c.send_reliably(b"bye\r\n")
            for c in telnet:
                c.wait_for(lambda: c.fin_received, 10)
            for c in telnet + echo:
                c.close()
                problems += [f"round {r}: {c.sport} {p}" for p in c.problems]
                threading.Thread(target=lambda c=c: [c.pump(1) for _ in iter(int, 1)],
                                 daemon=True).start()   # TIME-WAIT: answer a resent FIN
            self.send_ip(17, self.udp_segment(40010, 5001, b"mark"))
            deadline = time.time() + 70     # the OS answers once its connections are gone
            while time.time() < deadline:
                try:
                    packet, ihl, message = self.udp_replies.get(timeout=1)
                except queue.Empty:
                    continue
                if message[8:] == b"ready":
                    break
            else:
                problems.append(f"round {r}: the OS did not settle")
                break
        print(f"peer: soak: {r} rounds", flush=True)
        for p in problems:
            print(f"peer: {p}", flush=True)

    def hostile_telnet(self):
        """Telnet clients of the sandbox: a slow typist, who must not hold up
        anyone else, and one who sends every kind of rubbish."""
        slow, quick, junk = (TcpClient(self, p, dport=4000) for p in (61010, 61011, 61012))
        clients = [("slow typist", slow), ("quick", quick), ("rubbish", junk)]
        for name, c in clients:
            if not (c.connect() and c.wait_for_text("leave.\r\n")):
                print(f"peer: telnet {name}: no session", flush=True)
                return
        for ch in b"1 2 ":
            slow.send_reliably(bytes([ch]))
            time.sleep(0.2)
        quick.send_reliably(b"6 7 * .\r\n")
        print(f"peer: telnet: another session answers while one types slowly: "
              f"{'yes' if quick.wait_for_text('42  ok\r\n', 5) else 'no'}", flush=True)
        for ch in b"+ .\r\n":
            slow.send_reliably(bytes([ch]))
            time.sleep(0.2)
        print(f"peer: telnet slow typist: {'ok' if slow.wait_for_text('3  ok\r\n') else 'no answer'}", flush=True)

        IAC = 255
        cases = [
            ("subnegotiation 3000 bytes long",
             bytes([IAC, 250, 24]) + b"x" * 3000 + bytes([IAC, 240]) + b"2 2 + .\r\n", "4  ok\r\n"),
            ("every command and option",
             b"".join(bytes([IAC, c, 1]) if c >= 251 else bytes([IAC, c]) for c in range(236, 255) if c != 250)
             + b"\r\n3 3 + .\r\n", "6  ok\r\n"),
            ("an escaped 255 in a line", bytes([IAC, IAC]) + b"\r\n" + b"4 4 + .\r\n", "8  ok\r\n"),
            ("control characters in a line", b"5\x00 5\x01 +\x07 \x1b.\r\n", "10  ok\r\n"),
            ("CR NUL line end", b"6 6 + .\r\0", "12  ok\r\n"),
            ("a 5000-byte line", b"x" * 5000 + b"\r\n7 7 + .\r\n", "14  ok\r\n"),
            ("a line end inside a subnegotiation", bytes([IAC, 250]) + b"\r\n"
             + bytes([IAC, 240]) + b"8 8 + .\r\n", "16  ok\r\n"),
        ]
        for name, data, answer in cases:
            for i in range(0, len(data), 1000):
                junk.send_reliably(data[i:i + 1000])
            print(f"peer: telnet {name}: {'ok' if junk.wait_for_text(answer) else 'no answer'}", flush=True)
        for _, c in clients:
            c.send_reliably(b"bye\r\n")
        for _, c in clients:
            c.wait_for(lambda: c.fin_received, 10)
            c.close()
        for name, c in clients:
            for problem in c.problems:
                print(f"peer: telnet {name}: {problem}", flush=True)


MOD32 = 1 << 32


def backoff(budget):
    """Times to wait between resends, doubling from 1 s to 8 s, as real TCP
    backs off: resending at a fixed rate to a receiver that has fallen behind
    only queues more stale segments in front of the ones it needs."""
    end, wait = time.time() + budget, 1
    while time.time() < end:
        yield min(wait, max(0.05, end - time.time()))
        wait = min(wait * 2, 8)
FIN, SYN, RST, PSH, ACK = 1, 2, 4, 8, 16


def telnet_text(data):
    """Bytes from a telnet server as text: telnet commands removed, LF line ends."""
    out, i = bytearray(), 0
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
        self.mss_option = 1460
        self.window = 65535                 # what we advertise
        self.log = []                       # (flags, seq, ack, data length) of each segment in
        self.done = threading.Event()       # the script has finished

    # ---- segments

    def send_seg(self, flags, seq, data=b"", options=b"", ack=None):
        hlen = 20 + len(options)
        if ack is None:
            ack = self.rcv_nxt if flags & ACK else 0
        ack %= MOD32
        seg = struct.pack("!HHIIHHHH", self.sport, self.dport, seq % MOD32, ack,
                          (hlen // 4) << 12 | flags, self.window, 0, 0) + options + data
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
        self.log.append((flags, seq, ack, len(data)))
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
        if data and offset == 0 and self.window:   # a closed window takes nothing
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
        for wait in backoff(30):
            self.send_seg(SYN, self.iss, options=struct.pack("!BBH", 2, 4, self.mss_option))
            deadline = time.time() + wait
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
        for wait in backoff(40):
            if self.snd_una >= self.snd_nxt or self.reset:
                return not self.reset
            self.send_seg(ACK | PSH, start, data)
            deadline = time.time() + wait
            while self.snd_una < self.snd_nxt and time.time() < deadline:
                self.pump(0.05)
        if self.snd_una >= self.snd_nxt or self.reset:
            return not self.reset
        self.problems.append(f"no ACK for data at {start - self.iss - 1}")
        return False

    def drain(self, seconds):
        """Take in whatever the OS sends for this long."""
        deadline = time.time() + seconds
        while time.time() < deadline:
            self.pump(0.05)

    def challenged(self, forge):
        """Send a forged segment; True if a challenge ACK came back (a bare
        ACK of what we really sent) and the connection survived."""
        start = len(self.log)
        forge()
        bare = lambda: [e for e in self.log[start:] if e[0] == ACK and e[3] == 0 and e[2] == self.snd_nxt % MOD32]
        self.wait_for(bare, 10)
        return bool(bare()) and not self.reset

    def echo(self, line):
        """Send a line and check it comes back."""
        start = len(self.received)
        if not self.send_reliably(line + b"\r\n"):
            return False
        self.wait_for(lambda: len(self.received) >= start + len(line) + 2, 10)
        return self.received[start:] == line + b"\r\n"

    def wait_for(self, predicate, seconds):
        deadline = time.time() + seconds
        while not predicate() and time.time() < deadline and not self.reset:
            self.pump(0.05)
        return predicate()

    def run(self):
        """The script, then keep acknowledging what the OS sends, as a closed
        client in TIME-WAIT would: a resent FIN must not go unanswered."""
        try:
            self.script()
        except Exception as e:                  # report, don't hang the test
            self.problems.append(f"exception {e!r}")
        self.done.set()
        while True:
            self.pump(1)

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
        for wait in backoff(30):
            self.send_seg(FIN | ACK, fin_seq)
            if self.wait_for(lambda: self.snd_una == self.snd_nxt and self.fin_received, wait):
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
        return telnet_text(self.received)

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
    p.add_argument("script", choices=["ping", "udp", "tcp", "tcp-attack", "repl", "hostile", "soak",
                                      "connect", "players"])
    p.add_argument("args", nargs="*", help="the script's arguments")
    args = p.parse_args()
    peer = Peer(args.port, args.os_port)
    peer.args = args.args
    getattr(peer, "script_" + args.script.replace("-", "_"))()
    while True:                     # keep answering until terminated
        time.sleep(1)


if __name__ == "__main__":
    sys.exit(main())
