# BeePL UDP load-balancer prototype

`applications/tc_udp_lb.bpl` implements a small direct-server-return (DSR)
forwarding policy at TC ingress. It selects one of two backends for the virtual
service **192.0.2.100:9000/UDP**, rewrites the 12 Ethernet address bytes, and calls
`bpf_redirect`. The destination IP and UDP port remain unchanged. Both backends
own the VIP on loopback and respond using that address. In the test topology,
responses route through the router namespace to the client; no reverse BPF
translation is needed.

The verifier accepted this prototype and all 14 live request/reply checks passed
on Linux 7.0.0-42-generic, with successful cleanup. Source, object and compiler
hashes match the tested artifacts. Evidence: [live report](results/archive/lb-live.json).
The first 16 packet cases passed; the initial run then hit a kernel test-input
restriction. Short-frame fixtures are corrected, and the complete 44-case packet
suite awaits a rerun. The original failure report is preserved in
[the archive](results/archive/kernel-lb-short-fixture-failure.json).

## Build and test

Run from the repository root:

```sh
make -C evaluation/examples build EXAMPLE=tc_udp_lb
llvm-objdump -d evaluation/.build/objects/tc_udp_lb.o
bpftool btf dump file evaluation/.build/objects/tc_udp_lb.o format raw
sudo make -C evaluation/examples kernel-lb-check
sudo make -C evaluation/examples lb-live
```

Artifacts: `evaluation/.build/objects/tc_udp_lb.s`, `.o`, `.bin`, `.disasm` and
build hashes in `.manifest.json`. Loadable objects are `.o`; raw `.bin` files
lack ELF/map metadata. Root runners consume these prebuilt artifacts and reject
stale source/compiler/object hashes. No handwritten bytecode or C datapath is used.

`kernel-lb-check` loads through the verifier and executes 44 synthetic packet
cases: backend selection, repeatability, forced backends, disabling service,
nonmatching traffic, fragments/options, inconsistent lengths, and every length
14–41. For lengths 14–33 the fixtures use experimental EtherType 0x88b5:
Linux rejects IPv4-labeled TC test packets below 34 bytes before invoking BPF.
These L2 fixtures exercise helper bounds failures before protocol selection.
Lengths 34–41 retain IPv4 EtherType and exercise truncated UDP access. It checks the exact rewritten Ethernet addresses and unchanged remaining
packet bytes. The report is `evaluation/results/kernel-lb.json`. It uses
`BPF_PROG_TEST_RUN`, not real forwarding. The userspace interpreter does not
model these helpers; an unprivileged build is not an execution test.

`lb-live` needs root, `ip`, `tc`, `sysctl`, Python 3 and libbpf. It creates four
unique namespaces and three veth pairs. It starts two UDP servers and two client
sockets, creates a clsact qdisc, configures the map, and attaches the actual BeePL
program with libbpf. Fourteen assertions check:

- No service before attachment or after detachment.
- Both backends receive their selected flows, with three repetitions each.
- Replies contain the correct backend ID and original payload, from the VIP/port.
- A map mode update moves an existing flow to the other backend.
- Disabling the service stops replies; restoring hashing restores replies.

Results and TC statistics are saved in `evaluation/results/lb-live.json`.
The runner stops/reaps workers, detaches the program and removes its namespaces,
including on errors. It changes no host routes or interfaces and does not require
bpffs mounting. Sysctl changes are confined to disposable network namespaces.
Do not manually attach this demonstration to a production interface.

## Map configuration

The array `counts` retains the evaluation map name but holds configuration, not
counters. It has `uint32` keys and `ulong` values:

| Keys | Meaning |
| --- | --- |
| 0 | Mode: 0 hash, 1 force A, 2 force B, 3 disabled; larger values also drop |
| 1 / 5 | Backend A / B egress interface index |
| 2–4 / 6–8 | Three little-endian uint32 words: destination MAC followed by source MAC |

Initialize backend tuples before attachment. They are not an atomic multi-key
snapshot: change tuples while detached. A single mode entry can be updated live,
as the test demonstrates. There is no flow table, so forcing a backend changes
existing flows as well. The parity hash uses source IPv4 and source port; it is
for deterministic demonstration and is not a production distribution algorithm.

## Parsing and helper contracts

Only untagged, fixed-IHL IPv4 UDP packets are eligible. Fragments and malformed
lengths drop. Nonmatching VIP/port or protocols return TC_ACT_OK after the relevant
header guards; short packets can drop before protocol classification. The parser
requires at least 42 bytes. This does not validate IP/UDP checksums; it preserves
them, and the backend network stack checks incoming checksums.

The source checker limits `bpf_skb_load_bytes` and `bpf_skb_store_bytes` to a
`uint32*` buffer and literal `(uint32)4` length. The kernel helper checks packet
bounds. Store/redirect flags must be literal `(ulong)0`. These helpers currently
require a TC entry point, including when called through ordinary BeePL functions.
Every helper result that can fail is checked; failure drops the packet. Packet
access uses offsets and typed buffers, without arbitrary source pointer arithmetic.
The checker restrictions are part of the trusted implementation; no new formal
soundness proof is claimed.

## Remaining production work

No NAT, checksum-changing mutation, dynamic header cursor, IPv6 service, VLAN
service, connection tracking, health checker, concurrent backend-table replacement,
production hashing, throughput/latency benchmark, or multi-kernel qualification
is provided. This is the first complete application target, not Katran parity.
