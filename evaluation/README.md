# BeePL eBPF evaluation

This suite exercises BeePL source → the extracted BeePL typechecker → Csyntax →
CompCert's **ebpf64** backend → LLVM's assembler → a Linux eBPF ELF object.
The compiler build is isolated in `.build/compiler`; the repository's native
compiler configuration is preserved.

**Status:** 49 programs compile (45 examples and four applications). The original
37 pass 290 userspace instruction cases; five map programs and two new syscall
tracers pass libbpf map-metadata validation and are not emulated. Four
cgroup socket policies pass program/attach metadata validation and are not
emulated. All 43 rejection tests and 33 harness tests pass. Native and isolated eBPF compiler builds pass.

Packet/map kernel evidence covers 42 programs and 305 cases: 26 XDP programs (255),
four socket filters (12), seven TC programs (23), and five typed-map programs (15).
Real UDP socket delivery passed 10 checks; real TC ingress passed 15 checks.
Reports are retained under [results/archive](results/archive). All 42 previously
kernel-tested objects remain byte-for-byte unchanged; archived reports retain
the compiler identity used in each run. Both new tracers also passed the verifier
and all 15 live syscall checks on Linux 7.0.0-42-generic; see the
[tracing report](results/archive/kernel-tracing.json). This brings coverage to
42 kernel-tested programs before the cgroup milestone. All four cgroup socket
policies passed all 80 IPv4/IPv6 live checks. The two VLAN classifiers also passed
55 kernel cases, bringing the total to 48 kernel-tested programs, with
305 packet/map cases and 120 live checks. The expanded 80-case
suite supersedes the earlier 30-case IPv4 suite in this total.
This is not support for all eBPF programs or a completed formal soundness proof.

## UDP load-balancer application

[tc_udp_lb](applications/tc_udp_lb.bpl) is a two-backend IPv4 UDP direct-server-return
prototype: it selects a backend, rewrites Ethernet addresses, redirects the
packet, and supports live mode configuration through a map. It preserves the
VIP, UDP port and checksums. The [complete run guide](LOAD_BALANCER.md) describes
the topology, narrow packet profile, helper restrictions and remaining limitations.

```sh
sudo make -C evaluation/examples kernel-lb-check
sudo make -C evaluation/examples lb-live
```

The first command tests 44 packet cases; the second creates four temporary
namespaces and checks real UDP requests/replies in 14 assertions. Reports are
`results/kernel-lb.json` and `results/lb-live.json`. The program passed verifier loading and all 14 live checks; see the
[archived live report](results/archive/lb-live.json). The first 16 packet cases
passed, then the test runner rejected an undersized IPv4 fixture before BPF ran.
The short-frame fixtures are corrected; rerun `kernel-lb-check` for the complete
44-case result. No program rebuild or live rerun is needed. It is not emulated.

## VS Code highlighting

A tested declarative extension is available in [editors/vscode/beepl](../editors/vscode/beepl).
It highlights `.bpl` files and provides bracket pairing, block comments and snippets.
Build/install the VSIX using that directory's guide. It has no language server or
compiler diagnostics. Marketplace publication is deferred; VSIX sharing works now.

## Collection by category

Counts include runnable `.bpl` files, not negative typechecker fixtures.

| Category | Examples | Applications |
| --- | ---: | ---: |
| XDP language features and helpers | 17 | 0 |
| XDP packet parsing and filtering | 7 | 2 |
| XDP typed maps | 5 | 0 |
| Socket filters | 4 | 0 |
| TC traffic control | 7 | 1 |
| Raw syscall tracing | 1 | 1 |
| Cgroup socket creation policies | 4 | 0 |
| **Total** | **45** | **4** |

Applications: `ipv6_guard`, `udp_port_filter`, `syscall_histogram`, and `tc_udp_lb`.
The original 48 programs have saved passing kernel evidence, including the VLAN
classifiers. The load-balancer application also passed all 14 live checks; its corrected
packet suite awaits a complete rerun.

## On-wire VLAN and QinQ filtering

`xdp_vlan_ipv4` passes a single 802.1Q tag with VID 100 and inner IPv4 EtherType.
`xdp_qinq_ipv4` passes an 802.1ad outer VID 200, 802.1Q inner VID 100, and inner
IPv4 EtherType. Other tag layouts/IDs and inner EtherTypes drop. Both use fixed
scalar `Pbytes` schemas (18 and 22 bytes) without source pointer arithmetic.
The VLAN ID masks exclude PCP/DEI bits, so priority and drop-eligibility flags
do not affect the policy. EtherType and tag constants follow Linux
`include/uapi/linux/if_ether.h` and `VLAN_VID_MASK` in `include/linux/if_vlan.h`.

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples kernel-vlan-check
```

Results: `evaluation/results/kernel-vlan.json`. There are 55 cases covering
matching IDs, wrong IDs and tag types, priority/DEI bits, inner EtherTypes,
extra/missing tags, exact header bounds and every truncated length from 14 bytes.
Both classifiers passed the verifier and all 55 kernel cases on Linux
7.0.0-42-generic; all packet-preservation assertions passed. Source, object and
compiler hashes match the current files. Evidence is retained in the
[archived VLAN report](results/archive/kernel-vlan.json). All 55 userspace cases
also pass. Full compile/load/inspect/attach/detach commands are in each source.
The existing `kernel-packet-check` retains its original five-program scope;
`kernel-check` includes both new VLAN programs.

These examples classify tag headers only: matching header-only frames pass,
and IPv4 contents/checksums are not validated. No dynamic tag traversal, packet
mutation, or hardware-stripped VLAN metadata is supported. Test-run supplies
on-wire tag bytes and does not establish behavior with NIC offloads.

## Cgroup socket creation policies

Four examples extend the collection to `cgroup/sock_create`:

| Example | Policy |
| --- | --- |
| `cgroup_sock_allow` | Allow Internet socket creation |
| `cgroup_sock_deny` | Deny Internet socket creation |
| `cgroup_sock_udp` | Deny datagram sockets, allow stream sockets |
| `cgroup_sock_ipv4` | Allow IPv4 sockets, deny IPv6 sockets |

The compiler checks a read-only four-field prefix of Linux `bpf_sock`:
`bound_dev_if`, `family`, `type`, `protocol`, all `uint32`. Whole-context loads
and writes are rejected. The section requires that context pointer. This is a
source-checker restriction, not a new formal proof. The hook and section follow
the kernel's [program type table](https://docs.kernel.org/bpf/libbpf/program_types.html).

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples cgroup-live
```

`kernel-cgroup-check` is an alias. Results go to
`evaluation/results/kernel-cgroup.json`. A single example can be tested with
`sudo make -C evaluation/examples kernel-test EXAMPLE=cgroup_sock_udp`.
Each source includes full build, verifier-load, inspection and cleanup commands.
Bytecode, ELF and disassembly are saved under `evaluation/.build/objects`.

The runner needs writable cgroup v2 at `/sys/fs/cgroup` and BPF privileges.
For each policy it creates a unique temporary cgroup and moves only short-lived
child processes there. Twenty assertions per program check real IPv4 and IPv6 TCP/UDP socket creation:
before/after controls, repeated attached outcomes, and unaffected creation
outside the cgroup. Denials must be `EPERM`; other errors fail the test. Children
are reaped before the attachment is destroyed and the group is removed. The
shell remains in its original cgroup; no network interfaces are changed.
Ancestor policies may cause baseline controls to fail. Socket creation policy
does not filter existing sockets or implement connect/bind/address restrictions.
IPv6 must be enabled: unavailable families fail the baseline controls rather
than silently skipping them. Other cgroup hook families remain unsupported.

All four examples passed the verifier and all 80 IPv4/IPv6 live checks on Linux
7.0.0-42-generic; see the [expanded cgroup report](results/archive/kernel-cgroup-ipv4-ipv6.json).
Source, object and compiler hashes match the current files. Denied socket
creation returned EPERM. The UDP policy allowed TCP and denied UDP in both
families; the IPv4-only policy allowed IPv4 and denied IPv6 for both socket types.
Outside-cgroup and post-detachment controls passed, and cleanup completed
without errors. The earlier [IPv4 report](results/archive/kernel-cgroup.json)
is preserved separately. Unprivileged checks validate program and attach
metadata, not kernel execution. To repeat the expanded checks, run
`sudo make -C evaluation/examples cgroup-live`. Full `kernel-check` includes
these temporary cgroup attachments as well.

## Raw syscall tracing and observation

[raw_syscall_count](examples/raw_syscall_count.bpl) counts a configured syscall
for one host process. [syscall_histogram](applications/syscall_histogram.bpl)
counts syscall IDs 0–255 for one host process. Both use per-CPU array maps and
`bpf_get_current_pid_tgid`, with scoped attachment to `raw_tracepoint/sys_enter`.
The context exposes only the scalar syscall ID: reading the reserved register
pointer, copying the whole context, and writing the context are rejected.
These source-checker restrictions are not a new formal soundness proof.

The finished objects, raw bytecode and disassembly are in `.build/objects`.
Each source includes its complete compile/load/observe/cleanup guide. To rebuild
and then run the 15 live-event assertions:

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples trace-live
```

`kernel-trace-check` is an alias. The runner loads through the kernel verifier,
attaches, triggers real getpid/getuid syscalls, checks map-count changes, and
closes the attachment. Tests include unselected syscalls, changing the selected
syscall, PID filtering, and before-attach/after-detach controls. Results go to
`evaluation/results/kernel-tracing.json`. No tracefs mount is required.

To observe an existing process, replace 1234 with its host TGID:

```sh
sudo make -C evaluation/examples trace-observe PID=1234 DURATION=5
```

This prints nonzero syscall counts and saves `evaluation/results/trace-observe.json`.
The observation lasts 1–60 seconds and detaches before reading the map. An idle
process may produce zero events; an observation is not a passing test assertion.
The current fixtures require Linux x86_64 (getpid=39, getuid=102) and host TGIDs
from the initial PID namespace, not container-local PID numbers. The histogram
omits syscall IDs above 255 and does not inspect syscall arguments. Return zero
from these tracing programs does not allow or deny syscalls. Ordinary tracepoints,
probes, BTF tracing, and typed event streaming remain future work.

## Typed maps and observable kernel state

Five new examples use modern BTF map definitions emitted directly by the BeePL
compiler. No C shim, clang compilation, legacy map definitions, or handwritten
object repair is required. The supported profile uses `uint32` keys and `ulong`
values in hash, array and per-CPU array maps, with 1–65536 entries.

```text
#section .maps
struct counts {
  map_type : uint32[6], key : uint32, value : ulong,
  max_entries : uint32[1]
}
```

The array bounds on `map_type` and `max_entries` encode declaration constants,
not stored arrays: kinds 1, 2 and 6 mean hash, array and per-CPU array. Fields must
appear in the shown order. Source handles are opaque and may only be passed by
name to map helpers; aliasing, indexing and shadowing are rejected. The internal
array representation decays to a pointer at the helper-call ABI boundary.

Lookup takes a `uint32*` key and returns `oulong*`; match `some`/`none` before
using the value. Update takes a `ulong*` value and `ulong` flags; update/delete
return signed `long` errors. Lookup requires `read, io`; update/delete require
`write, io`. The source checker and extracted checker agree on these signatures.
The BTF emission and source-level handle restrictions remain part of the trusted
compiler boundary; this is not a completed map-lifetime/soundness proof.

| Example | Passing kernel assertions |
| --- | --- |
| `xdp_map_counter` | Per-CPU array starts at zero, then totals 1–5 after five packets |
| `xdp_map_bounds` | Out-of-range array lookup takes the `none` branch |
| `xdp_map_update` | Insert hash key 7 with 42; replace userspace value 99 with 42 |
| `xdp_map_delete` | Missing key fails; seeded key deletes successfully; second delete fails |
| `xdp_map_config` | Userspace changes array value; zero passes and nonzero drops |

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples kernel-map-check
sudo make -C evaluation/examples map-observe
```

**All 15 map kernel cases passed** on Linux 7.0.0-42-generic, including actual
map readback. See the [archived map report](results/archive/kernel-maps.json).
Source, object and compiler hashes match the tested artifacts. The separate
[counter observation](results/archive/map-counter.json) also passed, showing
totals 1, 2, 3, 4, 5. At the map milestone, the packet/map collection had 40 kernel-tested programs and 250
passing kernel cases, plus the existing 25 socket/TC live checks. The repeated
counter observation is additional evidence for the same five counter cases.
`kernel-map-check` writes new runs to `results/kernel-maps.json`. `map-observe`
prints counter totals after five synthetic kernel executions and writes
`results/map-counter.json`; it does not attach to an interface. Both release the
programs and maps when done. The smoke interpreter does not support map
relocations/helper behavior: reports explicitly say `emulation=not_supported`.
Unprivileged checks use libbpf to open each ELF and validate kind, key/value sizes
and capacity; these checks are not verifier or execution results.

For persistent state you can inspect repeatedly:

```sh
mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
sudo make -C evaluation/examples map-load EXAMPLE=xdp_map_counter
sudo make -C evaluation/examples map-dump EXAMPLE=xdp_map_counter
sudo make -C evaluation/examples run EXAMPLE=xdp_map_counter
sudo make -C evaluation/examples map-dump EXAMPLE=xdp_map_counter
sudo make -C evaluation/examples map-unload EXAMPLE=xdp_map_counter
```

Each source includes these commands plus optional test-interface attachment and
cleanup. The configuration example also gives literal `bpftool map update`
commands. The ELF `.o` contains BTF and map relocations; `.bin` alone cannot load
this program. Inspect BTF with `bpftool btf dump file <object.o> format raw`.

The per-CPU counter avoids cross-CPU shared increments. Reading all CPU slots is
not a globally atomic snapshot while traffic is active. Shared-map atomic
operations, lock/lifetime rules, generic key/value structs, map-in-map, LRU and
other map kinds are still outside this profile. See the Linux
[array/per-CPU map documentation](https://docs.kernel.org/bpf/map_array.html)
and [BTF specification](https://docs.kernel.org/bpf/btf.html).

## TC traffic control and metadata mutation

The `tc` section produces a SCHED_CLS direct-action program. TC returns
`0 = TC_ACT_OK` and `2 = TC_ACT_SHOT`; these differ from XDP and socket returns.
The examples use Linux `__sk_buff` metadata with Ethernet included in `len`.

| Example | Behavior |
| --- | --- |
| `tc_pass`, `tc_drop` | Unconditional pass/drop |
| `tc_ipv4` | Pass IPv4, drop other EtherTypes |
| `tc_length` | Pass frames through 80 bytes; reject larger frames |
| `tc_mark` | Select skb mark 42; test-run supplies several marks |
| `tc_host` | Change packet type to PACKET_HOST and read back the result |
| `tc_type_error` | Assert invalid type 7 gives -EINVAL and leaves metadata unchanged |

The new typed `bpf_skb_change_type` helper takes `struct __sk_buff*` and `uint32`,
returns `long`, and requires `write, io` effects. The source checker restricts it
to TC entry points, including calls through other functions. No arbitrary struct
field assignment or packet-byte mutation is added. See the Linux
[helper implementation](https://github.com/torvalds/linux/blob/master/net/core/filter.c)
and [TC action constants](https://github.com/torvalds/linux/blob/master/include/uapi/linux/pkt_cls.h).

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples kernel-tc-check
sudo make -C evaluation/examples tc-live
```

`kernel-tc-check` loads saved objects and asserts 23 cases, covering protocol,
length boundaries, supplied marks, mutation and helper errors. It writes
`results/kernel-tc.json`. Every example includes manual load, inspect, run and
unload commands; those targets select the correct section and program type.

`tc-live` creates two uniquely named network namespaces, connects them with a
veth pair and uses fixed neighbors to separate IPv4 filtering from ARP. It runs
three pings with each of `tc_pass`, `tc_drop` and `tc_ipv4` attached at receiver
ingress, plus successful before/after controls. It prints REPLY/NO REPLY and
records ping output and TC filter statistics in `results/tc-live.json`. It does
not modify existing interfaces. Namespace deletion releases the veth pair and
filters; cleanup failures make the run fail and identify the remaining namespaces.
It requires root, iproute2 (`ip`, `tc`), `ping`, network namespaces and veth support.
The privileged live run passed all 15 checks. Source, object and compiler hashes
match the current artifacts. The saved TC output identifies the attached programs
and their JIT status; this kernel output did not include packet counters.

Helper calls exposed uninitialized callee-save spills in the backend's entry
prologue. The eBPF assembly expansion now initializes spilled r6-r9 registers at
recognized XDP/socket/TC entry points before those spills, retaining ordinary
subprogram calling conventions. The strict interpreter still rejects uninitialized
reads. This expansion is part of the existing unverified backend boundary; no new
axioms or admitted proofs were added. The isolated builder also invalidates copied
source timestamps correctly so an incremental build cannot silently use stale code.

## Socket filters and visible kernel behavior

The compiler now preserves ordinary context pointer types rather than forcing
all entry points to `xdp_md*`. The optional BeePL XDP bytes wrapper still lowers
to the native XDP context. Socket and TC entry points require `struct __sk_buff*`;
these examples declare its first five uint32 fields in Linux UAPI order and read
only `len` and `protocol`. This is a checked example layout, not automatic layout
validation for arbitrary user-defined context structs. Packet reads through
socket helpers and socket `Pbytes` parsing remain unsupported by this collection.

| Example | Behavior |
| --- | --- |
| `socket_accept` | Return UINT32_MAX: accept the whole packet for this socket |
| `socket_drop` | Return zero: reject delivery to this socket |
| `socket_ipv4` | Select IPv4 using protocol metadata |
| `socket_length` | Accept skb lengths at least 32 bytes |

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples kernel-socket-check
sudo make -C evaluation/examples socket-live
```

The first privileged command asserts 12 synthetic kernel cases, including both
sides of the length boundary. Results go to `results/kernel-socket.json`.
Socket test-run receives Ethernet frames but exposes skb length minus the
14-byte Ethernet header. It returns a capture byte count, not an XDP action,
and restores a zeroed Ethernet header in its output. The runner checks this
output explicitly. See the [kernel test-run implementation](https://github.com/torvalds/linux/blob/master/net/bpf/test_run.c).

`socket-live` attaches the compiled accept/drop filters to temporary IPv4 UDP
sockets on loopback. It prints **RECEIVED** for accepted messages and **NO DELIVERY
(timeout)** for filtered messages. Each filter has three attached trials plus
successful deliveries before attachment and after detachment. A mismatch exits
nonzero. `results/socket-live.json` records observations and artifact hashes.
There are no interface changes or persistent attachments; sockets and programs
close on success and failure. Socket filtering affects the receiving socket,
not host-wide traffic; see [Linux socket filtering](https://docs.kernel.org/networking/filter.html).

Every new source includes compile, verifier, pin/load, inspect, run, live-test and
cleanup commands. Existing Makefile targets choose `socket_filter` for these
objects. Interface attach/detach targets reject socket programs with a helpful
message. Raw `.bin` files now extract the appropriate `socket` or `xdp` section.

## Packet parsing without pointer arithmetic

BeePL source uses `Pbytes` with a scalar header schema. The compiler generates
`data + schema_size <= data_end` checks before field loads. There is no source
pointer addition, subtraction, or integer-to-pointer cast; rejection tests cover
these operations. Inspect the saved `.disasm` files to see the generated offsets.

| Example | Schema size | Behavior |
| --- | --- | --- |
| `xdp_eth_ipv4` | 14 | Select IPv4 EtherType |
| `xdp_ipv4_ttl` | 34 | Select fixed-header IPv4 with TTL above 1 |
| `xdp_ipv4_fragments` | 34 | Reject IPv4 fragments; allow DF |
| `xdp_udp_dns` | 42 | Select unfragmented fixed-header IPv4/UDP destination port 53 |
| `xdp_tcp_syn` | 54 | Select unfragmented fixed-header IPv4/TCP SYN without ACK |

These are header selection demonstrations, not complete protocol validators or
production firewalls. They do not validate IP total length, checksums, or payloads.
These five examples do not parse VLAN layouts or IP/TCP options. Separate
VLAN/QinQ examples above handle fixed tag layouts. Each pattern starts at the packet
start; it does not advance a cursor. Dynamic header traversal needs an additional
checked cursor/slicing language operation. Multibyte comparisons currently use
little-endian representations of wire bytes.

The five examples include 150 cases: matching/nonmatching fields, exact schema
lengths, and every truncated length from Ethernet's 14-byte minimum through the
schema boundary. Linux XDP test-run rejects inputs shorter than 14 bytes itself.
Each source has the full compile, verify, load, inspect, attach and cleanup guide.
Build normally, then run only the new examples with:

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples kernel-packet-check
```

The latter loads saved objects, checks expected actions and unchanged PASS packets,
and releases programs without attaching to an interface. Its separate report is
`evaluation/results/kernel-packet-parsing.json`; it preserves the baseline report.

## Run from the repository root

```sh
make -C evaluation/examples check
sudo make -C evaluation/examples kernel-check
```

Build prerequisites are the project's Coq/OCaml/Menhir dependencies, **GNU make
4.3 or later**, Python 3, and LLVM tools (`llvm-mc`, `llvm-readelf`,
`llvm-objdump`, `llvm-objcopy`). Kernel execution additionally needs Linux with BPF and XDP test
run support, the `libbpf` shared library, and sufficient BPF/network capabilities
(usually root). No Python packages, clang, libbpf development headers, or bpffs
mount are required. The current machine already has the required runtime
library and LLVM tools.

The runner exits nonzero on a failed build, unexpected acceptance/rejection,
blocked kernel load, or incorrect return value. Kernel mode uses libbpf to load
objects and `BPF_PROG_TEST_RUN` to execute synthetic packets. The two syscall
tracers instead attach temporarily to real raw syscall events and assert map counts. It does **not**
attach to a live network interface, pin objects, or change networking. File
descriptors are closed after each program, unloading it. XDP_PASS cases also
assert that the packet is unchanged. Capture stderr if you need libbpf's verifier
diagnostics:

```sh
sudo make -C evaluation/examples kernel-check 2> evaluation/results/kernel.log
```

See the [Linux kernel's test-run documentation](https://docs.kernel.org/bpf/bpf_prog_run.html)
for the distinction between ordinary test runs and live packet execution.
The ctypes binding follows the [libbpf API](https://libbpf.readthedocs.io/en/latest/api.html).

`--emulate` is an independent, deliberately limited instruction smoke interpreter.
It catches uninitialized registers/stack reads and exercises the emitted packet
loads and branches. It implements only the instructions used here; time and
random helpers are **stubbed**. It is neither the Linux verifier nor proof of
kernel acceptance. Emulation and kernel results have separate fields in reports.

To build or test one program:

```sh
make -C evaluation/examples build EXAMPLE=xdp_arithmetic
make -C evaluation/examples test EXAMPLE=xdp_arithmetic
sudo make -C evaluation/examples kernel-test EXAMPLE=xdp_arithmetic
```

`make` is the public interface; the existing Python build/test helpers run behind
it. Compilation itself invokes BeePL CompCert and LLVM. Every `.bpl` starts with
its own complete run guide, following the build/inspect/load/attach/observe/
cleanup organization of [your packet-count notes](https://github.com/swarnpriya/eBPF_notes/blob/main/eBPF_Koka/packet_count/packet_count_eBPF.md).
The comments distinguish actual kernel results from expected output. `make help`
(in `evaluation/examples`) lists all targets. Live attachment is optional;
`kernel-test` needs no network attachment or bpffs mount.

## Programs

| Source | Behavior | Test coverage |
| --- | --- | --- |
| `examples/xdp_pass.bpl` | Return XDP_PASS | IPv4/IPv6 EtherTypes |
| `examples/xdp_drop.bpl` | Return XDP_DROP | IPv4/IPv6 EtherTypes |
| `examples/xdp_queue.bpl` | Pass queue zero | Default test-run context |
| `examples/xdp_arithmetic.bpl` | Divide by the queue index, safely | Zero-divisor path; emitted guard |
| `examples/xdp_loop.bpl` | Increment a local reference four times | Inclusive bounded loop, stack mutation |
| `examples/xdp_loop_limits.bpl` | Terminate at uint32 maximum/zero endpoints | Stops before overflow/underflow |
| `examples/xdp_loop_empty.bpl` | Skip loops with reversed bounds | Both directions |
| `examples/xdp_array.bpl` | Initialize/read an array | Three integer elements |
| `examples/xdp_cast.bpl` | Narrow and widen an integer | 511 becomes uint8 255 |
| `examples/xdp_boolean.bpl` | Negate a boolean | Default queue condition |
| `examples/xdp_shift.bpl` | Guard an invalid shift | Shift by 32 on uint32 |
| `examples/xdp_signed_div.bpl` | Signed division | -17 / 4 rounds to -4 |
| `examples/xdp_modulo.bpl` | Guard modulo by zero | Default queue zero |
| `examples/xdp_option_some.bpl` | Match then dereference | Non-null optional reference |
| `examples/xdp_option_none.bpl` | Handle an absent reference | None branch |
| `examples/xdp_clock.bpl` | Read monotonic time | Helper 5; nonzero time |
| `examples/xdp_random.bpl` | Pass/drop by the low random bit | Helper 7; 16 runs, either valid action |
| `applications/ipv6_guard.bpl` | Drop IPv6, pass other EtherTypes | IPv4, IPv6, ARP, exact Ethernet-header boundary |
| `applications/udp_port_filter.bpl` | Drop IPv4 UDP destination port 9999 | Allowed/blocked ports, TCP, IPv6, ARP, truncated headers, options, fragments, exact 42-byte boundary |

The application headers use scalar fields with actual wire offsets: Ethernet
is 14 bytes; the fixed Ethernet+IPv4+UDP schema is 42 bytes. Comparisons use
little-endian representations of network-order constants because this compiler
target is little-endian. This does not depend on an unresolved `htons` call.

The UDP policy deliberately drops all frames shorter than 42 bytes, IPv4 options,
and IPv4 fragments (except the don't-fragment flag). It passes non-IPv4 frames
of sufficient length and non-UDP IPv4 packets with the supported layout. It is
a fixed-layout policy demonstration, not a complete firewall: it does not parse
VLAN tags, IPv6 extension headers, validate checksums, or validate IP/UDP length
fields. Synthetic EtherType tests do not require valid higher-layer packets.
Linux XDP test-run requires at least an Ethernet header, so shorter-than-14-byte
frames are not sent to the kernel runner.

## Outputs and adding cases

- `.build/build.log`: compiler build log.
- `.build/objects/`: `.s` assembly, loadable `.o` ELF objects, `.bin` raw XDP
  instructions, `.disasm` listings, and compiler diagnostics. Use `.o` to load;
  raw `.bin` lacks the ELF metadata needed by bpftool.
- `results/latest.json`: compilation, emulation, and rejection outcomes.
- `results/kernel.json`: outcomes from your privileged run.
- `results/kernel-attempt.json` / `.log`: the unprivileged attempt on this machine.

Reports include source/object/compiler SHA-256 hashes, host kernel version,
expected/actual actions, and per-case results. Artifacts are ignored by Git.
A successful compilation additionally requires an ELF64 `EM_BPF` object with no
unresolved BPF helper relocation. Timing is the kernel's single-run measurement,
not a performance benchmark.

Add a `.bpl` under `examples` or `applications`, name its entry point after the
file stem, and add packet cases to `tools/run.py`. Rejection fixtures live in
`tests/reject`; their expected diagnostic substrings are in `tests/rejections.json`.
Keep both positive and negative tests when extending a language feature.

To compile one example manually:

```sh
evaluation/.build/compiler/ccomp -typecheck -bpfmap -c \
  -o /tmp/xdp_pass.o evaluation/examples/xdp_pass.bpl
```

The `.bpl` extension selects BeePL compilation. **`-beepl` exports a Rocq AST;
it does not generate eBPF bytecode.** `#ebpf` entry points now trigger the
extracted typechecker even without `-typecheck`.

## Relation to the paper and remaining work

The supplied `beepl.pdf` motivates nullable references, explicit effects, bounded
loops, safe byte-pattern matching, and compilation to BPF. This suite exercises
those mechanisms where implemented and records concrete gaps rather than
assuming the paper establishes implementation completeness.

This change fixes clean/parallel eBPF builds; comparisons returning `bool` in the
executable typechecker; empty-set variable membership used by loop checks; endpoint termination before overflow/underflow;
source-level field typing that preserves `bytes`; canonical identifier agreement
with extracted context/helper definitions; and initialization of both the header
and named fields in `Pbytes` lowering. It also fixes cast precedence and checks
function arity, optional field access, exhaustive option matches, byte-schema
field types, pointer returns, recursion in eBPF call graphs, and license-array
lengths. Helper replacement matches complete names and fails if its mapping is
missing. Unused external signatures are no longer emitted into every program.

The following still require design and implementation work:

1. **Broader maps and userspace data exchange.** The fixed uint32/ulong
   hash/array/per-CPU profile is implemented with BTF and 15 passing kernel tests.
   Generic key/value layouts, shared-state atomics, borrow/lifetime rules, more
   map kinds and ring buffers still need implementation and kernel validation.
2. **Hook/context coverage.** XDP, socket metadata and an initial TC metadata/helper subset are implemented. Tracepoint,
   kprobe, fentry, TC packet access/TCX, and other context ABIs need validated signatures and wrappers.
3. **Richer packet schemas.** This path currently accepts scalar header fields
   only and a struct pattern followed by a bytes fallback. Pointer deserialization
   is rejected. Fixed single/double VLAN tags are tested. Nested structures/arrays,
   advancing byte slices, variable headers, and writes need dedicated lowering
   and bounds-check tests.
4. **Remaining typechecker/proof gaps.** The executable checker still has legacy
   limitations, including annotated-variable lookup and pattern-binding contexts;
   effect lists use exact ordered equality. The source checker is part of the
   trusted boundary. Existing `Admitted` proofs remain in the BeePL development.
   Successful `make` checks the current development, including its admitted facts;
   it does not establish a completed end-to-end soundness theorem. No new axioms
   or admitted proofs were added for this work.
5. **Resource bounds and broader testing.** Acyclic calls and the bounded-loop
   example do not establish that every accepted program terminates within a
   kernel budget. Additional integer-width boundaries, stack/call-depth limits, helper
   availability by hook, and richer arithmetic need systematic testing. The 24 XDP programs passed kernel loading and their 200 tested
   cases on Linux 7.0.0-42-generic; this does not cover arbitrary programs or kernels.

See [READINESS.md](READINESS.md) for program-family coverage and release gates.
