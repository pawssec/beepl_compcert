# BeePL readiness for eBPF

**Not ready for all kinds of eBPF programs.** Kernel evidence currently covers
24 XDP programs (200 cases), four socket filters (12 cases), and accept/drop
socket delivery (10 live checks), on Linux 7.0.0-42-generic. Reports are retained
under [results/archive](results/archive). Their previously tested object files remain unchanged;
the compiler identity has changed. Seven TC programs passed all 23 kernel cases, bringing the total to 35 programs
and 235 passing kernel cases. TC live ingress also passed 15 checks across pass, drop and IPv4 selection,
with successful before/after controls and complete cleanup. Five typed-map programs also passed all 15 kernel-state cases, including
userspace readback and configuration changes. At the map milestone, coverage reached 40 kernel-tested
programs and 250 passing kernel cases, plus 25 live checks. Map programs are not
emulated. The separate counter observation repeated its five cases successfully.

The collection now has 48 kernel-tested programs. Both raw syscall tracers
passed the verifier and all 15 live-event checks, including syscall selection,
PID filtering and before/after attachment controls; see the
[tracing report](results/archive/kernel-tracing.json). Its
source and object hashes match the tested files; the archived report retains
the compiler hash used for that run. Total coverage is 305 packet/map cases
and 120 live checks, including the 80 cgroup checks below. All 43 rejection tests and
33 harness tests pass; all 290 userspace instruction cases pass.

All four socket-create cgroup examples passed verifier loading and all 80 live
checks on Linux 7.0.0-42-generic. Both IPv4 and IPv6 TCP/UDP paths were exercised.
Denials returned EPERM; outside-cgroup and post-detachment controls passed,
and cleanup completed without errors. Source, object and compiler hashes match
the current files; see the [expanded cgroup report](results/archive/kernel-cgroup-ipv4-ipv6.json).
The earlier 30-case IPv4 report remains archived, but is not added again to the
coverage total. Repeat with `sudo make -C evaluation/examples cgroup-live`.

All 48 programs (45 examples and three applications) now have passing kernel
evidence. Both VLAN/QinQ classifiers passed verifier loading and all 55 cases,
including packet-preservation checks, on Linux 7.0.0-42-generic. Source, object
and compiler hashes match the current files; see the
[archived VLAN report](results/archive/kernel-vlan.json). Repeat with
`sudo make -C evaluation/examples kernel-vlan-check`. These fixed tag layouts
do not add dynamic header traversal, packet mutation, or hardware-stripped VLAN
metadata support. The tested collection does not establish arbitrary eBPF support.

A new TC UDP load-balancer prototype raises the compiled collection to 49 programs
(45 examples, four applications). It adds fixed four-byte packet load/store
helpers and TC redirection. It passed verifier loading and all 14 live two-backend checks, including cleanup.
The first 16 packet cases passed; an undersized IPv4 fixture was then rejected
by the kernel test harness before BPF execution. The short-frame fixtures are
fixed. Rerun `sudo make -C evaluation/examples kernel-lb-check` for the full
44-case result; the application bytecode is unchanged. See [the application guide](LOAD_BALANCER.md).
Kernel execution evidence now covers 49 programs, though the load-balancer
packet suite remains incomplete. The previously reported totals cover the
original 48 programs; the new live run adds 14 passing checks. This prototype adds no NAT,
connection tracking, dynamic packet cursors, or production performance evidence.

## Language coverage in this collection

| Feature | Evidence |
| --- | --- |
| Scalar constants, conditions, booleans | pass/drop, queue, boolean |
| Integer widths and casts | cast |
| Unsigned division/modulo, zero guards | arithmetic, modulo |
| Signed division | signed_div |
| Invalid shift guard | shift |
| Local references and mutation | loop |
| Inclusive loops, reversed bounds, unsigned endpoints | loop, loop_empty, loop_limits |
| Fixed arrays | array; out-of-bounds rejection |
| Nullable references, exhaustive matching | option_some, option_none; invalid optional accesses rejected |
| Helper calls/effects | clock, random; undeclared effects rejected |
| Bounded scalar-header packet parsing | Ethernet, IPv4 TTL/fragments, UDP port, TCP flags; IPv6 guard and UDP filter applications |
| Unsafe constructs rejected | 43 fixtures: arity/types, recursion, pointer return, invalid schemas and others |

This is coverage of specific test cases, not a proof of every input or feature.
The instruction interpreter is limited, models three helpers, and cannot validate
kernel pointer provenance, helper contracts, or resource accounting.

## Program-family coverage

Linux distinguishes program types, attach types and ELF section names. The
families below organize that surface; they are not interchangeable aliases.
See the kernel's [program types and ELF sections table](https://docs.kernel.org/bpf/libbpf/program_types.html).

| Family | BeePL status / missing work |
| --- | --- |
| XDP packet processing | 26 packet-processing programs kernel-tested (255 cases), including fixed VLAN/QinQ layouts; no variable-header parser |
| Socket filters | Four programs kernel-tested (12 cases); accept/drop live-tested (10 checks); packet helpers and general context-layout validation remain |
| TC classifier/action, TCX | Seven SCHED_CLS programs passed 23 kernel cases; pass/drop/IPv4 live-tested (15 checks). Fixed-buffer packet copies, L2 rewriting and redirect are live-tested by the load balancer; the corrected packet suite awaits rerun; dynamic parsing and TCX remain |
| Raw tracepoints | Scalar `sys_enter` context, PID helper, counter and histogram implemented; Both programs verifier-accepted; all 15 live checks passed. Register pointers remain inaccessible |
| Ordinary tracepoints | Need separate context schemas, helper contracts and event tests |
| Kprobe/kretprobe, uprobe/uretprobe | Need architecture-correct register contexts and safe reads |
| Fentry/fexit/fmod_ret and iterators | Need BTF-aware signatures, typed attachment and context translation |
| Cgroup socket creation | Read-only scalar context and allow/deny/UDP policies implemented; all four programs passed the verifier and all 80 IPv4/IPv6 checks |
| Other cgroup socket/address/device/sysctl hooks | Need distinct context types, return conventions and attachment tests |
| Sockops, sk_msg, sk_skb, sk_lookup, reuseport | Need socket/map types, lifetime rules and integration tests |
| LSM | Need hook-specific BTF types, sleepable-helper restrictions and enforcement tests |
| Perf events | Need event setup, context mapping and sample observation |
| LWT/seg6, flow dissector, netfilter | Need their separate context and action semantics |
| struct_ops (including scheduler-related uses) | Need BTF-defined callback structs, registration and lifetime handling |

A first map profile now supports hash, array and per-CPU array declarations with
uint32 keys, ulong values, nullable lookup, update/delete and modern BTF metadata.
Five examples passed all 15 kernel-state assertions on the tested kernel. Generic layouts, shared-state atomics, borrow/lifetime rules, other map
kinds and ring buffers still need design and tests. Ring-buffer reservation,
submission and discard need explicit lifetime handling; see the
[kernel ring-buffer design](https://docs.kernel.org/bpf/ringbuf.html).

## Gates before calling a family ready

1. Define its context layouts, permitted operations, helper signatures and result
   conventions in the language and executable checker.
2. Compile representative applications without handwritten repair of emitted
   bytecode, unresolved helpers, or bypassing typechecking.
3. Load on supported kernels and retain verifier diagnostics, kernel version,
   compiler/object hashes, and pass/fail results.
4. Execute positive, negative and boundary cases with observable assertions;
   attachment or verifier acceptance alone is insufficient.
5. Test resource limits and update the formal development. Source type soundness
   for coherent initialized states is checked separately with `make soundness-check`
   (see [PROOFS.md](../PROOFS.md)). Compiler correspondence, external-helper/kernel
   contracts, and general loader adequacy remain separate obligations; a successful
   `make` or source safety proof does not establish those claims.

To repeat the tracing checks, after `make -C evaluation/examples check`:

```sh
sudo make -C evaluation/examples trace-live
```

It loads both new objects through the verifier, temporarily attaches them to
`sys_enter`, triggers real syscalls and checks map-count changes, including
before/after controls. Attachment FDs are closed on completion or failure.
Results go to `evaluation/results/kernel-tracing.json`. The runner needs Linux
x86_64 and host TGIDs in the initial PID namespace. Full `kernel-check` now also
includes these temporary raw-tracepoint attachments; packet tests still use
synthetic packets without attaching to a network interface.

For a visible histogram of an existing process, use
`sudo make -C evaluation/examples trace-observe PID=1234 DURATION=5`, replacing
1234 with its host TGID. The report is `evaluation/results/trace-observe.json`;
zero observed events are possible and do not establish test success.

## Remaining implementation sequence

1. TC metadata/helper milestone validated: 23 kernel cases and 15 live checks.
   Retain these as regression tests while extending support.
2. Fixed-profile maps validated: 15 kernel-state cases and counter observation
   passed. Next extend generic layouts, atomics and map-value lifetime rules.
3. Add checked dynamic packet slices and mutation, with bounds, checksum and
   fragmentation cases; extend XDP and TC applications beyond fixed headers.
4. Raw syscall counter and histogram validated: all 15 live checks passed.
   Next add typed event output, ordinary tracepoints, architecture-dependent
   probes and BTF-based tracing.
5. Cgroup socket-create policies validated: all 80 IPv4/IPv6 live checks passed.
   Next extend cgroup address and socket-management hooks with
   distinct context, lifetime, helper and return-value contracts.
6. Cover the remaining program families in the table, including BTF/CO-RE,
   resource lifetimes, concurrency, kernel-version coverage and formal proof gaps.

A compiling entry point does not make a program family complete. Each milestone
needs representative applications, verifier acceptance and observable execution.
