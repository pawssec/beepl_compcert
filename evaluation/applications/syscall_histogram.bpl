(* RUN GUIDE: syscall_histogram
Count syscall numbers 0..255 for a selected host process.
Program family: raw tracepoint, attached to sys_enter. This observes events;
it does not allow/deny syscalls. Returning zero has no packet action meaning.
Kernel verification and live event checks are PENDING your privileged run.

Run commands from the repository root. Requires the existing compiler/LLVM,
libbpf and bpftool dependencies plus kernel BPF tracing privileges. The current
fixtures use Linux x86_64 syscall IDs: getpid=39 and getuid=102. The runner checks
architecture and invokes libc.syscall directly; it does not rely on a cached PID.
Use host TGIDs (initial PID namespace), not container-local PID numbers.

1. Compile/typecheck and save assembly, ELF, raw instructions and disassembly:
   make -C evaluation/examples build EXAMPLE=syscall_histogram
   file evaluation/.build/objects/syscall_histogram.o
   llvm-objdump -d evaluation/.build/objects/syscall_histogram.o
   bpftool btf dump file evaluation/.build/objects/syscall_histogram.o format raw
   Artifacts: evaluation/.build/objects/syscall_histogram.s, .o, .bin, .disasm
   The code section is raw_tracepoint/sys_enter; .o includes map relocations and
   BTF. Raw .bin bytes are not independently loadable. Unprivileged validation
   checks libbpf map metadata, not execution; tracing is not smoke-emulated.
2. Verify, attach, trigger actual syscalls, assert map counts, detach and unload:
   sudo make -C evaluation/examples kernel-test EXAMPLE=syscall_histogram
   Report: evaluation/results/syscall_histogram-kernel.json
   Test both the small example and histogram application together:
   sudo make -C evaluation/examples trace-live
   Equivalent: sudo make -C evaluation/examples kernel-trace-check
   Report: evaluation/results/kernel-tracing.json
   The test attaches briefly to the real sys_enter event, filters the runner's
   TGID, and prints before/after counter values. It checks PID filtering,
   selected syscall counts, configuration changes where applicable, and zero
   increments before attachment and after detachment. No tracefs mount needed.
3. Observe an existing application (histogram, both run guides show this target):
   ps -eo pid,comm
   Replace TARGET_PID with a host process ID from that list:
   sudo make -C evaluation/examples trace-observe PID=TARGET_PID DURATION=5
   While it runs, make that application perform work. It reports numeric syscall
   counts and saves evaluation/results/trace-observe.json. Duration is 1..60 s.
   The observation always uses syscall_histogram, not a pinned program below.
   Zero matching events can be legitimate; an observation is not a test pass.
4. Optional manual verifier load and instruction inspection (NO attachment):
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=syscall_histogram
   sudo make -C evaluation/examples inspect EXAMPLE=syscall_histogram
   sudo make -C evaluation/examples jited EXAMPLE=syscall_histogram
   Successful load confirms verifier acceptance; stop on any load error.
   A pinned program alone does not attach or collect events. Use trace-live or
   trace-observe for attachment and map observation. The packet 'run' target
   rejects tracing examples because it cannot generate these events.
5. Remove the optional manual program pin:
   sudo make -C evaluation/examples unload EXAMPLE=syscall_histogram
   trace-live/trace-observe own their separate program/map/attachment FDs and
   close them automatically, including on errors. Process exit also closes FDs.

Data layout: raw sys_enter arguments are (struct pt_regs *regs, long id).
The first eight bytes are reserved and may not be read or copied in this profile;
syscall_id is at byte offset 8. The source checker validates the exact layout.
Map counts is per-CPU; keys 0..255 = event counters; key 256 = host TGID.
Userspace sets configuration in every CPU slot and sums counter slots. Live
snapshots need not be globally atomic. The histogram intentionally excludes
syscalls numbered 256 or above and records no arguments or register contents.
This is raw-tracepoint support, not conventional tracepoint/kprobe/BTF tracing.
*)
#section .maps
struct counts {
  map_type : uint32[6], key : uint32, value : ulong,
  max_entries : uint32[257]
}
struct bpf_raw_sys_enter { reserved_regs : ulong, syscall_id : long }
#section license
let _license : int8[4] = "GPL"
#ebpf
#section raw_tracepoint/sys_enter
fun syscall_histogram (struct bpf_raw_sys_enter* ctx) : int32,
  io, alloc, read, io, read, alloc, read, io, read, write {
  if (ctx.syscall_id < (long)0) then 0 else
  if (ctx.syscall_id >= (long)256) then 0 else (
    let identity : ulong = bpf_get_current_pid_tgid() in
    let owner_key : uint32* = ref (uint32)256 in
    let owner_slot : oulong* = bpf_map_lookup_elem(counts, owner_key) in
    match owner_slot with
    | none -> 0
    | some owner ->
        if ((identity >> (ulong)32) != !owner) then 0 else (
          let key : uint32* = ref (uint32)ctx.syscall_id in
          let slot : oulong* = bpf_map_lookup_elem(counts, key) in
          match slot with
          | none -> 0
          | some counter -> let done : unit = counter := (!counter + (ulong)1) in 0
        )
  )
}
