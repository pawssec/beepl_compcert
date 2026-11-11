(* RUN GUIDE: cgroup_sock_allow
Allow IPv4/IPv6 socket creation in the attached cgroup.
Hook: cgroup/sock_create. Return 1 allows creation; 0 rejects it with EPERM.
This is a socket creation policy, not packet filtering or a connect policy.
Existing sockets are unaffected. Current tests exercise IPv4 and IPv6 TCP and UDP.
The original IPv4 checks passed; the expanded IPv6 checks await your run.

Run from the repository root using the existing Coq/OCaml/LLVM dependencies.
Live tests require libbpf, root/BPF privileges, and writable cgroup v2 mounted
at /sys/fs/cgroup. Ancestor policies can affect results and cause a control failure.

1. Compile/typecheck and save assembly, ELF, raw instructions and disassembly:
   make -C evaluation/examples build EXAMPLE=cgroup_sock_allow
   file evaluation/.build/objects/cgroup_sock_allow.o
   llvm-objdump -d evaluation/.build/objects/cgroup_sock_allow.o
   Artifacts: evaluation/.build/objects/cgroup_sock_allow.s, .o, .bin, .disasm
   Use the ELF .o for loading: the section is cgroup/sock_create.
   Unprivileged checks validate ELF program/attach types, not kernel execution.
2. Load through the verifier, attach, assert real socket outcomes, detach/unload:
   sudo make -C evaluation/examples kernel-test EXAMPLE=cgroup_sock_allow
   Report: evaluation/results/cgroup_sock_allow-kernel.json
   Or test all four policies:
   sudo make -C evaluation/examples cgroup-live
   Equivalent: sudo make -C evaluation/examples kernel-cgroup-check
   Report: evaluation/results/kernel-cgroup.json
   Each program has twenty checks: before/after TCP+UDP controls, two repetitions
   of attached TCP+UDP outcomes, and outside-cgroup TCP+UDP controls for both
   IPv4 and IPv6. IPv6 must be enabled; unsupported families fail controls. Creation
   prints created=true; denial must report errno=1 (EPERM), not any other error.
   The runner creates a unique temporary cgroup, moves only its short-lived
   children there, reaps children, destroys its BPF link and removes the group.
   Your shell stays in its original cgroup. No interface changes or bpffs mount.
3. Optional manual verifier load and inspection (this does NOT attach):
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples load EXAMPLE=cgroup_sock_allow
   sudo make -C evaluation/examples inspect EXAMPLE=cgroup_sock_allow
   sudo make -C evaluation/examples jited EXAMPLE=cgroup_sock_allow
   Stop on load errors. Use cgroup-live for scoped attachment and observation;
   the packet 'run' target rejects this family.
4. Remove an optional manual pin:
   sudo make -C evaluation/examples unload EXAMPLE=cgroup_sock_allow
   The automated runner owns separate unpinned programs and cleans up on errors.

Context: first four uint32 fields of Linux bpf_sock at offsets 0,4,8,12:
bound_dev_if, family, type, protocol. The source checker enforces this prefix
and rejects whole-context loads and writes. No pointer arithmetic or mutation.
*)
struct bpf_sock_create {
  bound_dev_if : uint32, family : uint32, type : uint32, protocol : uint32
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section cgroup/sock_create
fun cgroup_sock_allow (struct bpf_sock_create* ctx) : int32, [] {
  1
}
