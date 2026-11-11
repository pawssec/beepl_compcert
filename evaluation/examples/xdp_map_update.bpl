(* RUN GUIDE: xdp_map_update
Hash map update: insert or replace key 7 with value 42.
Run from the repository root. Kernel verification/execution is pending your sudo
run. Requires the compiler/LLVM dependencies, libbpf, bpftool, and BPF privileges.

1. Compile through both typecheckers, assemble, and inspect map metadata:
   make -C evaluation/examples build EXAMPLE=xdp_map_update
   file evaluation/.build/objects/xdp_map_update.o
   llvm-objdump -d evaluation/.build/objects/xdp_map_update.o
   bpftool btf dump file evaluation/.build/objects/xdp_map_update.o format raw
   Saved .s, .o, .bin and .disasm files are in evaluation/.build/objects/.
   The .o includes BTF and map relocations; raw .bin bytes cannot be loaded alone.
   Userspace checks parse the map using libbpf without loading it. The smoke
   interpreter does NOT emulate maps; only kernel tests establish map behavior.
2. Verify and assert kernel actions plus userspace map readback:
   sudo make -C evaluation/examples kernel-test EXAMPLE=xdp_map_update
   Report: evaluation/results/xdp_map_update-kernel.json
   Whole map group: sudo make -C evaluation/examples kernel-map-check
   A successful load establishes verifier acceptance on this kernel only.
3. Watch a counter change after five synthetic kernel packet executions:
   sudo make -C evaluation/examples map-observe
   Expected counter totals: 1, 2, 3, 4, 5. This target uses xdp_map_counter.
   Report: evaluation/results/map-counter.json. It unloads automatically.
4. Manually pin this program AND its map for inspection:
   mountpoint -q /sys/fs/bpf || sudo mount -t bpf bpf /sys/fs/bpf
   sudo make -C evaluation/examples map-load EXAMPLE=xdp_map_update
   sudo make -C evaluation/examples inspect EXAMPLE=xdp_map_update
   sudo make -C evaluation/examples map-dump EXAMPLE=xdp_map_update
   sudo make -C evaluation/examples run EXAMPLE=xdp_map_update
   sudo make -C evaluation/examples map-dump EXAMPLE=xdp_map_update
   Expected initial run retval: 2 (XDP_PASS=2, XDP_DROP=1).
   Map observation: after a run, key 7 has value 42.
   Run again and dump again to see persistence within the same loaded map.
5. Optional real traffic attachment, only on an existing TEST interface:
   ip -brief link
   sudo make -C evaluation/examples attach EXAMPLE=xdp_map_update IFACE=TEST_IFACE
   sudo bpftool net show dev TEST_IFACE
   Generate traffic from a peer; read the pinned map using map-dump above.
   An interface may see background traffic: the counter is not limited to test packets.
   sudo make -C evaluation/examples detach EXAMPLE=xdp_map_update IFACE=TEST_IFACE
6. After detaching, remove both program and map pins:
   sudo make -C evaluation/examples map-unload EXAMPLE=xdp_map_update
   Removes only /sys/fs/bpf/beepl_eval_xdp_map_update and
   /sys/fs/bpf/beepl_maps_xdp_map_update/counts plus that empty directory.

Map declaration profile: map_type uint32[N] encodes the numeric map kind,
not a data array (1=hash, 2=array, 6=per-CPU array); max_entries uint32[N]
encodes capacity. Keys are uint32 and values ulong. The compiler emits modern
BTF map metadata and keeps handles opaque: no arithmetic, indexing or aliases.
Lookup returns oulong*: some/none matching is required before dereference.
Per-CPU counters avoid cross-CPU shared increments. Reads of live per-CPU totals
are snapshots, not globally atomic; shared-map atomic operations are not added.
*)
#section .maps
struct counts {
  map_type : uint32[1], key : uint32, value : ulong,
  max_entries : uint32[1]
}
struct xdp_md {
  _data : uint32, _data_end : uint32, _data_meta : uint32,
  _ingress_ifindex : uint32, _rx_queue_index : uint32, _egress_ifindex : uint32
}
#section license
let _license : int8[4] = "GPL"
#ebpf
#section xdp
fun xdp_map_update (struct xdp_md* ctx) : int32, alloc, alloc, write, io {
  let key : uint32* = ref (uint32)7 in
  let value : ulong* = ref (ulong)42 in
  let result : long = bpf_map_update_elem(counts, key, value, (ulong)0) in
  if (result == (long)0) then 2 else 1
}
