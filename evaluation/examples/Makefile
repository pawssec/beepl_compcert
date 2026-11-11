# Build as your normal user. Only load/run/unload/kernel-test need sudo.
.DEFAULT_GOAL := all
ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../..)
EVAL := $(ROOT)/evaluation
OUT := $(EVAL)/.build/objects
PACKETS := $(EVAL)/.build/packets
CCOMP := $(EVAL)/.build/compiler/ccomp
PYTHON ?= python3
BPFTOOL ?= bpftool
JOBS ?= 4
IFACE ?=
PID ?=
DURATION ?= 5
EXAMPLE ?= xdp_pass
NAMES := $(basename $(notdir $(wildcard $(EVAL)/examples/*.bpl $(EVAL)/applications/*.bpl)))
PIN := /sys/fs/bpf/beepl_eval_$(EXAMPLE)
MAPDIR := /sys/fs/bpf/beepl_maps_$(EXAMPLE)
TRACE_NAMES := raw_syscall_count syscall_histogram
base_section = $(if $(filter $(TRACE_NAMES),$(1)),raw_tracepoint/sys_enter,$(if $(filter tc_%,$(1)),tc,$(if $(filter socket_%,$(1)),socket,xdp)))
section = $(if $(filter cgroup_sock_%,$(1)),cgroup/sock_create,$(call base_section,$(1)))
SECTION := $(call section,$(EXAMPLE))
BASE_PROGTYPE := $(if $(filter $(TRACE_NAMES),$(EXAMPLE)),raw_tracepoint,$(if $(filter tc,$(SECTION)),sched_cls,$(if $(filter socket,$(SECTION)),socket_filter,xdp)))

PROGTYPE := $(if $(filter cgroup_sock_%,$(EXAMPLE)),cgroup/sock,$(BASE_PROGTYPE))

ifeq ($(filter $(EXAMPLE),$(NAMES)),)
$(error Unknown EXAMPLE '$(EXAMPLE)'; choose one of $(NAMES))
endif

.PHONY: kernel-vlan-check cgroup-live kernel-cgroup-check all build compiler artifacts packets check test kernel-test kernel-check kernel-packet-check kernel-socket-check kernel-tc-check kernel-map-check kernel-trace-check trace-live trace-observe map-observe map-load map-dump map-unload tc-live socket-live load run inspect jited attach detach unload help
all: compiler
	@$(MAKE) --no-print-directory artifacts packets

build: compiler
	@$(MAKE) --no-print-directory $(OUT)/$(EXAMPLE).s $(OUT)/$(EXAMPLE).o $(OUT)/$(EXAMPLE).disasm $(OUT)/$(EXAMPLE).bin packets
	$(PYTHON) $(EVAL)/tools/run.py --program $(EXAMPLE) --emulate --report $(EVAL)/results/$(EXAMPLE)-userspace.json

compiler:
	$(PYTHON) $(EVAL)/tools/build_compiler.py -j $(JOBS)

artifacts: $(addprefix $(OUT)/,$(addsuffix .s,$(NAMES))) $(addprefix $(OUT)/,$(addsuffix .o,$(NAMES))) $(addprefix $(OUT)/,$(addsuffix .disasm,$(NAMES))) $(addprefix $(OUT)/,$(addsuffix .bin,$(NAMES)))

$(OUT):
	mkdir -p $@

$(OUT)/%.s: $(EVAL)/examples/%.bpl $(CCOMP) | $(OUT)
	$(CCOMP) -typecheck -bpfmap -S -o $@ $<

$(OUT)/%.s: $(EVAL)/applications/%.bpl $(CCOMP) | $(OUT)
	$(CCOMP) -typecheck -bpfmap -S -o $@ $<

$(OUT)/%.o: $(OUT)/%.s
	llvm-mc -triple bpf -filetype=obj -o $@ $<

$(OUT)/%.disasm: $(OUT)/%.o
	llvm-objdump -d $< > $@

$(OUT)/%.bin: $(OUT)/%.o
	llvm-objcopy --dump-section $(call section,$*)=$@ $<

# Preserve assembly and object files even though they are intermediate targets.
.SECONDARY:

packets:
	@mkdir -p $(PACKETS)
	PYTHONPATH=$(EVAL)/tools $(PYTHON) -c "from run import packet; from pathlib import Path; p=Path('$(PACKETS)'); (p/'ipv4.bin').write_bytes(packet()); (p/'ipv6.bin').write_bytes(packet(0x86dd)); (p/'udp9999.bin').write_bytes(packet(dport=9999))"

check: all
	$(PYTHON) $(EVAL)/tools/run.py --emulate --report $(EVAL)/results/examples.json
	$(PYTHON) -m unittest discover -s $(EVAL)/tests -v

# Selected example only. Does not rebuild the compiler under sudo.
test:
	$(PYTHON) $(EVAL)/tools/run.py --program $(EXAMPLE) --emulate --report $(EVAL)/results/$(EXAMPLE)-userspace.json

kernel-test:
	$(PYTHON) $(EVAL)/tools/run.py --program $(EXAMPLE) --prebuilt --kernel --report $(EVAL)/results/$(EXAMPLE)-kernel.json

kernel-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --report $(EVAL)/results/kernel.json

kernel-vlan-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --vlan-only --report $(EVAL)/results/kernel-vlan.json

kernel-packet-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --packet-parsing --report $(EVAL)/results/kernel-packet-parsing.json

kernel-socket-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --socket-only --report $(EVAL)/results/kernel-socket.json

cgroup-live kernel-cgroup-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --cgroup-only --report $(EVAL)/results/kernel-cgroup.json

socket-live:
	$(PYTHON) $(EVAL)/tools/socket_live.py

kernel-tc-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --tc-only --report $(EVAL)/results/kernel-tc.json

tc-live:
	$(PYTHON) $(EVAL)/tools/tc_live.py

kernel-map-check:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --maps-only --report $(EVAL)/results/kernel-maps.json

kernel-trace-check trace-live:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --trace-only --report $(EVAL)/results/kernel-tracing.json

trace-observe:
	@test -n '$(PID)' || { echo 'Specify PID=<host-process-id> and optionally DURATION=5'; exit 1; }
	$(PYTHON) $(EVAL)/tools/trace_observe.py --pid '$(PID)' --seconds '$(DURATION)'

map-observe:
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --kernel --program xdp_map_counter --report $(EVAL)/results/map-counter.json

map-load:
	@test -n '$(filter xdp_map_%,$(EXAMPLE))' || { echo 'Choose an xdp_map_ example'; exit 1; }
	@test -f $(OUT)/$(EXAMPLE).o || { echo 'Build without sudo first'; exit 1; }
	@mountpoint -q /sys/fs/bpf || { echo 'Mount bpffs first'; exit 1; }
	@test ! -e $(PIN) && test ! -e $(MAPDIR) || { echo 'Existing pins; use map-unload for this example first'; exit 1; }
	@mkdir $(MAPDIR)
	@$(BPFTOOL) -d prog load $(OUT)/$(EXAMPLE).o $(PIN) type xdp pinmaps $(MAPDIR) || { rm -f $(PIN) $(MAPDIR)/counts; rmdir $(MAPDIR); exit 1; }

map-dump:
	$(BPFTOOL) map dump pinned $(MAPDIR)/counts

map-unload:
	rm -f -- $(PIN) $(MAPDIR)/counts
	@if test -d $(MAPDIR); then rmdir $(MAPDIR); fi

load:
	@test -f $(OUT)/$(EXAMPLE).o || { echo 'Run make first, without sudo.'; exit 1; }
	@mountpoint -q /sys/fs/bpf || { echo 'Mount bpffs first: sudo mount -t bpf bpf /sys/fs/bpf'; exit 1; }
	@test ! -e $(PIN) || { echo 'Pin already exists; use make unload for this example first.'; exit 1; }
	$(BPFTOOL) -d prog load $(OUT)/$(EXAMPLE).o $(PIN) type $(PROGTYPE)

run:
	@test -z '$(filter cgroup_sock_%,$(EXAMPLE))' || { echo 'Socket creation needs live processes: use make cgroup-live'; exit 1; }
	@test -z '$(filter $(TRACE_NAMES),$(EXAMPLE))' || { echo 'Tracing needs real syscall events: use make trace-live'; exit 1; }
	@test -f $(PACKETS)/ipv4.bin || { echo 'Run make packets first, without sudo.'; exit 1; }
	$(BPFTOOL) -j prog run pinned $(PIN) data_in $(PACKETS)/ipv4.bin repeat 1

inspect:
	$(BPFTOOL) prog show pinned $(PIN)
	$(BPFTOOL) prog dump xlated pinned $(PIN)

jited:
	$(BPFTOOL) prog dump jited pinned $(PIN)

attach:
	@test '$(SECTION)' = xdp || { echo 'Use make socket-live or tc-live for this program family.'; exit 1; }
	@test -n "$(IFACE)" || { echo 'Specify IFACE=<test-interface>'; exit 1; }
	$(BPFTOOL) net attach xdpgeneric pinned $(PIN) dev "$(IFACE)"

detach:
	@test '$(SECTION)' = xdp || { echo 'The socket-live and tc-live runners clean up their attachments.'; exit 1; }
	@test -n "$(IFACE)" || { echo 'Specify IFACE=<test-interface>'; exit 1; }
	$(BPFTOOL) net detach xdpgeneric dev "$(IFACE)"

unload:
	rm -f -- $(PIN)

help:
	@echo 'sudo make kernel-vlan-check        Verify single VLAN and double-tagged QinQ filtering'
	@echo 'sudo make cgroup-live              Test socket creation in a disposable cgroup v2'
	@echo 'make                       Build compiler, all examples, bytecode and packets'
	@echo 'make build EXAMPLE=name     Build one example or application'
	@echo 'make check                 Compile, run userspace tests and rejection tests'
	@echo 'make test EXAMPLE=name     Test one example in userspace'
	@echo 'sudo make kernel-test EXAMPLE=name   Load, assert kernel results, unload'
	@echo 'sudo make kernel-check              Test the whole collection in kernel'
	@echo 'sudo make kernel-packet-check       Test the five new packet parsers in kernel'
	@echo 'sudo make kernel-socket-check       Verify and execute socket filter cases'
	@echo 'sudo make socket-live               Observe real loopback UDP accept/drop delivery'
	@echo 'sudo make kernel-tc-check           Verify TC actions, metadata and helper cases'
	@echo 'sudo make tc-live                   Observe TC filtering in a temporary namespace'
	@echo 'sudo make kernel-map-check          Verify map lookups, updates, deletion and state'
	@echo 'sudo make trace-live                Attach syscall tracers, trigger events, assert counts, detach'
	@echo 'sudo make trace-observe PID=1234 DURATION=5  Observe an existing host process'
	@echo 'sudo make map-observe               Print per-CPU counter totals after five kernel runs'
	@echo 'sudo make map-load EXAMPLE=xdp_map_counter  Load and pin program plus maps'
	@echo 'sudo make map-dump EXAMPLE=xdp_map_counter  Read pinned map values'
	@echo 'sudo make map-unload EXAMPLE=xdp_map_counter Remove program and map pins'
	@echo 'sudo make load EXAMPLE=name          Load and pin; verifier runs here'
	@echo 'sudo make run EXAMPLE=name           Execute a supplied packet in kernel'
	@echo 'sudo make inspect EXAMPLE=name       Show loaded program and instructions'
	@echo 'sudo make jited EXAMPLE=name         Show JIT machine code if available'
	@echo 'sudo make attach EXAMPLE=name IFACE=test-interface  Optional live attach'
	@echo 'sudo make detach EXAMPLE=name IFACE=test-interface  Detach before unload'
	@echo 'sudo make unload EXAMPLE=name        Remove this example pin'
	@echo 'Examples: $(NAMES)'
