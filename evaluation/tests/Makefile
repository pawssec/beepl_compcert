# New features stay here until privileged tests establish kernel acceptance.
.DEFAULT_GOAL := nested-options-native
ROOT := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../..)
EVAL := $(ROOT)/evaluation
NATIVE_OUT := $(EVAL)/.build/nested-options-native
OUT := $(EVAL)/.build/objects
CCOMP := $(ROOT)/ccomp
BPFCC := $(EVAL)/.build/compiler/ccomp
CC ?= cc
PYTHON ?= python3
JOBS ?= 4
NATIVE_NAMES := nested_option_cases nested_option_once nested_option_storage
BPF_NAMES := $(basename $(notdir $(wildcard $(EVAL)/tests/accept/xdp_nested*.bpl)))

.PHONY: native-compiler bpf-compiler nested-options-native nested-options-check nested-options-kernel-check
native-compiler:
	$(MAKE) -C $(ROOT) -j$(JOBS)

bpf-compiler:
	$(MAKE) -C $(EVAL)/examples compiler JOBS=$(JOBS)

nested-options-native: native-compiler
	@$(MAKE) --no-print-directory $(addprefix $(NATIVE_OUT)/,$(NATIVE_NAMES))
	@set -e; for name in $(NATIVE_NAMES); do "$(NATIVE_OUT)/$$name"; echo "$$name: native execution passed"; done

$(NATIVE_OUT):
	mkdir -p $@

$(NATIVE_OUT)/%.s: $(EVAL)/tests/accept/%.bpl $(CCOMP) | $(NATIVE_OUT)
	$(CCOMP) -typecheck -S $< -o $@

$(NATIVE_OUT)/%: $(NATIVE_OUT)/%.s
	$(CC) -no-pie $< -o $@

# Builds under the ordinary user and saves ELF, disassembly, assembly, bytecode,
# hash manifests, and the userspace instruction-test report.
nested-options-check: bpf-compiler
	$(PYTHON) $(EVAL)/tools/run.py --nested-options --emulate --report $(EVAL)/results/nested-options-userspace.json
	@set -e; for name in $(BPF_NAMES); do \
	  $(BPFCC) -typecheck -bpfmap -S "$(EVAL)/tests/accept/$$name.bpl" -o "$(OUT)/$$name.s"; \
	  llvm-objcopy --dump-section "xdp=$(OUT)/$$name.bin" "$(OUT)/$$name.o"; \
	done

# Intentionally has no compiler/build prerequisite: only loading and execution
# need sudo. The runner verifies artifact hashes and closes loaded descriptors.
nested-options-kernel-check:
	$(PYTHON) $(EVAL)/tools/run.py --nested-options --prebuilt --kernel --report $(EVAL)/results/nested-options-kernel.json

.SECONDARY:
