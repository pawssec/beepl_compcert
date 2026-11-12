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

.PHONY: native-compiler bpf-compiler native-check escape-rejections option-match-native loop-temporaries-native parameter-temporaries-native nested-options-native nested-options-build nested-options-check nested-options-kernel-check
native-compiler:
	$(MAKE) -C $(ROOT) -j$(JOBS)

bpf-compiler:
	$(MAKE) -C $(EVAL)/examples compiler JOBS=$(JOBS)

native-check: nested-options-native option-match-native loop-temporaries-native parameter-temporaries-native binary-guards-native tail-call-native scoped-bindings-native loop-bounds-native

.PHONY: binary-guards-native
binary-guards-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/binary_guard_once $(NATIVE_OUT)/binary_guard_edges
	@$(NATIVE_OUT)/binary_guard_once
	@$(NATIVE_OUT)/binary_guard_edges
	@echo "binary_guard_once, binary_guard_edges: native execution passed"

# Require the escape diagnostic, not just any backend/typechecking failure.
# After an existing compiler build: make -C evaluation/tests -o native-compiler escape-rejections
escape-rejections: native-compiler
	@mkdir -p $(EVAL)/.build/escape-rejections
	@set -e; for source in $(EVAL)/tests/reject/ref_escape_*.bpl; do \
	  name=$$(basename "$$source" .bpl); \
	  log="$(EVAL)/.build/escape-rejections/$$name.log"; \
	  if $(CCOMP) -typecheck -S "$$source" -o "$(EVAL)/.build/escape-rejections/$$name.s" >"$$log" 2>&1; then \
	    echo "$$name: FAILED (compiler accepted escape)"; cat "$$log"; exit 1; \
	  fi; \
	  if ! grep -Fq 'Reference escape check failed' "$$log"; then \
	    echo "$$name: FAILED (wrong rejection diagnostic)"; cat "$$log"; exit 1; \
	  fi; \
	  echo "$$name: escape rejection passed"; \
	done

parameter-temporaries-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/parameter_fresh_temporaries
	@$(NATIVE_OUT)/parameter_fresh_temporaries
	@echo "parameter_fresh_temporaries: native execution passed"

loop-temporaries-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/loop_fresh_temporaries
	@$(NATIVE_OUT)/loop_fresh_temporaries
	@echo "loop_fresh_temporaries: native execution passed"

option-match-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/option_match_once
	@$(NATIVE_OUT)/option_match_once
	@echo "option_match_once: native execution passed"

nested-options-native: native-compiler
	@$(MAKE) --no-print-directory $(addprefix $(NATIVE_OUT)/,$(NATIVE_NAMES))
	@set -e; for name in $(NATIVE_NAMES); do "$(NATIVE_OUT)/$$name"; echo "$$name: native execution passed"; done

$(NATIVE_OUT):
	mkdir -p $@

$(NATIVE_OUT)/%.s: $(EVAL)/tests/accept/%.bpl $(CCOMP) | $(NATIVE_OUT)
	$(CCOMP) -typecheck -S $< -o $@

$(NATIVE_OUT)/%: $(NATIVE_OUT)/%.s
	$(CC) -no-pie $< -o $@

# Save artifacts before optional emulation, which currently lacks BPF calls.
# Compilation does not establish kernel verifier acceptance.
nested-options-build: bpf-compiler
	$(PYTHON) $(EVAL)/tools/run.py --nested-options --report $(EVAL)/results/nested-options-build.json
	@set -e; for name in $(BPF_NAMES); do \
	  $(BPFCC) -typecheck -bpfmap -S "$(EVAL)/tests/accept/$$name.bpl" -o "$(OUT)/$$name.s"; \
	  llvm-objcopy --dump-section "xdp=$(OUT)/$$name.bin" "$(OUT)/$$name.o"; \
	  llvm-objcopy --dump-section ".text=$(OUT)/$$name.text.bin" "$(OUT)/$$name.o"; \
	done

nested-options-check: nested-options-build
	$(PYTHON) $(EVAL)/tools/run.py --prebuilt --nested-options --emulate --report $(EVAL)/results/nested-options-userspace.json

# Intentionally has no compiler/build prerequisite: only loading and execution
# need sudo. The runner verifies artifact hashes and closes loaded descriptors.
nested-options-kernel-check:
	$(PYTHON) $(EVAL)/tools/run.py --nested-options --prebuilt --kernel --report $(EVAL)/results/nested-options-kernel.json

.SECONDARY:

.PHONY: tail-call-native
tail-call-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/tail_call_result
	@$(NATIVE_OUT)/tail_call_result
	@echo "tail_call_result: native execution passed"

.PHONY: scoped-bindings-native loop-bounds-native
scoped-bindings-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/option_match_shadow $(NATIVE_OUT)/option_scope_cases $(NATIVE_OUT)/underscore_binding_use
	@set -e; for name in option_match_shadow option_scope_cases underscore_binding_use; do "$(NATIVE_OUT)/$$name"; echo "$$name: native execution passed"; done

loop-bounds-native: native-compiler
	@$(MAKE) --no-print-directory $(NATIVE_OUT)/loop_long_bounds
	@$(NATIVE_OUT)/loop_long_bounds
	@echo "loop_long_bounds: native execution passed"
