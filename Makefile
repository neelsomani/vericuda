PYTHON ?= python3
RUSTC ?= rustc
CARGO ?= cargo

STAMP_DIR ?= stamps
EXAMPLE_DIR := examples
LOG_DIR := log
COQ_DIR := coq
COQ_EXAMPLE_DIR := $(COQ_DIR)/examples
CUQ_EXAMPLES_MANIFEST := $(EXAMPLE_DIR)/Cargo.toml
CUQ_EXAMPLES_DRIVER_SRCS := $(EXAMPLE_DIR)/build.rs $(EXAMPLE_DIR)/src/lib.rs $(EXAMPLE_DIR)/src/main.rs

# Tests ending with _bad are expected to be rejected by the translator.
EXAMPLE_SOURCES := $(wildcard $(EXAMPLE_DIR)/test/*.rs)
ALL_TESTS := $(notdir $(basename $(EXAMPLE_SOURCES)))
BAD_TESTS := $(filter %_bad,$(ALL_TESTS))
GOOD_TESTS := $(filter-out $(BAD_TESTS),$(ALL_TESTS))

MIR_STAMPS := $(ALL_TESTS:%=$(STAMP_DIR)/%.stamp)
COQ_GOOD_OUTPUTS := $(GOOD_TESTS:%=$(COQ_EXAMPLE_DIR)/%_gen.v)

.PHONY: demo translate tests good-tests bad-tests bad-test-% coq bad-demo

.SECONDARY: $(MIR_STAMPS)

translate: $(COQ_GOOD_OUTPUTS)

tests: good-tests bad-tests

good-tests: translate

bad-tests: $(BAD_TESTS:%=bad-test-%)

demo: tests coq

bad-demo: bad-tests

coq: translate
	$(MAKE) -C $(COQ_DIR) all

$(STAMP_DIR)/%.stamp: $(EXAMPLE_DIR)/test/%.rs $(CUQ_EXAMPLES_MANIFEST) $(CUQ_EXAMPLES_DRIVER_SRCS)
	@mkdir -p $(STAMP_DIR)
	@$(CARGO) run --manifest-path $(CUQ_EXAMPLES_MANIFEST) -- --target=$* 2>/dev/null
	@touch $@

$(COQ_EXAMPLE_DIR)/%_gen.v: $(EXAMPLE_DIR)/test/%.rs tools/mir2coq.py $(STAMP_DIR)/%.stamp
	@mkdir -p $(dir $@)
	@FILE_BASE=$*; \
	MIR_DIR="$(EXAMPLE_DIR)/mir_dumps/$*"; \
	for MIR_FILE in "$$MIR_DIR"/cuq_examples.$*-*.PreCodegen.after.mir; do \
	  if [ ! -e "$$MIR_FILE" ]; then \
	    continue; \
	  fi; \
	  MIR_BASE=$$(basename "$$MIR_FILE"); \
	  case "$$MIR_FILE" in *assert_kernel_parameter_is_copy*) \
	    echo "[skip] ignoring $$MIR_FILE"; \
	    continue; \
	  ;; \
	  esac; \
	  MODULE_AND_ENTRY=$$(printf "%s" "$$MIR_BASE" | cut -d. -f2); \
	  MODULE_NAME=$${MODULE_AND_ENTRY%%-*}; \
	  if [ "$$MODULE_NAME" != "$$FILE_BASE" ]; then \
	    continue; \
	  fi; \
	  ENTRY_NAME=$${MODULE_AND_ENTRY#*-}; \
	  if [ "$$ENTRY_NAME" = "$$FILE_BASE" ]; then \
	    OUT_FILE=$@; \
	  else \
	    OUT_FILE="$(COQ_EXAMPLE_DIR)/$*_$${ENTRY_NAME}_gen.v"; \
	  fi; \
	  if $(PYTHON) tools/mir2coq.py $$MIR_FILE $$OUT_FILE; then \
	    echo "[ok] translated $$ENTRY_NAME from $* -> $$OUT_FILE"; \
	  else \
	    echo "error: translator failed for $* ($$ENTRY_NAME)" >&2; \
	    rm -f $$OUT_FILE; \
	    exit 1; \
	  fi; \
	done;

bad-test-%: $(EXAMPLE_DIR)/test/%.rs tools/mir2coq.py $(STAMP_DIR)/%.stamp
	@MIR_DIR="$(EXAMPLE_DIR)/mir_dumps/$*"; \
	for MIR_FILE in "$$MIR_DIR"/cuq_examples.$*-*.PreCodegen.after.mir; do \
	  if [ ! -e "$$MIR_FILE" ]; then \
	    continue; \
	  fi; \
	  MIR_BASE=$$(basename "$$MIR_FILE"); \
	  MODULE_AND_ENTRY=$$(printf "%s" "$$MIR_BASE" | cut -d. -f2); \
	  MODULE_NAME=$${MODULE_AND_ENTRY%%-*}; \
	  if [ "$$MODULE_NAME" != "$*" ]; then \
	    continue; \
	  fi; \
	  ENTRY_NAME=$${MODULE_AND_ENTRY#*-}; \
	  OUT_FILE="$(COQ_EXAMPLE_DIR)/$*_bad_gen.v"; \
	  if $(PYTHON) tools/mir2coq.py $$MIR_FILE $$OUT_FILE; then \
	    echo "ERROR: translator accepted bad test $* ($$ENTRY_NAME)" >&2; \
	    rm -f $$OUT_FILE; \
	    exit 1; \
	  else \
	    echo "[ok] translator rejected bad test $* ($$ENTRY_NAME)"; \
	  fi; \
	  rm -f $$OUT_FILE; \
	done

clean:
	rm -rf $(STAMP_DIR) $(COQ_EXAMPLE_DIR) $(EXAMPLE_DIR)/target $(EXAMPLE_DIR)/mir_dumps $(LOG_DIR)/*

all: demo