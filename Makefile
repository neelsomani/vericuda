PYTHON ?= python3
RUSTC ?= rustc

MIR_DUMP_DIR ?= mir_dump
EXAMPLE_DIR := examples
COQ_DIR := coq
COQ_EXAMPLE_DIR := $(COQ_DIR)/examples

# Tests ending with _bad are expected to be rejected by the translator.
EXAMPLE_SRCS := $(wildcard $(EXAMPLE_DIR)/*.rs)
BAD_TEST_SRCS := $(filter %_bad.rs,$(EXAMPLE_SRCS))
GOOD_TEST_SRCS := $(filter-out $(BAD_TEST_SRCS),$(EXAMPLE_SRCS))

GOOD_TESTS := $(basename $(notdir $(GOOD_TEST_SRCS)))
BAD_TESTS := $(basename $(notdir $(BAD_TEST_SRCS)))
ALL_TESTS := $(GOOD_TESTS) $(BAD_TESTS)

MIR_STAMPS := $(ALL_TESTS:%=$(MIR_DUMP_DIR)/%.stamp)
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

$(MIR_DUMP_DIR)/%.stamp: $(EXAMPLE_DIR)/%.rs
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all $<
	@touch $@

$(COQ_EXAMPLE_DIR)/%_gen.v: $(EXAMPLE_DIR)/%.rs tools/mir2coq.py $(MIR_DUMP_DIR)/%.stamp
	@mkdir -p $(dir $@)
	@FILE_BASE=$*; \
	for MIR_FILE in $(MIR_DUMP_DIR)/$*.*.PreCodegen.after.mir; do \
	  if [ ! -e "$$MIR_FILE" ]; then \
	    continue; \
	  fi; \
	  MIR_BASE=$$(basename "$$MIR_FILE"); \
	  ENTRY_NAME=$$(printf "%s" "$$MIR_BASE" | cut -d. -f2); \
	  if [ "$$ENTRY_NAME" = "$$FILE_BASE" ]; then \
	    OUT_FILE=$@; \
	  else \
	    OUT_FILE="$(COQ_EXAMPLE_DIR)/$*_$$ENTRY_NAME_gen.v"; \
	  fi; \
	  if $(PYTHON) tools/mir2coq.py $$MIR_FILE $$OUT_FILE; then \
	    echo "[ok] translated $$ENTRY_NAME from $* -> $$OUT_FILE"; \
	  else \
	    echo "error: translator failed for $* ($$ENTRY_NAME)" >&2; \
	    rm -f $$OUT_FILE; \
	    exit 1; \
	  fi; \
	done;

bad-test-%: $(EXAMPLE_DIR)/%.rs tools/mir2coq.py $(MIR_DUMP_DIR)/%.stamp
	@for MIR_FILE in $(MIR_DUMP_DIR)/$*.*.PreCodegen.after.mir; do \
	  if [ ! -e "$$MIR_FILE" ]; then \
	    continue; \
	  fi; \
	  MIR_BASE=$$(basename "$$MIR_FILE"); \
	  ENTRY_NAME=$$(printf "%s" "$$MIR_BASE" | cut -d. -f2); \
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
	rm -rf $(MIR_DUMP_DIR) $(COQ_EXAMPLE_DIR)