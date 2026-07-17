PYTHON ?= python3
RUSTC ?= rustc

MIR_DUMP_DIR ?= mir_dump
SAXPY_SRC := examples/saxpy.rs
ATOMIC_SRC := examples/atomic_flag.rs

COQ_DIR := coq
PTX_DIR := target
SAXPY_PTX := $(PTX_DIR)/saxpy.ptx
ATOMIC_PTX := $(PTX_DIR)/atomic_flag.ptx

.PHONY: demo translate mir-saxpy mir-atomic ptx check-ptx translator-test translator-validation coq

demo: translate translator-test check-ptx translator-validation coq

translate: mir-saxpy mir-atomic
	@SAXPY_MIR=`ls -t $(MIR_DUMP_DIR)/saxpy.saxpy.*.PreCodegen.after.mir 2>/dev/null | head -n 1`; \
	if [ -z "$$SAXPY_MIR" ]; then \
	  echo "error: no saxpy PreCodegen MIR dump found" >&2; \
	  exit 1; \
	fi; \
	$(PYTHON) tools/mir2coq.py $$SAXPY_MIR coq/examples/saxpy_gen.v
	@ATOMIC_MIR=`ls -t $(MIR_DUMP_DIR)/atomic_flag.acquire_release.*.PreCodegen.after.mir 2>/dev/null | head -n 1`; \
	if [ -z "$$ATOMIC_MIR" ]; then \
	  echo "error: no atomic_flag PreCodegen MIR dump found" >&2; \
	  exit 1; \
	fi; \
	$(PYTHON) tools/mir2coq.py $$ATOMIC_MIR coq/examples/atomic_flag_gen.v

mir-saxpy:
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all $(SAXPY_SRC)

mir-atomic:
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all $(ATOMIC_SRC)

ptx:
	@mkdir -p $(PTX_DIR)
	$(RUSTC) --crate-type=lib --target nvptx64-nvidia-cuda \
		-C link-dead-code=yes -O --emit=asm $(SAXPY_SRC) -o $(SAXPY_PTX)
	$(RUSTC) --crate-type=lib --target nvptx64-nvidia-cuda \
		-C target-cpu=sm_70 -C link-dead-code=yes -O --emit=asm \
		$(ATOMIC_SRC) -o $(ATOMIC_PTX)

check-ptx: translate ptx tools/check_ptx.sh
	tools/check_ptx.sh

translator-test:
	$(PYTHON) tools/test_mir2coq.py

coq: translate
	$(MAKE) -C $(COQ_DIR) all

translator-validation: examples/atomic_bad.rs tools/mir2coq.py
	@mkdir -p $(MIR_DUMP_DIR)
	RUSTFLAGS="-Zunstable-options" $(RUSTC) --crate-type=lib -Z dump-mir=all examples/atomic_bad.rs
	@BAD_MIR=`ls -t $(MIR_DUMP_DIR)/atomic_bad.*.PreCodegen.after.mir 2>/dev/null | head -n 1`; \
	if [ -z "$$BAD_MIR" ]; then \
	  echo "error: no atomic_bad PreCodegen MIR dump found" >&2; exit 1; \
	fi; \
	if $(PYTHON) tools/mir2coq.py $$BAD_MIR coq/examples/atomic_bad_gen.v; then \
	  echo "ERROR: translator accepted an unsupported atomic ordering"; \
	  rm -f coq/examples/atomic_bad_gen.v; \
	  exit 1; \
	else \
	  echo "[ok] translator input validation rejected unsupported atomic orderings"; \
	fi
	@rm -f coq/examples/atomic_bad_gen.v
