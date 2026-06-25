# VeriCUDA: A MIR-to-Coq Framework Targeting PTX for Formal Semantics and Verified Translation of Rust GPU Kernels

## Abstract

Rust's rise as a systems language has extended into GPU programming through projects like Rust-CUDA and rust-gpu, which compile Rust kernels to NVIDIA's PTX or SPIR-V backends. Yet despite Rust's strong safety guarantees, there is currently no formal semantics for Rust's GPU subset, nor any verified mapping from Rust's compiler IR to PTX's formally defined execution model.

This project introduces the first framework for **formally verifying the semantics of Rust GPU kernels** by translating Rust's Mid-level Intermediate Representation (MIR) into Coq and building a PTX-flavored event layer designed to line up with the Coq formalization of the PTX memory model (Lustig et al., ASPLOS 2019).
Rather than modeling Rust's ownership and borrowing rules directly, this work focuses on defining a mechanized operational semantics for a realistic subset of MIR and establishing memory-model soundness: defining a translation from MIR atomic and synchronization events to PTX-style events and proving per-event and per-trace shape correctness, as a stepping stone toward a full memory-model soundness theorem.

**VeriCUDA = CUDA + Rocq**.

## Motivation

1. **No formal semantics for Rust GPU code:**
   Although Rust compilers can emit GPU code via NVVM or SPIR-V, the semantics of such kernels are defined only informally through the compiler's behavior. There is no mechanized model of MIR execution for GPU targets.

2. **Disconnect between high-level Rust and verified GPU models:**
   NVIDIA's PTX memory model has a complete Coq specification, but that model has never been linked to a high-level language. Existing proofs connect only C++ atomics to PTX atomics.

3. **MIR as a verification sweet spot:**
   MIR is a well-typed SSA IR that preserves Rust's structured control flow and side-effect information while stripping away syntax. It provides a precise, implementation-independent level at which to define semantics and translate to Coq.

## Technical Approach

1. **Define a mechanized semantics for MIR:**
   Implement a Coq formalization of a small MIR-like subset sufficient to express simple GPU kernels: variable assignment, arithmetic, control flow, memory loads/stores, and synchronization intrinsics.

2. **Translate MIR to Coq:**
   Develop a translation tool that consumes `rustc`'s `-Z dump-mir` output for a curated fragment and produces corresponding Gallina definitions. The translation captures MIR basic blocks, terminators, and memory actions as Coq terms.

3. **Connect to PTX semantics:**
   Define a PTX-style event layer in Coq, together with a translation from MIR events to PTX events that matches PTX's acquire/release annotations, and prove per-event and per-trace shape properties. The intent is to plug this event layer into the existing Coq PTX memory model of Lustig et al in the next phase, with the long-term goal of proving:

   > If a MIR kernel is data-race-free under the MIR memory model, its compiled PTX program admits only executions consistent with the PTX memory model.

4. **Property verification:**
   Leverage this semantics later to verify kernel-level properties such as:

   * Absence of divergent barrier synchronization;
   * Preservation of sequential equivalence (e.g., for reductions or scans);
   * Conformance to the PTX consistency model under shared-memory interactions.

5. **Prototype toolchain:**
   Deliver a prototype that automatically translates Rust-CUDA kernels into Coq terms, evaluates their semantics within Coq, and interfaces with PTX proofs.

## Current Status

* ✓ A Coq formalization of Rust MIR semantics for GPU kernels using Rust nightly-2025-03-02.
* ✓ Per-event and per-trace structural correspondence proofs (`translate_trace_shape`) showing MIR events map correctly to PTX event constructors.
* ✓ A prototype translator generating Coq verification artifacts from Rust code.
* ⧖ Full semantic soundness theorem connecting MIR memory model to PTX memory model (planned).
* ⧖ Case studies on standard CUDA benchmarks (e.g., SAXPY, reductions) verifying barrier correctness and dataflow soundness (in progress).

## Future Work

While this first phase omits Rust's ownership and lifetime reasoning, the framework is designed to incorporate it later. Future extensions can integrate ownership types or affine resource logics into the MIR semantics, enabling end-to-end proofs of data-race freedom and alias safety.

This project establishes the missing formal bridge between Rust's compiler infrastructure and the only existing mechanized model of GPU execution.
By defining verified semantics for MIR and connecting it to PTX, it provides the foundation for future CompCert-style verified compilation of GPU code and opens the door to ownership-aware proofs of safety and correctness for massively parallel Rust programs.

## End-to-End Demo

Rebuild the MIR dumps, translate them into Coq, and check the traces/bridges with:

```
make demo
```

The target performs three steps:

1. `rustc -Z dump-mir=all` for `examples/saxpy.rs` and `examples/atomic_flag.rs` (writes into `mir_dump/`).
2. `tools/mir2coq.py` parses the `PreCodegen.after` dumps and regenerates `coq/examples/{saxpy,atomic_flag}_gen.v`.
3. `make -C coq all` type-checks the MIR semantics, the generated programs, and the MIR→PTX translation lemmas.

Afterwards you can inspect `coq/examples/*_gen.v` and re-run `Eval compute` queries found in `coq/MIRTests.v` to see the MIR event traces and their PTX images.

### Architecture at a Glance

```
examples/*.rs --rustc -Z dump-mir--> mir_dump/*.mir --tools/mir2coq.py--> coq/examples/*_gen.v
        \                                                                 |
         \--> target/*.ptx (optional)                                     v
           Coq build (MIRSyntax + MIRSemantics + Translate + Soundness) -> PTX event traces
```

### Reproduce the Pipeline

1. Ensure the Rust nightly and Coq toolchain are available:
   - `rustup toolchain install nightly-2025-03-02`
   - `rustup override set nightly-2025-03-02`
   - `opam install coq` (Coq ≥ 8.18)
2. In every new shell, activate the Coq switch so `coq_makefile` is on your `PATH`:

   ````
   eval "$(opam env)"
   ````

3. Run the end-to-end build:

   ```
   make demo
   make bad-demo
   ```

### MIR→PTX Mapping (MVP)

Refer to `docs/mapping-table.md` for the full table. In short:

- `TyI32`/`TyU32`/`TyF32` loads and stores become `EvLoad`/`EvStore` in PTX with
  `space_global`, relaxed semantics, and the matching `mem_ty` (`MemS32`,
  `MemU32`, `MemF32`).
- Acquire loads and release stores attach `sem_acquire`/`sem_release` and SYS
  scope, mirroring the observed `ld.acquire.sys.<ty>` and `st.release.sys.<ty>`.
- Barriers translate to `EvBarrier scope_cta`.

The translator (`coq/Translate.v`) and the docs stay in sync via helper
functions `mem_ty_of_mir` and `z_of_val`.

### Limitations (MVP)

- Global memory only; shared-memory scopes and bank conflicts are out of scope.
- Non-atomic accesses are relaxed and scope-less; only one acquire/release pair
  with SYS scope is modelled.
- Floating-point values are treated as raw IEEE-754 bit patterns (`Z` payloads);
  no reasoning about NaNs or rounding edge cases yet.
- Translator handles a curated subset of MIR (no arbitrary control flow, panic
  paths, or complex intrinsics).

### Next Steps

1. Extend the translator grammar to cover additional MIR statements
   (comparisons, guards, simple loops/barriers) while preserving determinism.
2. Enrich the PTX shim with reads-from / coherence relations from the PTX Coq
   model.
3. Define a MIR memory model and prove semantic soundness: the current
   `translate_trace_shape` theorem establishes structural correspondence only
   (events line up correctly). The missing piece is proving that MIR traces
   that are data-race-free under a MIR memory model produce PTX executions
   consistent with the PTX memory model's happens-before and coherence relations.
4. Integrate shared-memory scope tags and CTA-wide fences, then revisit
   atomics/fences beyond acquire-release.
