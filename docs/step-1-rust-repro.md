# Rust MIR and PTX Reproduction Guide

The prototype targets Rust nightly `nightly-2025-03-02` and two curated inputs:
`examples/saxpy.rs` and `examples/atomic_flag.rs`.

## Prerequisites

```sh
rustup toolchain install nightly-2025-03-02
rustup target add nvptx64-nvidia-cuda --toolchain nightly-2025-03-02
rustup override set nightly-2025-03-02
```

## MIR and extraction

Run:

```sh
make mir-saxpy mir-atomic translate
```

The first two targets write `rustc -Z dump-mir=all` output under `mir_dump/`.
The extractor selects each function's `PreCodegen.after.mir` dump and writes
`coq/examples/saxpy_gen.v` and `coq/examples/atomic_flag_gen.v`.

The extractor deliberately does not model MIR control-flow graphs. It prints a
warning for every omitted `goto`, `switchInt`, assert/call edge, and loop
back-edge. For SAXPY, this means the generated Coq program contains one
straight-line copy of the loop body's memory operations, not the loop.

## PTX and correspondence check

Run:

```sh
make check-ptx
```

The target freshly emits both `target/*.ptx` files with
`-C link-dead-code=yes`, so the SAXPY function body is retained. The atomic
fixture additionally uses `-C target-cpu=sm_70`; that target is required for the
observed `ld.acquire.sys.u32` and `st.release.sys.u32` forms.

`tools/check_ptx.sh` checks:

- the SAXPY Coq artifact has two `TyF32` loads and one `TyF32` store, while the
  real (possibly unrolled) PTX contains `ld.f32` and `st.f32`;
- the atomic Coq artifact has acquire/release `TyU32` actions, while PTX contains
  `ld.acquire.sys.u32` and `st.release.sys.u32`.

Raw Rust pointers compile to generic-address `ld.f32`/`st.f32` on this
toolchain—not `ld.global.relaxed.f32`/`st.global.relaxed.f32`.

This is a syntactic check that the event layer tracks the compiler's observed
operation kinds. It is not a proof of extraction or compiler correctness.
