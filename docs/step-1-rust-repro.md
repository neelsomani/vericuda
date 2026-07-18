# Rust MIR and PTX Reproduction Guide

The prototype targets Rust nightly `nightly-2025-03-02` and three curated
inputs: `examples/saxpy.rs`, `examples/atomic_flag.rs`, and
`examples/reduction.rs`.

## Prerequisites

```sh
rustup toolchain install nightly-2025-03-02
rustup target add nvptx64-nvidia-cuda --toolchain nightly-2025-03-02
rustup override set nightly-2025-03-02
```

## MIR and extraction

Run:

```sh
make mir-saxpy mir-atomic mir-reduction translate
```

The first two targets write `rustc -Z dump-mir=all` output under `mir_dump/`.
The extractor selects each function's `PreCodegen.after.mir` dump and writes
`coq/examples/saxpy_gen.v`, `coq/examples/atomic_flag_gen.v`, and
`coq/examples/reduction_gen.v`.

The extractor deliberately does not model MIR control-flow graphs. It prints a
warning for every omitted `goto`, `switchInt`, assert/call edge, and loop
back-edge. For SAXPY, this means the generated Coq program contains one
straight-line copy of the loop body's memory operations, not the loop.

The one loop exception is the reduction fixture's exact rustc
Range/Iterator/back-edge shape for `0..3u32`. The extractor emits an `SFor`
with bound 3 and continues to warn that branch reconstruction inside the body
is pattern-driven. Dynamic or otherwise unrecognized loops remain loud and
omitted.

The reduction command passes `--shared-param _1`. `_1` is rustc's MIR local
for the raw `*mut f32` parameter; the flag propagates through derived pointers
and emits `SLoadShared`, `SStoreShared`, and `SBarrierShared`. This is a
modeling convention for the Coq fixture, not a claim that Rust's type system or
rustc places the raw pointer in CUDA shared memory.

## PTX and correspondence check

Run:

```sh
make check-ptx
```

The target freshly emits all three `target/*.ptx` files with
`-C link-dead-code=yes`, so the SAXPY function body is retained. The atomic
fixture additionally uses `-C target-cpu=sm_70`; that target is required for the
observed `ld.acquire.sys.u32` and `st.release.sys.u32` forms.

`tools/check_ptx.sh` checks:

- the SAXPY Coq artifact has two `TyF32` loads and one `TyF32` store, while the
  real (possibly unrolled) PTX contains `ld.f32` and `st.f32`;
- the atomic Coq artifact has acquire/release `TyU32` actions, while PTX contains
  `ld.acquire.sys.u32` and `st.release.sys.u32`.
- the reduction artifact has an `SFor`, modeled shared actions, and shared
  barriers, while the actual PTX contains four `bar.sync 0` operations, six
  generic `ld.f32` loads, and three generic `st.f32` tree stores.

Raw Rust pointers compile to generic-address `ld.f32`/`st.f32` on this
toolchain—not `ld.shared.f32`/`st.shared.f32` or
`ld.global.relaxed.f32`/`st.global.relaxed.f32`. The Coq shared-space routing is
therefore deliberately more specific than the pointer address space visible
in emitted PTX.

This is a syntactic check that the event layer tracks the compiler's observed
operation kinds. It is not a proof of extraction or compiler correctness.
