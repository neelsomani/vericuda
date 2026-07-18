# Fixed Eight-Thread Reduction

## Kernel model

`coq/Reduction.v` models one CTA with thread ids 0–7 and shared addresses 0–7.
Each thread stores its baked-in input, synchronizes, and executes three
statically unfolded rounds with strides 4, 2, and 1. Active thread `t` reads
addresses `t` and `t + stride`, writes address `t`, and then every thread emits
its shared barrier.

The v1 input vector uses distinct payloads: thread `t` stores
`VF32 (Z.of_nat t + 1)`, giving `1, …, 8`. `VF32` is a raw `Z` payload wrapper,
and `MIRSemantics.add_vals` adds those integers. The combining operation is the
development's existing payload addition; the determinism result is about
uniqueness of the combining tree, not about floating-point arithmetic. In
particular, this is not an IEEE-754 result.

`reduction_thread` contains `SFor "s" 3 reduction_round`.
`reduction_thread_unrolled` writes out all three iterations, and
`reduction_unrolls` proves the per-thread `StepForUnfold` reaches that residual
code.

## Barrier and source semantics

`PTXHB.matching_barriers` pairs CTA barriers by their zero-based per-thread
count. `PTXHB.bar` orders strict pre-barrier program order on one participant to
strict post-barrier program order on another. The supplied endpoint-inclusive
formula was not used: it creates mutual barrier edges, so every real round
violates happens-before irreflexivity;
`bar_endpoint_irreflexive_statement_false` formalizes the counterexample.
`barrier_overwrite_forbidden` demonstrates
that the corrected relation prevents an overwritten read.

`MIRRelaxed.split_first_barrier_blocked` uses a deterministic round schedule.
At the least completed-barrier count it runs all non-barrier work, then releases
waiting barriers in thread-list/id order. The main `RelaxedLoadShared` rule is
gate-free: it permits any earlier same-address, same-type shared store. The
separate `no_stale_shared_source` predicate and its regression remain useful
diagnostics, but are not premises of the transition relation. Stale completed
executions therefore exist; PTX consistency rejects overwritten sources.

The schedule is canonical: **“all executions” means all reads-from choices
under this fixed event order. Relaxation is in load sourcing only; there is no
action reordering or enumeration of alternate thread interleavings.** This is
not a general CUDA scheduler.

## Checked results

The concrete trace has 61 events:

- 8 input stores and 8 initial barriers;
- 12 memory events and 8 barriers at stride 4;
- 6 memory events and 8 barriers at stride 2;
- 3 memory events and 8 barriers at stride 1.

`barrier_round_structure` computes that filtering the trace leaves four
complete `[0; …; 7]` barrier rounds, and `reduction_barrier_uniform` proves the
translated trace satisfies the explicit uniformity predicate.

```coq
Theorem reduction_deterministic : forall final rf,
  relaxed_machine_steps reduction_initial_machine final rf ->
  all_done final ->
  consistent (translate_trace (mach_trace final)) rf ->
  mach_trace final = reduction_final_trace.

Corollary reduction_result_unique : forall final rf,
  (* the same premises *)
  mem_read (mach_shared final) 0 = Some (VF32 reduction_result).

Theorem reduction_determinism_needs_consistency :
  ~ (forall final rf,
      relaxed_machine_steps reduction_initial_machine final rf ->
      all_done final ->
      mach_trace final = reduction_final_trace).
```

`reduction_result` is `36`. The negative theorem constructs a completed run in
which the event-36 load reads the initial store at event 0 rather than the
post-barrier overwrite at event 18; its trace and result differ from the
canonical execution, and `reduction_stale_final_result` computes the stale
result as `31`. The positive proof uses its named consistency premise:
an executable overwrite witness is proved sound by applying
`PTXHB.no_hb_overwrite`, and each stale branch is eliminated through that
lemma. Thus determinism is not obtained by silently turning relaxed loads into
current-memory loads.

## Rust/PTX and empirical protocol

`examples/reduction.rs` has the same eight-lane control shape. The extractor
uses `--shared-param _1` to model its raw pointer as shared, and recognizes only
the curated `0..3u32` iterator/back-edge as `SFor`. The actual pinned NVPTX
backend emits four `bar.sync 0` instructions. Because the Rust parameter is
still a raw generic pointer, it emits generic `ld.f32`/`st.f32`, not
`ld.shared.f32`/`st.shared.f32`; `tools/check_ptx.sh` checks those real forms.

The standalone `bench/` programs provide the GPU protocol: reduce one million
deterministic floats 1,000 times with `atomicAdd` and with a fixed shared tree,
record atomic result bit patterns, and assert the tree result is bit-identical.
They are not part of `make demo`, because this environment does not assume CUDA
hardware. The verified Coq kernel is an 8-element model of this kernel's
synchronization structure; the benchmark demonstrates the phenomenon the
theorem is about, not a verified binary.

## Explicit v2 boundary

- General N/`NTHREADS` by induction on rounds.
- A global-to-shared staging phase.
- Divergence-freedom derived from source syntax.
- IEEE-754 semantics.
- While loops or dynamic bounds.
- Arbitrary scheduling instead of the canonical scheduler.
