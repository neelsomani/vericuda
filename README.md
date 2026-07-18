# VeriCUDA: A Mechanized Rust-to-PTX Memory Model with a Deterministic Tree Reduction Theorem

VeriCUDA connects a small executable Rust-like IR to a hand-written PTX-style
event layer and establishes two concurrency-sensitive results. First, the
message-passing litmus test forbids `flag = 1, data = 0` when the flag handoff is
release/acquire, while an explicit consistent execution permits that outcome
when both flag accesses are relaxed. Second, an eight-thread shared-memory tree
reduction has a unique 61-event trace and result across completed consistent
executions. A mechanized stale-read execution breaks that determinism when the
consistency premise is removed, showing that the barrier-derived
happens-before constraints are essential to the reduction theorem.

This is not an end-to-end verifier and is not connected to the Coq PTX model of
Lustig et al. The repository is an intermediate milestone toward that
larger result.

## Checked contributions

1. An executable small-step semantics for a Rust-like statement fragment with
   loads, stores, atomics, distinct global/shared barriers, structured
   conditionals, sequences, thread ids, comparisons, shifts, and statically
   unfolded counted loops.
   `MIRRun.step_fun_sound` and `MIRRun.step_fun_complete` prove agreement between
   the executable step function and the inductive semantics.
2. An interleaving semantics with separate global and CTA-shared memories,
   whose
   traces contain `(thread-id, event)` pairs, plus a PTX-style layer with
   candidate reads-from, program order, release/acquire synchronization,
   happens-before, count-matched CTA-barrier synchronization, and a small
   consistency predicate.
3. Mechanized message-passing results across `coq/MP.v`,
   `coq/MPRealizable.v`, and `coq/MPCandidates.v`:

   ```coq
   Theorem mp_acqrel_forbids_weak : forall rfc,
     consistent mp_trace_acqrel_weak rfc ->
     ~ weak_outcome mp_trace_acqrel_weak rfc.

   Theorem mp_relaxed_permits_weak : exists rfc,
     consistent mp_trace_relaxed rfc /\
     weak_outcome mp_trace_relaxed rfc.

   Lemma mp_acqrel_realizable : exists m,
     machine_steps mp_initial_machine m /\
     mach_threads_all_done m /\
     Translate.translate_trace (mach_trace m) = mp_trace_acqrel_good.

   Theorem mp_candidates_exact : forall final rf,
     relaxed_machine_steps mp_initial_machine final rf ->
     all_done final ->
     rf 4 = Some 3 ->
     Translate.translate_trace (mach_trace final) = mp_trace_acqrel_good \/
     Translate.translate_trace (mach_trace final) = mp_trace_acqrel_weak.

   Theorem mp_consistent_execution_good : forall final rf,
     relaxed_machine_steps mp_initial_machine final rf ->
     all_done final ->
     rf 4 = Some 3 ->
     consistent (Translate.translate_trace (mach_trace final)) rf ->
     Translate.translate_trace (mach_trace final) = mp_trace_acqrel_good.
   ```

4. A fixed `NTHREADS = 8`, three-round shared-memory reduction in
   `coq/Reduction.v`. `reduction_deterministic` proves that every completed
   consistent relaxed execution has the concrete 61-event trace, and
   `reduction_result_unique` proves shared address 0 contains `VF32 36` for
   the distinct payload vector `1, …, 8`. The gate-free relaxed relation also
   has a completed stale-read counterexample, formalized by
   `reduction_determinism_needs_consistency`; consistency is therefore a
   necessary premise rather than unused decoration. The positive proof invokes
   `no_hb_overwrite` to reject those stale sources. It also includes a computed
   barrier-uniformity regression and a concrete round-structure lemma.
5. A regex-driven prototype that extracts memory actions from `rustc -Z
   dump-mir` for three curated examples. A separate syntactic check compares
   the extracted action kinds with freshly emitted PTX, including four actual
   `bar.sync` operations in the reduction fixture.

The following long-term theorem remains future work:

> If a MIR kernel is data-race-free under the MIR memory model, its compiled PTX
> program admits only executions consistent with the PTX memory model.

## Message passing

The central litmus test is:

```text
Thread 0                         Thread 1
data := 1        (relaxed)       r1 := flag      (acquire)
flag := 1        (release)       if r1 = 1:
                                    r2 := data    (relaxed)
```

`PTXHB.sw` gives semantic force to the release/acquire tags: a SYS release store
synchronizes with the SYS acquire load whose candidate reads-from map selects
that store. `PTXHB.hb` is the transitive closure of program order and this
synchronizes-with edge. The acquire/release proof uses the resulting
`data-store -> flag-store -> flag-load -> data-load` happens-before path to rule
out reading overwritten initialization. The relaxed proof supplies a concrete
reads-from map and proves it consistent, so the model is not vacuously strong.

The traces include explicit zero-initialization stores. This keeps
`rf_well_formed` simple: every load, including a load of the initial value, reads
an actual same-address, same-value store.

`MPRealizable.mp_acqrel_realizable` constructs one six-step MIR-machine
schedule—initializer, writer, then reader—and proves that its translated trace
is exactly `mp_trace_acqrel_good`. `MP.mp_acqrel_same_program` proves that this
trace and `mp_trace_acqrel_weak` contain the same program actions, while
`mp_acqrel_only_index5_value_differs` proves that they agree through index 4
and differ only in the data-load value at index 5. The weak candidate is the
trace rejected by `mp_acqrel_forbids_weak`.

`MIRRelaxed` adds a finite candidate-execution machine. Its canonical scheduler
fixes event order, while each load may select
any earlier same-address, same-type store and records that choice in a
reads-from map. `MPCandidates.mp_candidates_all` derives all four raw completed
MP candidates (`flag/data` values `0/0`, `0/1`, `1/0`, and `1/1`). Conditioning
the acquire on the release edge (`rf 4 = Some 3`) leaves exactly the good and
weak candidates; both are explicitly reachable. The consistency payoff theorem
then rules out the weak one and returns the good trace.
`mp_unconditioned_two_candidate_statement_false` formally proves why that
handoff premise cannot be omitted. `mp_sc_is_relaxed_latest_special_case`
connects the ordinary execution to the relaxed path that selects the latest
matching flag and data stores.

## Shared barriers and deterministic reduction

CTA barriers match by each thread's per-thread barrier count. `PTXHB.bar`
orders actions strictly before one participant's k-th barrier before actions
strictly after another participant's matching barrier, and `hb` is the
transitive closure of program order, release/acquire synchronization, and this
barrier relation. Strict pre/post legs are intentional: including the barrier
endpoints themselves would create mutual barrier edges and make
`hb_irreflexive` fail for every complete round;
`bar_endpoint_irreflexive_statement_false` formally exhibits the self-edge.
The legacy `SBarrier` translates
to a SYS-tagged inert event; only `SBarrierShared` translates to a CTA barrier.

The reduction uses eight shared addresses, eight threads, and strides 4, 2,
and 1. Shared loads may select any earlier same-address, same-type shared store;
the operational relation has no freshness gate. Consequently a stale completed
execution exists and produces a different trace/result. `PTXHB.consistent`, in
particular `no_hb_overwrite`, rejects it and the other overwritten-source
candidates. The separately checked `no_stale_shared_source` predicate is only
an optional diagnostic regression, not a transition premise.

This dependence is checked rather than merely documented:

```coq
Theorem reduction_determinism_needs_consistency :
  ~ (forall final rf,
      relaxed_machine_steps reduction_initial_machine final rf ->
      all_done final ->
      mach_trace final = reduction_final_trace).
```

The scheduler is round structured: work at the least completed-barrier count
finishes before those barriers are released in thread-list order. The canonical
scheduler caveat is exact: **“all executions” means all load-source choices
under this fixed schedule; relaxation is in load sourcing only, with no action
reordering or enumeration of alternate thread interleavings.** Programs without
shared barriers provably use the original MP scheduler.

The combining operation is the development's existing bit-pattern addition;
the determinism result is about uniqueness of the combining tree, not about
floating-point arithmetic. `VF32` does not model IEEE-754 rounding, NaNs, or
arithmetic.

## Repository map

| Path | Role |
| --- | --- |
| `coq/MIRSyntax.v` | Rust-like IR syntax and MIR-flavored events |
| `coq/MIRSemantics.v` | Per-thread inductive semantics |
| `coq/MIRRun.v` | Executable interpreter and step agreement proofs |
| `coq/MIRConcurrent.v` | Thread-tagged interleaving with separate global and one-CTA shared memories |
| `coq/MIRRelaxed.v` | Finite candidate machine with recorded reads-from choices and round scheduling |
| `coq/PTXEvents.v` | Hand-written PTX-style events; no external model import |
| `coq/PTXRelations.v` | Tagged trace accessors and candidate reads-from edges |
| `coq/PTXHB.v` | `po`, `sw`, `hb`, reads-from well-formedness, consistency |
| `coq/MP.v` | Acquire/release forbidden and relaxed permitted MP theorems |
| `coq/MPRealizable.v` | Explicit MIR-machine realization of `mp_trace_acqrel_good` |
| `coq/MPCandidates.v` | Exhaustive MP candidate derivation, reachability, and consistency payoff |
| `coq/Reduction.v` | Fixed eight-thread reduction, round structure, trace determinism, and unique result |
| `coq/Translate.v` | Thread-preserving MIR-event to PTX-event mapping |
| `tools/mir2coq.py` | Curated MIR text extractor with `--shared-param` modeling convention |
| `tools/check_ptx.sh` | Syntactic extracted-event/PTX validation |
| `bench/` | Standalone CUDA empirical protocol; not part of `make demo` |

`translate_trace_shape` remains as a useful regression check. It follows by
construction from `map` and is deliberately not presented as a semantic
soundness theorem.

## Reproduce the artifact

Requirements:

- Rust nightly `nightly-2025-03-02` with the `nvptx64-nvidia-cuda` target;
- Coq 8.18 or newer (the current artifact is checked with Coq 8.19);
- Python 3.

One possible setup is:

```sh
rustup toolchain install nightly-2025-03-02
rustup target add nvptx64-nvidia-cuda --toolchain nightly-2025-03-02
opam install coq
eval "$(opam env)"
```

Run the full pipeline:

```sh
make demo
```

This command:

1. regenerates MIR for `saxpy`, `atomic_flag`, and `reduction`;
2. extracts their supported memory actions into `coq/examples/*_gen.v`;
3. runs translator hardening tests and validates rejection of the deliberately
   unsupported relaxed atomic example;
4. freshly emits PTX and runs `tools/check_ptx.sh`;
5. type-checks all Coq definitions, regressions, the MP theorems, both relaxed
   candidate reachability proofs, exhaustive classification, and consistency
   payoff theorem, plus the reduction determinism theorem and result corollary.

The extractor prints warnings for omitted control flow. In particular, SAXPY's
loop and branch structure are not translated: `saxpy_gen.v` contains one
straight-line copy of the loop body's two loads and one store. The warning is an
intentional guard against treating that file as a translation of the loop.
For the reduction fixture it recognizes only rustc's curated `0..3u32`
Range/Iterator back-edge as `SFor`; its internal branch extraction remains
pattern-driven. `--shared-param _1` labels accesses through the first MIR
parameter as shared-space events. This is a modeling convention, not a claim
that the Rust pointer has CUDA shared address-space semantics.

The PTX check confirms operation forms, not semantic equivalence. For the atomic
example it checks `ld.acquire.sys.u32` and `st.release.sys.u32`. For SAXPY it
checks the generic-address `ld.f32`/`st.f32` instructions emitted by this
toolchain. The reduction check additionally observes four `bar.sync` operations
and generic pointer loads/stores; rustc does not emit `ld.shared`/`st.shared`
for the raw-pointer convention. LLVM may unroll the real loop, so PTX
instruction counts need not equal the extracted trace.

## Scope and limitations

- `PTXEvents.v` is hand-written and is **not connected** to Lustig et al.'s Coq
  PTX model. Connecting it is future work.
- The IR fragment has no MIR basic blocks, panic edges, drops, borrows,
  ownership model, or place projections. `SIf`, `SSeq`, and `SFor` are
  structured constructs, unlike rustc MIR control flow. `SFor` supports only
  a compile-time bound and fully unfolds in one silent step.
- `mir2coq.py` is regex-driven over three curated kernels. SAXPY's dynamic loop
  is diagnosed and omitted; only the reduction's exact fixed counted-loop
  pattern is recognized.
- The local consistency model has no fences, RMW operations, multiple-CTA
  membership, or source-level barrier divergence theorem. Barrier uniformity
  is an explicit trace-shape assumption where required.
- The supplied endpoint-inclusive sketch of `bar` was corrected to strict
  pre-/post-barrier program-order legs because endpoint edges make every
  matching round cyclic and consistency vacuous.
- The reduction theorem is for the fixed distinct payload vector `1, …, 8`
  and result `36`. `VF32` payloads are raw integers; there is no NaN, rounding,
  or IEEE-754 arithmetic correctness reasoning.
- The emitted-PTX comparison is a syntactic validation, not a proof of compiler
  correctness or event correspondence.
- The message-passing result is a litmus-test theorem, not the general
  Rust-to-PTX soundness theorem. The ordinary MIR machine remains sequentially
  consistent and emits only `mp_trace_acqrel_good`. The separate relaxed
  candidate machine derives the finite space only for this canonical,
  fixed schedule; arbitrary interleavings, dynamic loops, general programs,
  and a full axiomatic/operational correspondence remain future work. The
  relaxed-atomic litmus still remains model-level because the MIR fragment has
  no relaxed atomic statement syntax.

Explicitly out of scope for v1 (`[v2]`):

- Generalizing `NTHREADS`/N by induction on rounds (ship N=8; add 16/32 as
  instances only if free).
- Global→shared load phase in the kernel.
- Barrier divergence-freedom from syntax.
- IEEE-754 float semantics.
- While-loops / dynamic bounds.
- Lifting the canonical scheduler.
