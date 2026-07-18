# Event Translation and Message-Passing Results

## Structural translation checks

`coq/Translate.v` maps one MIR-flavored event to one local PTX-style event and
maps thread-tagged traces without changing the tags. `coq/Soundness.v` contains
small regression lemmas for barrier, release-store, acquire-load, trace length,
and per-event shape.

These lemmas are by construction. In particular, `translate_trace_shape`
follows from `map`; it is a useful change detector, not a verified-translation
or memory-model theorem.

## Semantic event layer

The concurrency-sensitive definitions are separate:

- `PTXRelations.v` treats reads-from as a supplied candidate and checks
  same-address/same-value edges rather than selecting the last list-order store.
- `PTXHB.v` defines per-thread program order, SYS release/acquire
  synchronizes-with, count-matched CTA barriers, their transitive
  happens-before closure, and consistency.
- `MP.v` proves the two message-passing results.
- `MPRealizable.v` constructs the initializer, writer, and reader threads and
  proves `mp_acqrel_realizable`: six `machine_step`s produce a finished machine
  whose translated trace is exactly `MP.mp_trace_acqrel_good`.
- `MIRRelaxed.v` gives loads nondeterministic reads-from choices, records the
  chosen source indices, and uses a canonical scheduler so the candidate space
  is finite. Shared loads are gate-free: barrier freshness is enforced only by
  the later consistency check.
- `MPCandidates.v` derives the complete MP candidate space, proves reachability
  of the good and weak handoff candidates, and connects consistency to the
  unique good result.
- `Reduction.v` proves the fixed eight-thread reduction's completed trace and
  result unique under the round-structured scheduler.

`PTXHB.bar` matches barriers by each thread's barrier count and orders an action
strictly before one participant's barrier before an action strictly after
another participant's matching barrier. The strict program-order legs are a
semantic correction to the endpoint-inclusive sketch: including endpoints
creates barrier-to-barrier cycles.
`bar_endpoint_irreflexive_statement_false` proves the sketch admits a
self-edge. `barrier_overwrite_forbidden` is a concrete
two-thread regression showing that the new relation rules out an overwritten
read; `no_barrier_no_bar` and `MP.mp_traces_no_bar` prove that the MP suite gains
no accidental edges.

`MIRRelaxed.no_stale_shared_source` is an optional diagnostic predicate that
identifies a shared source when a later same-address store is separated from it
by a complete eight-thread barrier round. It is deliberately not a premise of
`RelaxedLoadShared`; the gate-free relation admits a concrete stale reduction
run. The scheduler completes non-barrier work at the least emitted-barrier
count, then releases that barrier round in id/list order.
`scheduler_coincides_no_shared_barrier` recovers the original scheduler for MP
programs.

The acquire/release theorem uses an actual cross-thread happens-before path to
reject the weak read. The relaxed theorem constructs a reads-from witness and
proves that it is consistent, demonstrating that the model permits the weak
outcome when synchronization is absent.

The ordinary MIR machine is sequentially consistent because each load reads
current memory. It therefore realizes only the good execution where both loads
see thread 0's stores. `MP.mp_acqrel_same_program` formally relates that trace
to `MP.mp_trace_acqrel_weak` as the same sequence of program actions, and
`MP.mp_acqrel_only_index5_value_differs` proves that the concrete traces agree
everywhere except the final data-load value. The weak trace is an axiomatic
candidate rejected by consistency in the ordinary machine.

The relaxed candidate machine admits four completed acquire/release candidates:
the acquire may read either flag initialization or the release, and the data
load may read either data initialization or the writer. `mp_candidates_all`
proves that list exhaustive. Under `rf 4 = Some 3`,
`mp_candidates_exact` proves that exactly the good and weak traces remain.
`mp_good_relaxed_realizable` and `mp_weak_relaxed_realizable` construct both
paths, while `mp_consistent_execution_good` applies the existing consistency
theorem to exclude the weak path.

The handoff premise is logically necessary, not a proof convenience:
`mp_unconditioned_two_candidate_statement_false` constructs the completed
flag-initialization execution as a counterexample to the originally sketched
unconditioned two-trace statement. The SC relationship is also explicit:
`mp_sc_is_relaxed_latest_special_case` proves that the ordinary current-memory
path is the relaxed path whose loads select the latest matching stores.

`Reduction.reduction_deterministic` is semantic, not by construction. The
input payloads are the distinct values `1, …, 8`,
`reduction_final_trace_length` computes 61, and `reduction_result_unique`
computes shared address 0 as `VF32 36`. The exact negative theorem
`reduction_determinism_needs_consistency` supplies a completed stale execution,
so the consistency premise is logically necessary. The positive proof checks a
concrete HB-overwrite witness and uses `PTXHB.no_hb_overwrite` to eliminate each
stale source. The combining operation is raw payload addition, not IEEE-754.

This remains a fixed-schedule, fixed-N bridge, not a general
axiomatic/operational correspondence. “All executions” means all candidate
load sources under that schedule; relaxation does not reorder actions or
quantify over alternate thread interleavings.
The separate relaxed-atomic trace also remains model-level because the MIR
fragment has no relaxed atomic statement constructors.

## Run the checks

```sh
eval "$(opam env)"
make demo
```

The demo rebuilds MIR and PTX, checks translator failure modes, validates the
observed PTX memory-operation forms, and asks Coq to type-check both MP theorems.
It also checks the ordinary six-step realization, both relaxed candidate paths,
the exhaustive candidate theorem, the consistency payoff corollary, and the
61-event reduction theorem/result corollary.

The local event layer is not imported from or proved equivalent to Lustig et
al.'s PTX model. That future linkage, and the general Rust-to-PTX soundness
theorem, remain outside this artifact.
