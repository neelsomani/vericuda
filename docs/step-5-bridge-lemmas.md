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
  synchronizes-with, their transitive happens-before closure, and consistency.
- `MP.v` proves the two message-passing results.
- `MPRealizable.v` constructs the initializer, writer, and reader threads and
  proves `mp_acqrel_realizable`: six `machine_step`s produce a finished machine
  whose translated trace is exactly `MP.mp_trace_acqrel_good`.
- `MIRRelaxed.v` gives straight-line loads nondeterministic reads-from choices,
  records the chosen source indices, and uses a canonical scheduler so the
  candidate space is finite.
- `MPCandidates.v` derives the complete MP candidate space, proves reachability
  of the good and weak handoff candidates, and connects consistency to the
  unique good result.

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

This is deliberately a finite straight-line bridge, not a general
axiomatic/operational correspondence. The separate relaxed-atomic trace also
remains model-level because the MIR fragment has no relaxed atomic statement
constructors. General schedules, control flow, and the full reduction remain
future work.

## Run the checks

```sh
eval "$(opam env)"
make demo
```

The demo rebuilds MIR and PTX, checks translator failure modes, validates the
observed PTX memory-operation forms, and asks Coq to type-check both MP theorems.
It also checks the ordinary six-step realization, both relaxed candidate paths,
the exhaustive candidate theorem, and the consistency payoff corollary.

The local event layer is not imported from or proved equivalent to Lustig et
al.'s PTX model. That future linkage, and the general Rust-to-PTX soundness
theorem, remain outside this artifact.
