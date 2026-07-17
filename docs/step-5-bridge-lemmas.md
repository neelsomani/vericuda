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

The acquire/release theorem uses an actual cross-thread happens-before path to
reject the weak read. The relaxed theorem constructs a reads-from witness and
proves that it is consistent, demonstrating that the model permits the weak
outcome when synchronization is absent.

The MIR machine is sequentially consistent because each load reads current
memory. It therefore realizes only the good execution where both loads see
thread 0's stores. `MP.mp_acqrel_same_program` formally relates that trace to
`MP.mp_trace_acqrel_weak` as the same sequence of program actions, and
`MP.mp_acqrel_only_index5_value_differs` proves that the concrete traces agree
everywhere except the final data-load value. The weak trace is an axiomatic
candidate rejected by consistency, not a MIR-machine execution.

The relaxed weak trace also remains model-level: the MIR fragment deliberately
has no relaxed atomic statement constructors. More generally, the artifact
does not derive the axiomatic candidate-execution space from the operational
machine. Establishing that axiomatic/operational correspondence is future work.

## Run the checks

```sh
eval "$(opam env)"
make demo
```

The demo rebuilds MIR and PTX, checks translator failure modes, validates the
observed PTX memory-operation forms, and asks Coq to type-check both MP theorems.
It also checks the explicit six-step MIR-machine realizability construction.

The local event layer is not imported from or proved equivalent to Lustig et
al.'s PTX model. That future linkage, and the general Rust-to-PTX soundness
theorem, remain outside this artifact.
