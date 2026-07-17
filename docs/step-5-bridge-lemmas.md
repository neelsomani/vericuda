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

The acquire/release theorem uses an actual cross-thread happens-before path to
reject the weak read. The relaxed theorem constructs a reads-from witness and
proves that it is consistent, demonstrating that the model permits the weak
outcome when synchronization is absent.

## Run the checks

```sh
eval "$(opam env)"
make demo
```

The demo rebuilds MIR and PTX, checks translator failure modes, validates the
observed PTX memory-operation forms, and asks Coq to type-check both MP theorems.

The local event layer is not imported from or proved equivalent to Lustig et
al.'s PTX model. That future linkage, and the general Rust-to-PTX soundness
theorem, remain outside this artifact.
