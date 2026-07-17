# Executable Rust-Like IR Semantics

The small syntax and per-thread inductive semantics live in `MIRSyntax.v` and
`MIRSemantics.v`. `MIRRun.v` supplies the executable one-step function and
fuel-bounded runner.

Unlike the original smoke-test-only state, agreement is now proved:

```coq
Lemma step_fun_sound : forall c oev c',
  step_fun c = Some (oev, c') -> step c oev c'.

Lemma step_fun_complete : forall c oev c',
  step c oev c' -> step_fun c = Some (oev, c').
```

Therefore computations performed by `MIRRun.run` describe steps admitted by the
inductive relation, and every inductive step is reproduced by `step_fun`.

`MIRConcurrent.v` lifts the same per-thread relation to a machine with a shared
memory, multiple `(thread id, code, environment)` records, and a thread-tagged
event trace. A machine step nondeterministically chooses any thread whose next
statement can step. `MIRTests.v` proves that either of two runnable threads can
be selected from the same initial machine.

Build the checked development with:

```sh
eval "$(opam env)"
make -C coq all
```

This remains a Rust-like statement language, not full rustc MIR: it has no basic
blocks, terminators, place projections, panic edges, or loop representation.
