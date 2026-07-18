# Executable Rust-Like IR Semantics

The small syntax and per-thread inductive semantics live in `MIRSyntax.v` and
`MIRSemantics.v`. `MIRRun.v` supplies the executable one-step function and
fuel-bounded runner.

Unlike the original smoke-test-only state, agreement is now proved:

```coq
Lemma step_fun_sound : forall tid c oev c',
  step_fun tid c = Some (oev, c') -> step tid c oev c'.

Lemma step_fun_complete : forall tid c oev c',
  step tid c oev c' -> step_fun tid c = Some (oev, c').
```

Therefore computations performed by `MIRRun.run` describe steps admitted by the
inductive relation, and every inductive step is reproduced by `step_fun`.

Expression evaluation and stepping take a thread id for `ETid`. `ELt` supports
same-width signed/same-width unsigned comparisons, `EShr` is logical `VU32`
shift-right, and `SFor` fully unfolds its constant bound in one silent step.
The per-thread semantics is deliberately partial at `SLoadShared`,
`SStoreShared`, and `SBarrierShared`; both `step` and `step_fun` leave those
heads to the machine layer.

`MIRConcurrent.v` lifts the per-thread relation to a machine with disjoint
global and CTA-shared memories, multiple `(thread id, code, environment)`
records, and a thread-tagged event trace. Equal numeric global/shared addresses
do not alias. An ordinary machine step nondeterministically chooses a runnable
thread; three additional constructors perform one thread's shared load, shared
store, or shared barrier event. Cross-thread barrier force lives in `PTXHB` and
the relaxed scheduler, not in the one-thread barrier constructor.

Build the checked development with:

```sh
eval "$(opam env)"
make -C coq all
```

This remains a Rust-like statement language, not full rustc MIR: it has no basic
blocks, terminators, place projections, panic edges, or dynamic/back-edge loop
semantics.
