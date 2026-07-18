# VeriCUDA: A Mechanized Event Layer for Rust-to-PTX Atomics, with a Prototype MIR Extraction Pipeline

VeriCUDA connects a small executable Rust-like IR to a hand-written PTX-style
event layer. The artifact contains one concurrency-sensitive result: the
message-passing litmus test forbids `flag = 1, data = 0` when the flag handoff is
release/acquire, while an explicit consistent execution permits that outcome
when both flag accesses are relaxed.

This is not an end-to-end verifier and is not connected to the Coq PTX model of
Lustig et al. The repository is an intermediate milestone toward that
larger result.

## Checked contributions

1. An executable small-step semantics for a Rust-like statement fragment with
   loads, stores, atomics, barriers, structured conditionals, and sequences.
   `MIRRun.step_fun_sound` and `MIRRun.step_fun_complete` prove agreement between
   the executable step function and the inductive semantics.
2. An interleaving semantics with one memory shared by its threads, whose
   traces contain `(thread-id, event)` pairs, plus a PTX-style layer with
   candidate reads-from, program order, release/acquire synchronization,
   happens-before, and a small consistency predicate.
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

4. A regex-driven prototype that extracts memory actions from `rustc -Z
   dump-mir` for two curated examples. A separate syntactic check compares the
   extracted action kinds with freshly emitted PTX.

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

`MIRRelaxed` adds a finite candidate-execution machine for straight-line
programs. Its canonical scheduler fixes event order, while each load may select
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

## Repository map

| Path | Role |
| --- | --- |
| `coq/MIRSyntax.v` | Rust-like IR syntax and MIR-flavored events |
| `coq/MIRSemantics.v` | Per-thread inductive semantics |
| `coq/MIRRun.v` | Executable interpreter and step agreement proofs |
| `coq/MIRConcurrent.v` | Nondeterministic interleaving over one common memory |
| `coq/MIRRelaxed.v` | Finite straight-line candidate machine with recorded reads-from choices |
| `coq/PTXEvents.v` | Hand-written PTX-style events; no external model import |
| `coq/PTXRelations.v` | Tagged trace accessors and candidate reads-from edges |
| `coq/PTXHB.v` | `po`, `sw`, `hb`, reads-from well-formedness, consistency |
| `coq/MP.v` | Acquire/release forbidden and relaxed permitted MP theorems |
| `coq/MPRealizable.v` | Explicit MIR-machine realization of `mp_trace_acqrel_good` |
| `coq/MPCandidates.v` | Exhaustive MP candidate derivation, reachability, and consistency payoff |
| `coq/Translate.v` | Thread-preserving MIR-event to PTX-event mapping |
| `tools/mir2coq.py` | Curated MIR text extractor |
| `tools/check_ptx.sh` | Syntactic extracted-event/PTX validation |

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

1. regenerates MIR for `saxpy` and `atomic_flag`;
2. extracts their supported memory actions into `coq/examples/*_gen.v`;
3. runs translator hardening tests and validates rejection of the deliberately
   unsupported relaxed atomic example;
4. freshly emits PTX and runs `tools/check_ptx.sh`;
5. type-checks all Coq definitions, regressions, the MP theorems, both relaxed
   candidate reachability proofs, exhaustive classification, and consistency
   payoff theorem.

The extractor prints warnings for omitted control flow. In particular, SAXPY's
loop and branch structure are not translated: `saxpy_gen.v` contains one
straight-line copy of the loop body's two loads and one store. The warning is an
intentional guard against treating that file as a translation of the loop.

The PTX check confirms operation forms, not semantic equivalence. For the atomic
example it checks `ld.acquire.sys.u32` and `st.release.sys.u32`. For SAXPY it
checks the generic-address `ld.f32`/`st.f32` instructions emitted by this
toolchain. LLVM may unroll the real loop, so PTX instruction counts need not
equal the straight-line extracted trace.

## Scope and limitations

- `PTXEvents.v` is hand-written and is **not connected** to Lustig et al.'s Coq
  PTX model. Connecting it is future work.
- The IR fragment has no MIR basic blocks, terminators, loops, panic edges,
  drops, borrows, ownership model, or place projections. `SIf` and `SSeq` are
  structured constructs, unlike rustc MIR control flow.
- `mir2coq.py` is regex-driven over two curated kernels. SAXPY's loop is
  diagnosed and omitted.
- The consistency model covers global-memory, SYS-scope release/acquire only.
  It has no fences, CTA scope, shared memory, or read-modify-write operations.
- Barriers translate to events but impose no cross-thread constraint.
- Floating-point payloads are raw integers; there is no NaN, rounding, or
  arithmetic correctness reasoning.
- The emitted-PTX comparison is a syntactic validation, not a proof of compiler
  correctness or event correspondence.
- The message-passing result is a litmus-test theorem, not the general
  Rust-to-PTX soundness theorem. The ordinary MIR machine remains sequentially
  consistent and emits only `mp_trace_acqrel_good`. The separate relaxed
  candidate machine derives the finite space only for this canonical,
  straight-line schedule; arbitrary interleavings, loops, general programs,
  and a full axiomatic/operational correspondence remain future work. The
  relaxed-atomic litmus still remains model-level because the MIR fragment has
  no relaxed atomic statement syntax.
