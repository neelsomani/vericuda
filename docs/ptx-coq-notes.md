# Local PTX-Style Coq API

`coq/PTXEvents.v` defines a small event vocabulary owned by this repository. It
does not import the Coq PTX model of Lustig et al.; linkage to that model is
future work.

## Event vocabulary

- Spaces: `PTX.SpaceGlobal`, `PTX.SpaceShared`
- Semantics: `PTX.SemRelaxed`, `PTX.SemAcquire`, `PTX.SemRelease`
- Scopes: `PTX.ScopeCTA`, `PTX.ScopeSYS`
- Payload tags: `PTX.MemU32`, `PTX.MemS32`, `PTX.MemF32`, `PTX.MemU64`,
  `PTX.MemPred`
- Events:
  - `PTX.EvLoad space sem (option scope) mem_ty addr value`
  - `PTX.EvStore space sem (option scope) mem_ty addr value`
  - `PTX.EvBarrier scope`

Addresses and payloads are `Z`; there are no `PTX.addr`, `PTX.reg32`,
`PTX.reg64`, `PTX.pred`, or `PTX.f32` types in this artifact.

## Trace and consistency API

`PTXRelations.trace` is `list (nat * PTX.event)`, so every event retains its
thread id. An `rf_map` is an execution candidate of type `nat -> option nat`.
It is not derived from the preceding event in list order.

`coq/PTXHB.v` defines:

- `po`: increasing trace indices from the same thread;
- `sw`: a global SYS release store read by a global SYS acquire load;
- `bar`: strict pre-/post-ordering across same-count CTA barriers;
- `hb`: transitive closure of `po ∪ sw ∪ bar`;
- `barrier_uniform`: the explicit equal-barrier-count trace assumption;
- `rf_well_formed`: loads and selected stores agree on address and value;
- `consistent`: well-formed reads-from, no happens-before-overwritten read, and
  irreflexive happens-before.

This scope is intentionally narrow: SYS release/acquire plus one-CTA,
count-matched shared barriers. CTA barrier events add ordering edges; legacy
MIR barriers translate to SYS-tagged events and remain inert. There are no
fences, multiple-CTA membership rules, RMW operations, general coherence-order
axioms, or source-level divergence theorem. `MIRRelaxed` retains an optional
stale-source diagnostic predicate, but its main shared-load transition is
gate-free; overwritten reads are rejected by this API's `no_hb_overwrite`
consistency clause.
