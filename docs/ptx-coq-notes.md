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
- `hb`: transitive closure of `po ∪ sw`;
- `rf_well_formed`: loads and selected stores agree on address and value;
- `consistent`: well-formed reads-from, no happens-before-overwritten read, and
  irreflexive happens-before.

This scope is intentionally narrow: SYS release/acquire and global space only.
Barriers carry a tag but currently add no ordering edge. There are no fences,
CTA/shared-memory rules, RMW operations, or coherence-order axioms.
