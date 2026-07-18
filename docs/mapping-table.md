# Extracted MIR Event → PTX-Style Event Mapping

This table describes `coq/Translate.v`. The event constructors come from the
local, hand-written `coq/PTXEvents.v`; they are not constructors from an
external PTX formalization. The final column records what the repository's
`rustc` PTX check actually observes.

| Extracted action | MIR event | Local PTX-style event | Checked emitted PTX |
| --- | --- | --- | --- |
| plain `i32` load | `EvLoad TyI32 addr val` | `EvLoad SpaceGlobal SemRelaxed None MemS32 addr (z_of_val val)` | not exercised by the PTX fixtures |
| plain `f32` load | `EvLoad TyF32 addr val` | `EvLoad SpaceGlobal SemRelaxed None MemF32 addr (z_of_val val)` | SAXPY contains `ld.f32` |
| plain `i32` store | `EvStore TyI32 addr val` | `EvStore SpaceGlobal SemRelaxed None MemS32 addr (z_of_val val)` | not exercised by the PTX fixtures |
| plain `f32` store | `EvStore TyF32 addr val` | `EvStore SpaceGlobal SemRelaxed None MemF32 addr (z_of_val val)` | SAXPY contains `st.f32` |
| acquire `u32` load | `EvAtomicLoadAcquire TyU32 addr val` | `EvLoad SpaceGlobal SemAcquire (Some ScopeSYS) MemU32 addr (z_of_val val)` | `ld.acquire.sys.u32` |
| release `u32` store | `EvAtomicStoreRelease TyU32 addr val` | `EvStore SpaceGlobal SemRelease (Some ScopeSYS) MemU32 addr (z_of_val val)` | `st.release.sys.u32` |
| legacy barrier | `EvBarrier` | `EvBarrier ScopeSYS` | not emitted by the curated fixtures; deliberately inert in `PTXHB.is_barrier` |
| modeled shared `f32` load | `EvLoadShared TyF32 addr val` | `EvLoad SpaceShared SemRelaxed None MemF32 addr (z_of_val val)` | reduction raw pointer actually emits generic `ld.f32`, not `ld.shared.f32` |
| modeled shared `f32` store | `EvStoreShared TyF32 addr val` | `EvStore SpaceShared SemRelaxed None MemF32 addr (z_of_val val)` | reduction raw pointer actually emits a generic store rather than `st.shared.f32`; the exact PTX form is checked against the pinned toolchain |
| shared CTA barrier | `EvBarrierShared` | `EvBarrier ScopeCTA` | reduction emits four `bar.sync 0` instructions after LLVM unrolling |

Important distinctions:

- `SemRelaxed` is the local event layer's tag for plain actions. It does **not**
  claim that rustc emits a PTX mnemonic such as `ld.global.relaxed.*`.
- With raw Rust pointers, the checked toolchain emits generic-address
  `ld.f32`/`st.f32`, not `ld.global.f32`/`st.global.f32`. The model currently
  classifies the SAXPY pointers as global. For reduction,
  `mir2coq.py --shared-param _1` classifies the same raw-pointer forms as
  shared by explicit modeling convention; this does not change rustc's PTX
  address space.
- `mem_ty_of_mir` maps `TyI32 → MemS32`, `TyU32 → MemU32`, `TyF32 → MemF32`,
  `TyU64 → MemU64`, and `TyBool → MemPred`. This is a payload tag; there is no
  separate `value_has_type` judgment.
- Values are encoded by `z_of_val`; floating-point payloads are treated as raw
  bit-pattern integers and booleans as 0/1.

Run `make check-ptx` to regenerate all three PTX files and mechanically check the
rows exercised by the curated examples. This is syntactic validation, not a
compiler-correctness proof.
