From Coq Require Import ZArith Bool.Bool.

(** A hand-written PTX-style event vocabulary.

    This file does not import or claim a connection to the formal PTX model of
    Lustig et al.  It is the deliberately small event layer used by this
    artifact: global/shared-space tags, acquire/release annotations, SYS/CTA
    scope tags, barriers, and raw [Z] payloads. *)
Module PTX.

Inductive space :=
| SpaceGlobal
| SpaceShared.

Inductive mem_sem :=
| SemRelaxed
| SemAcquire
| SemRelease.

Inductive scope :=
| ScopeCTA
| ScopeSYS.

Inductive mem_ty :=
| MemU32
| MemS32
| MemF32
| MemU64
| MemPred.

Inductive event :=
| EvLoad
    (sp  : space)
    (sem : mem_sem)
    (sc  : option scope)
    (ty  : mem_ty)
    (addr: Z)
    (val : Z)
| EvStore
    (sp  : space)
    (sem : mem_sem)
    (sc  : option scope)
    (ty  : mem_ty)
    (addr: Z)
    (val : Z)
| EvBarrier (sc : scope).

Definition space_global : space := SpaceGlobal.
Definition space_shared : space := SpaceShared.

Definition sem_relaxed : mem_sem := SemRelaxed.
Definition sem_acquire : mem_sem := SemAcquire.
Definition sem_release : mem_sem := SemRelease.

Definition scope_cta : scope := ScopeCTA.
Definition scope_sys : scope := ScopeSYS.

End PTX.
