From Coq Require Import ZArith List String Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Module MIR.

(** * Week-1 MIR core syntax *)

Inductive mir_ty :=
| TyI32
| TyU32
| TyF32
| TyU64 (* pointer payload *)
| TyBool.

Inductive val :=
| VI32 (z : Z)
| VU32 (z : Z)
| VF32 (bits : Z)
| VU64 (addr : Z)
| VBool (b : bool).

Definition var := string.
Definition addr := Z.

Inductive expr :=
| EVal (v : val)
| EVar (x : var)
| EAdd (lhs rhs : expr)
| EMul (lhs rhs : expr)
| EPtrAdd (base ofs : expr).

Inductive stmt :=
| SAssign (x : var) (rhs : expr)
| SLoad (x : var) (ptr : expr) (ty : mir_ty)
| SStore (ptr : expr) (rhs : expr) (ty : mir_ty)
| SAtomicLoadAcquire (x : var) (ptr : expr) (ty : mir_ty)
| SAtomicStoreRelease (ptr : expr) (rhs : expr) (ty : mir_ty)
| SBarrier
| SIf (cond : expr) (then_branch else_branch : list stmt)
| SWhile (cond : expr) (body : list stmt)
| SSeq (body : list stmt).

Inductive event_mir :=
| EvLoad (ty : mir_ty) (addr : addr) (v : val)
| EvStore (ty : mir_ty) (addr : addr) (v : val)
| EvAtomicLoadAcquire (ty : mir_ty) (addr : addr) (v : val)
| EvAtomicStoreRelease (ty : mir_ty) (addr : addr) (v : val)
| EvBarrier.

End MIR.
