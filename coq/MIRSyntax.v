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
| ESub (lhs rhs : expr)
| EMul (lhs rhs : expr)
| EDiv (lhs rhs : expr)
| ERem (lhs rhs : expr)
| ELt (lhs rhs : expr)
| EEq (lhs rhs : expr)
| EAnd (lhs rhs : expr)
| EXor (lhs rhs : expr)
| EShl (lhs rhs : expr)
| EShr (lhs rhs : expr)
| ENot (arg : expr)
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
| SLoop (body : list stmt)
| SSeq (body : list stmt).

Inductive event_mir :=
| EvLoad (ty : mir_ty) (addr : addr) (v : val)
| EvStore (ty : mir_ty) (addr : addr) (v : val)
| EvAtomicLoadAcquire (ty : mir_ty) (addr : addr) (v : val)
| EvAtomicStoreRelease (ty : mir_ty) (addr : addr) (v : val)
| EvAssign (x : var) (v : val)
| EvCond (cond : expr) (result : bool)
| EvBarrier.

End MIR.

Module MIRConstants.

Module M := MIR.

Definition const_i128_MIN : M.val :=
	M.VI32 (-170141183460469231731687303715884105728)%Z.

Definition const_TILE_SIZE : M.val := M.VU64 16%Z.

Definition const_TILE_SIZE_2D : M.val := M.VU64 256%Z.

Definition const_gemm_tiled_TILE_SIZE : M.val := M.VU64 16%Z.

Definition const_gemm_tiled_TILE_SIZE_2D : M.val := M.VU64 256%Z.

Definition const_ALIGNOF_u128 : M.val := M.VU64 16%Z.

Definition const_SIZEOF_u128 : M.val := M.VU64 16%Z.

End MIRConstants.
