From Coq Require Import ZArith List.

Import ListNotations.

Require Import MIRSyntax.
Require Import PTXImports.

Module Translate.

Module M := MIR.
Module P := PTX.

(* Map MIR scalar types to PTX payload tags. *)
Definition mem_ty_of_mir (t : M.mir_ty) : P.mem_ty :=
  match t with
  | M.TyI32 => P.MemS32
  | M.TyU32 => P.MemU32
  | M.TyF32 => P.MemF32
  | M.TyU64 => P.MemU64
  | M.TyBool => P.MemPred
  end.

(* Encode MIR values as Z payloads following PTX register widths. *)
Definition z_of_val (v : M.val) : Z :=
  match v with
  | M.VI32 z => z
  | M.VU32 z => z
  | M.VF32 bits => bits
  | M.VU64 addr => addr
  | M.VBool true => 1
  | M.VBool false => 0
  | M.VOptionNone => 0
  | M.VOptionSome _ => 1
  | M.VRange cur _ _ => cur
  end.

(* Week-1 policy helpers. *)
Definition space_global : P.space := P.space_global.
Definition scope_cta   : P.scope := P.scope_cta.
Definition scope_sys   : P.scope := P.scope_sys.

(* One MIR event maps to one PTX event. *)
Definition translate_event (ev : M.event_mir) : option P.event :=
  match ev with
  | M.EvLoad ty addr v =>
      Some (P.EvLoad space_global P.sem_relaxed None (mem_ty_of_mir ty) addr (z_of_val v))
  | M.EvStore ty addr v =>
      Some (P.EvStore space_global P.sem_relaxed None (mem_ty_of_mir ty) addr (z_of_val v))
  | M.EvAtomicLoadAcquire ty addr v =>
      Some (P.EvLoad space_global P.sem_acquire (Some scope_sys)
               (mem_ty_of_mir ty) addr (z_of_val v))
  | M.EvAtomicStoreRelease ty addr v =>
      Some (P.EvStore space_global P.sem_release (Some scope_sys)
               (mem_ty_of_mir ty) addr (z_of_val v))
  | M.EvAssign _ _ => None
  | M.EvCond _ _ => None
  | M.EvBarrier => Some (P.EvBarrier scope_cta)
  end.

Definition translate_trace (trace : list M.event_mir) : list P.event :=
  List.fold_right
    (fun ev acc => match translate_event ev with
                   | Some pev => pev :: acc
                   | None => acc
                   end)
    [] trace.

End Translate.

