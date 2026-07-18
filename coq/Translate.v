From Coq Require Import ZArith List.

Import ListNotations.

Require Import MIRSyntax.
Require Import PTXEvents.

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
  end.

(* PTX address-space and scope policy helpers. *)
Definition space_global : P.space := P.space_global.
Definition space_shared : P.space := P.space_shared.
Definition scope_cta   : P.scope := P.scope_cta.
Definition scope_sys   : P.scope := P.scope_sys.

(** One MIR event maps to one local PTX-style event.  Only
    [EvBarrierShared] receives the CTA tag consumed by [PTXHB.is_barrier]; the
    legacy semantics-free barrier is retained as an inert SYS-tagged event.
    Shared-space tags are modeling classifications, not compiler-correctness
    claims about emitted pointer instructions. *)
Definition translate_event (ev : M.event_mir) : P.event :=
  match ev with
  | M.EvLoad ty addr v =>
      P.EvLoad space_global P.sem_relaxed None (mem_ty_of_mir ty) addr (z_of_val v)
  | M.EvStore ty addr v =>
      P.EvStore space_global P.sem_relaxed None (mem_ty_of_mir ty) addr (z_of_val v)
  | M.EvAtomicLoadAcquire ty addr v =>
      P.EvLoad space_global P.sem_acquire (Some scope_sys)
               (mem_ty_of_mir ty) addr (z_of_val v)
  | M.EvAtomicStoreRelease ty addr v =>
      P.EvStore space_global P.sem_release (Some scope_sys)
               (mem_ty_of_mir ty) addr (z_of_val v)
  | M.EvBarrier => P.EvBarrier scope_sys
  | M.EvLoadShared ty addr v =>
      P.EvLoad space_shared P.sem_relaxed None
               (mem_ty_of_mir ty) addr (z_of_val v)
  | M.EvStoreShared ty addr v =>
      P.EvStore space_shared P.sem_relaxed None
                (mem_ty_of_mir ty) addr (z_of_val v)
  | M.EvBarrierShared => P.EvBarrier scope_cta
  end.

(** Concurrent traces retain the identity of the thread that emitted each
    event.  Only the event component is translated. *)
Definition translate_trace
    (trace : list (nat * M.event_mir)) : list (nat * P.event) :=
  List.map (fun tagged => (fst tagged, translate_event (snd tagged))) trace.

(** Embed a sequential interpreter trace as events from one thread. *)
Definition tag_trace (tid : nat) (trace : list M.event_mir)
    : list (nat * M.event_mir) :=
  List.map (fun ev => (tid, ev)) trace.

End Translate.
