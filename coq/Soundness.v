From Coq Require Import List.

Import ListNotations.

Require Import MIRSyntax MIRSemantics Translate PTXImports PTXRelations.

Module Soundness.

Module M  := MIR.
Module MS := MIRSemantics.
Module T  := Translate.
Module P  := PTX.
Module RF := PTXRelations.

Lemma barrier_ok :
  T.translate_event M.EvBarrier = Some (P.EvBarrier P.scope_cta).
Proof. reflexivity. Qed.

Lemma atomic_store_release_ok : forall ty addr v,
  T.translate_event (M.EvAtomicStoreRelease ty addr v) =
    Some (P.EvStore P.space_global P.sem_release (Some P.scope_sys)
            (T.mem_ty_of_mir ty) addr (T.z_of_val v)).
Proof. intros; reflexivity. Qed.

Lemma atomic_load_acquire_ok : forall ty addr v,
  T.translate_event (M.EvAtomicLoadAcquire ty addr v) =
    Some (P.EvLoad P.space_global P.sem_acquire (Some P.scope_sys)
            (T.mem_ty_of_mir ty) addr (T.z_of_val v)).
Proof. intros; reflexivity. Qed.

Lemma translate_trace_length_le : forall tr,
  List.length (T.translate_trace tr) <= List.length tr.
Proof.
  induction tr as [|ev tr IH]; cbn; auto with arith.
  destruct (T.translate_event ev); cbn; auto with arith.
Qed.

Definition translate_shape (m : M.event_mir) (p : P.event) : Prop :=
  match m with
  | M.EvLoad ty a v =>
      p = P.EvLoad P.SpaceGlobal P.SemRelaxed None (T.mem_ty_of_mir ty) a (T.z_of_val v)
  | M.EvStore ty a v =>
      p = P.EvStore P.SpaceGlobal P.SemRelaxed None (T.mem_ty_of_mir ty) a (T.z_of_val v)
  | M.EvAtomicLoadAcquire ty a v =>
      p = P.EvLoad P.SpaceGlobal P.SemAcquire (Some P.ScopeSYS) (T.mem_ty_of_mir ty) a (T.z_of_val v)
  | M.EvAtomicStoreRelease ty a v =>
      p = P.EvStore P.SpaceGlobal P.SemRelease (Some P.ScopeSYS) (T.mem_ty_of_mir ty) a (T.z_of_val v)
  | M.EvAssign _ _ => False
  | M.EvCond _ _ => False
  | M.EvBarrier =>
      p = P.EvBarrier P.ScopeCTA
  end.

Lemma translate_event_shape : forall m pev,
  T.translate_event m = Some pev -> translate_shape m pev.
Proof.
  intros m pev H.
  destruct m; cbn in H; try discriminate; inversion H; subst; constructor.
Qed.

Fixpoint observable_events (tr : list M.event_mir) : list M.event_mir :=
  match tr with
  | [] => []
  | ev :: tr' =>
      match T.translate_event ev with
      | Some _ => ev :: observable_events tr'
      | None => observable_events tr'
      end
  end.

Lemma translate_trace_shape : forall tr,
  Forall2 translate_shape (observable_events tr) (T.translate_trace tr).
Proof.
  induction tr as [|ev tr IH].
  - cbn. constructor.
  - cbn. destruct (T.translate_event ev) eqn:Hev; cbn.
    + constructor.
      * eapply translate_event_shape; eauto.
      * apply IH.
    + apply IH.
Qed.

(* Placeholder for the eventual per-trace correspondence theorem. *)
Theorem translate_trace_sound : forall (trace : list M.event_mir),
  True.
Proof. exact (fun _ => I). Qed.

End Soundness.
