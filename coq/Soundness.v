From Coq Require Import List.

Import ListNotations.

Require Import MIRSyntax MIRSemantics Translate PTXEvents PTXRelations.

Module Soundness.

Module M  := MIR.
Module MS := MIRSemantics.
Module T  := Translate.
Module P  := PTX.
Module RF := PTXRelations.

Lemma barrier_ok :
  T.translate_event M.EvBarrier = P.EvBarrier P.scope_cta.
Proof. reflexivity. Qed.

Lemma atomic_store_release_ok : forall ty addr v,
  T.translate_event (M.EvAtomicStoreRelease ty addr v) =
    P.EvStore P.space_global P.sem_release (Some P.scope_sys)
            (T.mem_ty_of_mir ty) addr (T.z_of_val v).
Proof. intros; reflexivity. Qed.

Lemma atomic_load_acquire_ok : forall ty addr v,
  T.translate_event (M.EvAtomicLoadAcquire ty addr v) =
    P.EvLoad P.space_global P.sem_acquire (Some P.scope_sys)
            (T.mem_ty_of_mir ty) addr (T.z_of_val v).
Proof. intros; reflexivity. Qed.

Lemma translate_trace_length : forall tr,
  List.length (T.translate_trace tr) = List.length tr.
Proof. intro tr; unfold T.translate_trace; now rewrite map_length. Qed.

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
  | M.EvBarrier =>
      p = P.EvBarrier P.ScopeCTA
  end.

Definition tagged_translate_shape
    (m : nat * M.event_mir) (p : nat * P.event) : Prop :=
  fst m = fst p /\ translate_shape (snd m) (snd p).

(** Sanity/regression lemma only: this follows by construction from [map] and
    does not establish memory-model soundness. *)
Lemma translate_trace_shape : forall tr,
  Forall2 tagged_translate_shape tr (T.translate_trace tr).
Proof.
  induction tr as [|[tid e] tr IH]; cbn; constructor; auto.
  unfold tagged_translate_shape. cbn. split; [reflexivity|].
  destruct e; cbn; reflexivity.
Qed.

(* Status and next soundness boundary:

   [MIRRelaxed] and [MPCandidates] now provide a semantic result for the fixed,
   straight-line MP litmus.  They derive its finite reads-from candidate space
   from relaxed machine steps, prove both handoff candidates reachable, prove
   that the release-read condition leaves exactly the good and weak traces,
   and use [PTXHB.consistent] to eliminate the weak trace.

   That theorem is intentionally not imported here because it comes later in
   the dependency graph, and it is not a general compiler-soundness theorem.
   The next major result remains the general reduction, which will require:
   1. Integrating the external PTX memory model's happens-before and coherence
      relations (the local [PTXHB] litmus layer is not that integration)
   2. Generalizing the finite straight-line candidate machine to realistic MIR
      control flow and schedules
   3. Proving that if a MIR trace is DRF under the MIR model, its translated
      PTX trace admits only executions consistent with the PTX model

   The [translate_trace_shape] lemma above is still only a regression check for
   the mapping; the MP payoff theorem is in [MPCandidates]. *)

End Soundness.
