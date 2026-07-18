From Coq Require Import ZArith List Lia Relations Relation_Operators.

Import ListNotations.

Require Import PTXEvents PTXRelations.

(** Program order, acquire/release synchronization, CTA barrier rounds, and
    consistency for the artifact's deliberately small PTX-style event layer.

    This is not the external PTX model: it covers SYS acquire/release and
    count-matched CTA barriers only.  In particular, it does not model fences,
    RMW operations, CTA membership beyond the single traced CTA, or barrier
    divergence. *)
Module PTXHB.

Module P := PTX.
Module R := PTXRelations.

Definition po (tr : R.trace) (i j : nat) : Prop :=
  i < j /\
  exists tid, R.tid_at tr i = Some tid /\ R.tid_at tr j = Some tid.

Definition is_release_store (tr : R.trace) (idx : nat) : Prop :=
  match R.event_at tr idx with
  | Some (P.EvStore P.SpaceGlobal P.SemRelease (Some P.ScopeSYS) _ _ _) => True
  | _ => False
  end.

Definition is_acquire_load (tr : R.trace) (idx : nat) : Prop :=
  match R.event_at tr idx with
  | Some (P.EvLoad P.SpaceGlobal P.SemAcquire (Some P.ScopeSYS) _ _ _) => True
  | _ => False
  end.

Lemma release_store_in_bounds : forall tr idx,
  is_release_store tr idx -> idx < List.length tr.
Proof.
  intros tr idx Hrelease.
  unfold is_release_store in Hrelease.
  destruct (R.event_at tr idx) as [ev|] eqn:Hevent; try contradiction.
  eapply R.event_at_in_bounds. exact Hevent.
Qed.

(** A release store synchronizes with the SYS acquire load whose candidate
    reads-from map selects that store. *)
Definition sw (tr : R.trace) (rfc : R.rf_map) (i j : nat) : Prop :=
  is_release_store tr i /\
  is_acquire_load tr j /\
  rfc j = Some i.

(** Number of CTA barriers emitted by [t] among the first [i] trace entries.
    SYS-tagged legacy barriers are intentionally ignored. *)
Fixpoint barrier_count_before
    (tr : R.trace) (t : nat) (i : nat) : nat :=
  match i, tr with
  | O, _ => O
  | S i', [] => O
  | S i', (tid, ev) :: tr' =>
      let rest := barrier_count_before tr' t i' in
      match ev with
      | P.EvBarrier P.ScopeCTA =>
          if Nat.eqb tid t then S rest else rest
      | _ => rest
      end
  end.

(** Only CTA barriers synchronize.  [Translate] maps the legacy MIR barrier
    to SYS precisely so that it remains inert in this relation. *)
Definition is_barrier (tr : R.trace) (idx : nat) : Prop :=
  match R.event_at tr idx with
  | Some (P.EvBarrier P.ScopeCTA) => True
  | _ => False
  end.

Lemma is_barrier_in_bounds : forall tr idx,
  is_barrier tr idx -> idx < List.length tr.
Proof.
  intros tr idx Hbar. unfold is_barrier in Hbar.
  destruct (R.event_at tr idx) as [ev|] eqn:Hevent; try contradiction.
  destruct ev; try contradiction. destruct sc; try contradiction.
  eapply R.event_at_in_bounds. exact Hevent.
Qed.

(** Two barriers match when they have the same zero-based per-thread count.
    This assumes one CTA and does not itself assert barrier uniformity. *)
Definition matching_barriers (tr : R.trace) (i j : nat) : Prop :=
  is_barrier tr i /\ is_barrier tr j /\
  exists ti tj,
    R.tid_at tr i = Some ti /\ R.tid_at tr j = Some tj /\
    barrier_count_before tr ti i = barrier_count_before tr tj j.

(** The endpoint-inclusive relation from the initial design sketch, retained
    only to state its falsification.  It must not be used in [hb]. *)
Definition bar_endpoint (tr : R.trace) (i j : nat) : Prop :=
  exists bi bj,
    matching_barriers tr bi bj /\
    (i = bi \/ po tr i bi) /\ (j = bj \/ po tr bj j).

Lemma bar_endpoint_irreflexive_statement_false :
  ~ (forall tr idx, ~ bar_endpoint tr idx idx).
Proof.
  intro Hirrefl.
  specialize (Hirrefl [(0%nat, P.EvBarrier P.ScopeCTA)] 0%nat).
  apply Hirrefl. exists 0%nat, 0%nat. split.
  - unfold matching_barriers, is_barrier. cbn.
    split; [exact I|]. split; [exact I|].
    exists 0%nat, 0%nat. repeat split; reflexivity.
  - split; [left; reflexivity|left; reflexivity].
Qed.

(** Barrier synchronization orders a same-thread action strictly before one
    participant's barrier before a same-thread action strictly after the
    matching barrier of another participant.  The strict [po] legs are
    essential: including barrier endpoints themselves makes matching barriers
    mutually order one another and renders [hb_irreflexive] impossible. *)
Definition bar (tr : R.trace) (i j : nat) : Prop :=
  exists bi bj,
    matching_barriers tr bi bj /\ po tr i bi /\ po tr bj j.

(** All thread ids occurring in the trace have the same total CTA-barrier
    count.  This is an explicit execution-shape assumption, not a theorem
    about divergence freedom of source syntax. *)
Definition barrier_uniform (tr : R.trace) : Prop :=
  forall t t',
    (exists idx, R.tid_at tr idx = Some t) ->
    (exists idx, R.tid_at tr idx = Some t') ->
    barrier_count_before tr t (List.length tr) =
    barrier_count_before tr t' (List.length tr).

Definition hb (tr : R.trace) (rfc : R.rf_map) : nat -> nat -> Prop :=
  clos_trans nat (fun i j => po tr i j \/ sw tr rfc i j \/ bar tr i j).

Lemma no_barrier_no_bar : forall tr i j,
  (forall idx, ~ is_barrier tr idx) -> ~ bar tr i j.
Proof.
  intros tr i j Hnone [bi [bj [Hmatch _]]].
  destruct Hmatch as [Hbarrier _]. exact (Hnone bi Hbarrier).
Qed.

Lemma empty_barrier_uniform : barrier_uniform [].
Proof.
  intros t t' [idx Htid].
  destruct idx; cbn [R.tid_at R.tagged_event_at] in Htid; discriminate.
Qed.

(** Every load has a candidate source with the same address/value, and every
    non-[None] entry in the map is such an edge. *)
Definition rf_well_formed (tr : R.trace) (rfc : R.rf_map) : Prop :=
  (forall load_idx addr value,
      R.load_at tr load_idx addr value ->
      exists store_idx,
        rfc load_idx = Some store_idx /\
        R.store_at tr store_idx addr value) /\
  (forall load_idx store_idx,
      rfc load_idx = Some store_idx ->
      exists addr value,
        R.load_at tr load_idx addr value /\
        R.store_at tr store_idx addr value).

Definition no_hb_overwrite (tr : R.trace) (rfc : R.rf_map) : Prop :=
  forall load_idx source_idx overwrite_idx addr,
    rfc load_idx = Some source_idx ->
    R.addr_at tr load_idx = Some addr ->
    R.is_store_to tr overwrite_idx addr ->
    hb tr rfc source_idx overwrite_idx ->
    hb tr rfc overwrite_idx load_idx ->
    False.

Definition hb_irreflexive (tr : R.trace) (rfc : R.rf_map) : Prop :=
  forall idx, ~ hb tr rfc idx idx.

Definition consistent (tr : R.trace) (rfc : R.rf_map) : Prop :=
  rf_well_formed tr rfc /\
  no_hb_overwrite tr rfc /\
  hb_irreflexive tr rfc.

(** A concrete regression showing that [bar] contributes real ordering: the
    load after the matching barrier pair cannot read the initial store across
    the intervening overwrite.  This does not claim general coherence. *)
Definition barrier_overwrite_trace : R.trace :=
  [(0%nat, P.EvStore P.SpaceShared P.SemRelaxed None P.MemU32 0 0);
   (0%nat, P.EvStore P.SpaceShared P.SemRelaxed None P.MemU32 0 1);
   (0%nat, P.EvBarrier P.ScopeCTA);
   (1%nat, P.EvBarrier P.ScopeCTA);
   (1%nat, P.EvLoad P.SpaceShared P.SemRelaxed None P.MemU32 0 0)].

Definition barrier_overwrite_rf : R.rf_map :=
  fun idx => if Nat.eqb idx 4%nat then Some 0%nat else None.

Lemma barrier_overwrite_forbidden :
  no_hb_overwrite barrier_overwrite_trace barrier_overwrite_rf -> False.
Proof.
  intro Hno.
  eapply (Hno 4%nat 0%nat 1%nat 0%Z); cbn.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply t_step. left. unfold po. cbn. split; [lia|].
    exists 0%nat. auto.
  - apply t_step. right. right.
    exists 2%nat, 3%nat. split.
    + unfold matching_barriers. repeat split; cbn; try reflexivity.
      exists 0%nat, 1%nat. repeat split; reflexivity.
    + split.
      * unfold po. cbn. split; [lia|]. exists 0%nat. auto.
      * unfold po. cbn. split; [lia|]. exists 1%nat. auto.
Qed.

End PTXHB.
