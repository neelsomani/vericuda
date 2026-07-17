From Coq Require Import ZArith List Arith Lia Relations Relation_Operators.

Import ListNotations.
Open Scope Z_scope.

Require Import PTXEvents PTXRelations PTXHB.

(** The message-passing litmus test.

    Indices 0 and 1 are explicit zero-initialization writes.  Indices 2--3 are
    thread 0's data/flag stores; indices 4--5 are thread 1's flag/data loads.
    Making initialization explicit lets [rf_well_formed] require every load to
    read a matching store rather than relying on an implicit initial-memory
    exception. *)
Module MP.

Module P := PTX.
Module R := PTXRelations.
Module H := PTXHB.

Definition data_addr : Z := 1000.
Definition flag_addr : Z := 2000.

Definition mp_initialization : R.trace :=
  [ (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 data_addr 0)
  ; (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 flag_addr 0)
  ].

(** The four program actions from the litmus test. *)
Definition mp_actions_acqrel : R.trace :=
  [ (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 data_addr 1)
  ; (0%nat, P.EvStore P.SpaceGlobal P.SemRelease
                      (Some P.ScopeSYS) P.MemU32 flag_addr 1)
  ; (1%nat, P.EvLoad P.SpaceGlobal P.SemAcquire
                     (Some P.ScopeSYS) P.MemU32 flag_addr 1)
  ; (1%nat, P.EvLoad P.SpaceGlobal P.SemRelaxed None P.MemU32 data_addr 0)
  ].

Definition mp_actions_relaxed : R.trace :=
  [ (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 data_addr 1)
  ; (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 flag_addr 1)
  ; (1%nat, P.EvLoad P.SpaceGlobal P.SemRelaxed None P.MemU32 flag_addr 1)
  ; (1%nat, P.EvLoad P.SpaceGlobal P.SemRelaxed None P.MemU32 data_addr 0)
  ].

Definition mp_trace_acqrel : R.trace :=
  mp_initialization ++ mp_actions_acqrel.

Definition mp_trace_relaxed : R.trace :=
  mp_initialization ++ mp_actions_relaxed.

Definition weak_outcome (tr : R.trace) (rfc : R.rf_map) : Prop :=
  R.load_at tr 4%nat flag_addr 1 /\
  R.load_at tr 5%nat data_addr 0 /\
  rfc 4%nat = Some 3%nat /\
  rfc 5%nat = Some 0%nat.

Lemma mp_acqrel_hb_init_to_data : forall rfc,
  H.hb mp_trace_acqrel rfc 0%nat 2%nat.
Proof.
  intro rfc. apply t_step. left. unfold H.po.
  split; [lia|]. exists 0%nat. cbn. auto.
Qed.

Lemma mp_acqrel_hb_data_to_load : forall rfc,
  rfc 4%nat = Some 3%nat ->
  H.hb mp_trace_acqrel rfc 2%nat 5%nat.
Proof.
  intros rfc Hrf.
  eapply t_trans with (y := 3%nat).
  - apply t_step. left. unfold H.po.
    split; [lia|]. exists 0%nat. cbn. auto.
  - eapply t_trans with (y := 4%nat).
    + apply t_step. right. unfold H.sw. cbn. auto.
    + apply t_step. left. unfold H.po.
      split; [lia|]. exists 1%nat. cbn. auto.
Qed.

Theorem mp_acqrel_forbids_weak : forall rfc,
  H.consistent mp_trace_acqrel rfc ->
  ~ weak_outcome mp_trace_acqrel rfc.
Proof.
  intros rfc [_ [Hoverwrite _]] Hweak.
  destruct Hweak as [_ [_ [Hflag Hdata]]].
  eapply (Hoverwrite 5%nat 0%nat 2%nat data_addr).
  - exact Hdata.
  - reflexivity.
  - reflexivity.
  - apply mp_acqrel_hb_init_to_data.
  - now apply mp_acqrel_hb_data_to_load.
Qed.

(** Candidate reads-from map for the relaxed weak execution: the flag load
    reads thread 0's flag=1 store, while the data load reads initialization. *)
Definition mp_weak_rf : R.rf_map :=
  fun idx =>
    if Nat.eqb idx 4%nat then Some 3%nat
    else if Nat.eqb idx 5%nat then Some 0%nat
    else None.

Lemma mp_weak_rf_well_formed :
  H.rf_well_formed mp_trace_relaxed mp_weak_rf.
Proof.
  split.
  - intros load_idx addr value Hload.
    pose proof Hload as Hload_bound.
    destruct load_idx as [|[|[|[|[|[|load_idx]]]]]];
      cbv [R.load_at R.event_at R.tagged_event_at mp_trace_relaxed]
        in Hload; try contradiction.
    + destruct Hload as [Haddr Hvalue]. subst addr value.
      exists 3%nat. split; [reflexivity|].
      cbv [R.store_at R.event_at R.tagged_event_at mp_trace_relaxed].
      split; reflexivity.
    + destruct Hload as [Haddr Hvalue]. subst addr value.
      exists 0%nat. split; [reflexivity|].
      cbv [R.store_at R.event_at R.tagged_event_at mp_trace_relaxed].
      split; reflexivity.
    + apply R.load_at_in_bounds in Hload_bound.
      cbn in Hload_bound. lia.
  - intros load_idx store_idx Hrf.
    unfold mp_weak_rf in Hrf.
    destruct (Nat.eqb load_idx 4%nat) eqn:Hfour.
    + apply Nat.eqb_eq in Hfour. subst load_idx.
      inversion Hrf; subst store_idx.
      exists flag_addr, 1.
      cbv [R.load_at R.store_at R.event_at R.tagged_event_at
           mp_trace_relaxed]. repeat split; reflexivity.
    + destruct (Nat.eqb load_idx 5%nat) eqn:Hfive.
      * apply Nat.eqb_eq in Hfive. subst load_idx.
        inversion Hrf; subst store_idx.
        exists data_addr, 0.
        cbv [R.load_at R.store_at R.event_at R.tagged_event_at
             mp_trace_relaxed]. repeat split; reflexivity.
      * discriminate.
Qed.

Lemma mp_relaxed_no_sw : forall rfc i j,
  ~ H.sw mp_trace_relaxed rfc i j.
Proof.
  intros rfc i j [Hrelease _].
  pose proof (H.release_store_in_bounds mp_trace_relaxed i Hrelease) as Hbound.
  unfold H.is_release_store in Hrelease.
  destruct i as [|[|[|[|[|[|i]]]]]];
    cbn in Hrelease; try contradiction.
  cbn in Hbound. lia.
Qed.

Definition same_thread (tr : R.trace) (i j : nat) : Prop :=
  exists tid, R.tid_at tr i = Some tid /\ R.tid_at tr j = Some tid.

Lemma same_thread_trans : forall tr i j k,
  same_thread tr i j -> same_thread tr j k -> same_thread tr i k.
Proof.
  intros tr i j k [tid [Hi Hj]] [tid' [Hj' Hk]].
  rewrite Hj in Hj'. inversion Hj'. subst tid'.
  exists tid. auto.
Qed.

Lemma mp_relaxed_hb_same_thread : forall rfc i j,
  H.hb mp_trace_relaxed rfc i j ->
  same_thread mp_trace_relaxed i j.
Proof.
  intros rfc i j Hhb.
  induction Hhb as [i j Hedge | i j k Hij IHij Hjk IHjk].
  - destruct Hedge as [Hpo | Hsw].
    + exact (proj2 Hpo).
    + exfalso. now apply (mp_relaxed_no_sw rfc i j).
  - eapply same_thread_trans; eauto.
Qed.

Lemma mp_relaxed_hb_lt : forall rfc i j,
  H.hb mp_trace_relaxed rfc i j -> (i < j)%nat.
Proof.
  intros rfc i j Hhb.
  induction Hhb as [i j Hedge | i j k Hij IHij Hjk IHjk].
  - destruct Hedge as [Hpo | Hsw].
    + exact (proj1 Hpo).
    + exfalso. now apply (mp_relaxed_no_sw rfc i j).
  - lia.
Qed.

Lemma mp_weak_rf_load_tid : forall load_idx store_idx,
  mp_weak_rf load_idx = Some store_idx ->
  R.tid_at mp_trace_relaxed load_idx = Some 1%nat.
Proof.
  intros load_idx store_idx Hrf.
  unfold mp_weak_rf in Hrf.
  destruct (Nat.eqb load_idx 4%nat) eqn:Hfour.
  - apply Nat.eqb_eq in Hfour. subst load_idx. reflexivity.
  - destruct (Nat.eqb load_idx 5%nat) eqn:Hfive.
    + apply Nat.eqb_eq in Hfive. subst load_idx. reflexivity.
    + discriminate.
Qed.

Lemma mp_relaxed_store_tid : forall store_idx addr,
  R.is_store_to mp_trace_relaxed store_idx addr ->
  R.tid_at mp_trace_relaxed store_idx = Some 0%nat.
Proof.
  intros store_idx addr Hstore.
  pose proof (R.is_store_to_in_bounds
                mp_trace_relaxed store_idx addr Hstore) as Hbound.
  destruct store_idx as [|[|[|[|[|[|store_idx]]]]]];
    cbn in Hstore |- *; try contradiction; try reflexivity.
  cbn in Hbound. lia.
Qed.

Lemma mp_weak_rf_no_hb_overwrite :
  H.no_hb_overwrite mp_trace_relaxed mp_weak_rf.
Proof.
  intros load_idx source_idx overwrite_idx addr
         Hrf _ Hstore _ Hoverwrite_load.
  pose proof (mp_relaxed_hb_same_thread
                mp_weak_rf overwrite_idx load_idx Hoverwrite_load)
    as [tid [Hoverwrite_tid Hload_tid]].
  pose proof (mp_relaxed_store_tid overwrite_idx addr Hstore) as Hstore_zero.
  pose proof (mp_weak_rf_load_tid load_idx source_idx Hrf) as Hload_one.
  rewrite Hstore_zero in Hoverwrite_tid. inversion Hoverwrite_tid. subst tid.
  rewrite Hload_one in Hload_tid. discriminate.
Qed.

Lemma mp_weak_rf_consistent :
  H.consistent mp_trace_relaxed mp_weak_rf.
Proof.
  split.
  - apply mp_weak_rf_well_formed.
  - split.
    + apply mp_weak_rf_no_hb_overwrite.
    + intros idx Hcycle.
      pose proof (mp_relaxed_hb_lt mp_weak_rf idx idx Hcycle).
      lia.
Qed.

Theorem mp_relaxed_permits_weak : exists rfc,
  H.consistent mp_trace_relaxed rfc /\
  weak_outcome mp_trace_relaxed rfc.
Proof.
  exists mp_weak_rf. split.
  - apply mp_weak_rf_consistent.
  - repeat split; reflexivity.
Qed.

End MP.
