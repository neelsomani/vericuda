From Coq Require Import ZArith List Relations Relation_Operators.

Require Import PTXEvents PTXRelations.

(** Program order, acquire/release synchronization, and consistency for the
    artifact's deliberately small PTX-style event layer.

    Scope is restricted to global-memory SYS acquire/release operations.  No
    fences, CTA/shared-memory rules, RMW operations, or barrier semantics are
    included here. *)
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

Definition hb (tr : R.trace) (rfc : R.rf_map) : nat -> nat -> Prop :=
  clos_trans nat (fun i j => po tr i j \/ sw tr rfc i j).

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

End PTXHB.
