From Coq Require Import ZArith List.

Require Import PTXEvents.

(** Basic observations over thread-tagged PTX-style traces.

    A reads-from map is supplied as an execution candidate.  In particular,
    this module does not derive reads-from from list order: doing so would bake
    sequential consistency into the definition before consistency is checked. *)
Module PTXRelations.

Module P := PTX.

Definition trace := list (nat * P.event).
Definition rf_map := nat -> option nat.

Definition tagged_event_at (tr : trace) (idx : nat)
    : option (nat * P.event) :=
  nth_error tr idx.

Definition event_at (tr : trace) (idx : nat) : option P.event :=
  match tagged_event_at tr idx with
  | Some (_, ev) => Some ev
  | None => None
  end.

Definition tid_at (tr : trace) (idx : nat) : option nat :=
  match tagged_event_at tr idx with
  | Some (tid, _) => Some tid
  | None => None
  end.

Definition addr_at (tr : trace) (idx : nat) : option Z :=
  match event_at tr idx with
  | Some (P.EvLoad _ _ _ _ addr _) => Some addr
  | Some (P.EvStore _ _ _ _ addr _) => Some addr
  | _ => None
  end.

Definition value_at (tr : trace) (idx : nat) : option Z :=
  match event_at tr idx with
  | Some (P.EvLoad _ _ _ _ _ value) => Some value
  | Some (P.EvStore _ _ _ _ _ value) => Some value
  | _ => None
  end.

Definition load_at (tr : trace) (idx : nat) (addr value : Z) : Prop :=
  match event_at tr idx with
  | Some (P.EvLoad _ _ _ _ addr' value') =>
      addr' = addr /\ value' = value
  | _ => False
  end.

Definition store_at (tr : trace) (idx : nat) (addr value : Z) : Prop :=
  match event_at tr idx with
  | Some (P.EvStore _ _ _ _ addr' value') =>
      addr' = addr /\ value' = value
  | _ => False
  end.

Definition is_load (tr : trace) (idx : nat) : Prop :=
  exists addr value, load_at tr idx addr value.

Definition is_store_to (tr : trace) (idx : nat) (addr : Z) : Prop :=
  match event_at tr idx with
  | Some (P.EvStore _ _ _ _ addr' _) => addr' = addr
  | _ => False
  end.

(** [candidate_rf_edge] says that a proposed edge connects a load to a store
    of the same address and value.  The store need not precede the load in list
    order; ordering constraints belong in the consistency predicate. *)
Definition candidate_rf_edge
    (tr : trace) (rfc : rf_map) (store_idx load_idx : nat) : Prop :=
  rfc load_idx = Some store_idx /\
  exists addr value,
    load_at tr load_idx addr value /\
    store_at tr store_idx addr value.

Lemma event_at_in_bounds : forall tr idx ev,
  event_at tr idx = Some ev -> idx < List.length tr.
Proof.
  intros tr idx ev Hevent.
  unfold event_at, tagged_event_at in Hevent.
  destruct (nth_error tr idx) as [[tid found]|] eqn:Hnth; try discriminate.
  apply nth_error_Some. rewrite Hnth. discriminate.
Qed.

Lemma load_at_in_bounds : forall tr idx addr value,
  load_at tr idx addr value -> idx < List.length tr.
Proof.
  intros tr idx addr value Hload.
  unfold load_at, event_at, tagged_event_at in Hload.
  destruct (nth_error tr idx) as [[tid ev]|] eqn:Hnth; try contradiction.
  apply nth_error_Some. rewrite Hnth. discriminate.
Qed.

Lemma is_store_to_in_bounds : forall tr idx addr,
  is_store_to tr idx addr -> idx < List.length tr.
Proof.
  intros tr idx addr Hstore.
  unfold is_store_to in Hstore.
  destruct (event_at tr idx) as [ev|] eqn:Hevent; try contradiction.
  destruct ev; try contradiction.
  eapply event_at_in_bounds. exact Hevent.
Qed.

End PTXRelations.
