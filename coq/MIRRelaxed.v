From Coq Require Import ZArith List.

Import ListNotations.

Require Import MIRSyntax MIRSemantics MIRConcurrent PTXRelations.

(** A finite, straight-line candidate-execution machine.

    Stores and non-memory steps reuse [MIRSemantics.step].  A load evaluates
    its address normally, then nondeterministically selects any already-emitted
    same-address, same-type store as its source.  The selected source index is
    recorded in [relaxed_rf].  Loads do not roll memory back: the shared memory
    still records the latest operational write.

    To make candidate enumeration finite and independent of scheduling, this
    layer uses a canonical scheduler: only the first non-finished thread in the
    thread list may step.  It currently targets finite straight-line programs;
    loops and arbitrary interleavings require separate invariants. *)
Module MIRRelaxed.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConcurrent.
Module R := PTXRelations.

Definition thread_done (thread : MC.thread) : Prop :=
  MC.th_code thread = [].

Definition threads_done (threads : list MC.thread) : Prop :=
  Forall thread_done threads.

Definition all_done (machine : MC.machine) : Prop :=
  threads_done (MC.mach_threads machine).

Definition empty_rf : R.rf_map := fun _ => None.

Definition rf_set
    (rf : R.rf_map) (load_idx source_idx : nat) : R.rf_map :=
  fun idx => if Nat.eqb idx load_idx then Some source_idx else rf idx.

Record relaxed_state := {
  relaxed_mach : MC.machine;
  relaxed_rf   : R.rf_map
}.

Definition mk_relaxed_state
    (machine : MC.machine) (rf : R.rf_map) : relaxed_state :=
  {| relaxed_mach := machine; relaxed_rf := rf |}.

(** Deterministically split the thread list at its first unfinished thread.
    Returning the prefix as data, rather than quantifying over arbitrary list
    decompositions, makes both execution and finite candidate enumeration
    independent of proof choices. *)
Fixpoint split_first_runnable
    (threads : list MC.thread)
    : option (list MC.thread * MC.thread * list MC.thread) :=
  match threads with
  | [] => None
  | current :: after =>
      match MC.th_code current with
      | [] =>
          match split_first_runnable after with
          | None => None
          | Some (before, next, suffix) =>
              Some (current :: before, next, suffix)
          end
      | _ => Some ([], current, after)
      end
  end.

(** Only load statements receive special nondeterministic semantics. *)
Definition non_load_head (code : list M.stmt) : Prop :=
  match code with
  | M.SLoad _ _ _ :: _ => False
  | M.SAtomicLoadAcquire _ _ _ :: _ => False
  | [] => False
  | _ => True
  end.

(** A source is a previously emitted plain or release store with exactly the
    load's type, address, and selected value. *)
Inductive source_store
    (trace : list (nat * M.event_mir))
    (source_idx : nat) (ty : M.mir_ty) (addr : M.addr) (value : M.val) : Prop :=
| SourcePlain : forall tid,
    nth_error trace source_idx =
      Some (tid, M.EvStore ty addr value) ->
    source_store trace source_idx ty addr value
| SourceRelease : forall tid,
    nth_error trace source_idx =
      Some (tid, M.EvAtomicStoreRelease ty addr value) ->
    source_store trace source_idx ty addr value.

(** Selecting the latest matching store recovers the SC source policy.  The
    relaxed policy is [source_store] alone; this predicate is its subset that
    excludes a later same-address, same-type source. *)
Definition latest_source_store
    (trace : list (nat * M.event_mir))
    (source_idx : nat) (ty : M.mir_ty) (addr : M.addr) (value : M.val) : Prop :=
  source_store trace source_idx ty addr value /\
  forall later_idx later_value,
    (source_idx < later_idx)%nat ->
    ~ source_store trace later_idx ty addr later_value.

Inductive relaxed_machine_step : relaxed_state -> relaxed_state -> Prop :=
| RelaxedNonLoad :
    forall threads before current after memory trace rf oev next,
      split_first_runnable threads = Some (before, current, after) ->
      non_load_head (MC.th_code current) ->
      MS.step
        (MS.mk_cfg (MC.th_code current) (MC.th_env current) memory)
        oev next ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current)
                (MS.cfg_code next) (MS.cfg_env next) :: after)
            (MS.cfg_mem next)
            (MC.append_event (MC.th_id current) oev trace))
          rf)
| RelaxedLoad :
    forall threads before current after memory trace rf
           rest dst ptr ty addr value source_idx,
      split_first_runnable threads = Some (before, current, after) ->
      MC.th_code current = M.SLoad dst ptr ty :: rest ->
      MS.eval_addr (MC.th_env current) ptr = Some addr ->
      source_store trace source_idx ty addr value ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current) rest
                (MS.env_set (MC.th_env current) dst value) :: after)
            memory
            (trace ++ [(MC.th_id current, M.EvLoad ty addr value)]))
          (rf_set rf (length trace) source_idx))
| RelaxedAtomicLoadAcquire :
    forall threads before current after memory trace rf
           rest dst ptr ty addr value source_idx,
      split_first_runnable threads = Some (before, current, after) ->
      MC.th_code current = M.SAtomicLoadAcquire dst ptr ty :: rest ->
      MS.eval_addr (MC.th_env current) ptr = Some addr ->
      source_store trace source_idx ty addr value ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current) rest
                (MS.env_set (MC.th_env current) dst value) :: after)
            memory
            (trace ++
              [(MC.th_id current,
                M.EvAtomicLoadAcquire ty addr value)]))
          (rf_set rf (length trace) source_idx)).

Inductive relaxed_state_steps : relaxed_state -> relaxed_state -> Prop :=
| RelaxedDone : forall state,
    relaxed_state_steps state state
| RelaxedMore : forall state state' final,
    relaxed_machine_step state state' ->
    relaxed_state_steps state' final ->
    relaxed_state_steps state final.

Lemma split_first_runnable_all_done : forall threads,
  threads_done threads -> split_first_runnable threads = None.
Proof.
  intros threads Hdone. induction Hdone as [|thread threads Hthread _ IH].
  - reflexivity.
  - unfold thread_done in Hthread. cbn. rewrite Hthread, IH. reflexivity.
Qed.

(** A completed machine is terminal under the canonical scheduler. *)
Lemma all_done_no_step : forall machine rf next,
  all_done machine ->
  relaxed_machine_step (mk_relaxed_state machine rf) next ->
  False.
Proof.
  intros [threads memory trace] rf next Hdone Hstep. cbn in *.
  pose proof (split_first_runnable_all_done threads Hdone) as Hnone.
  inversion Hstep; subst;
    match goal with
    | Hsplit : split_first_runnable threads = Some _ |- _ =>
        rewrite Hnone in Hsplit; discriminate
    end.
Qed.

Definition relaxed_machine_steps
    (initial final : MC.machine) (rf : R.rf_map) : Prop :=
  relaxed_state_steps
    (mk_relaxed_state initial empty_rf)
    (mk_relaxed_state final rf).

End MIRRelaxed.
