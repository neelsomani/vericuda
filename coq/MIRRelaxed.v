From Coq Require Import ZArith List Bool Lia.

Import ListNotations.

Require Import MIRSyntax MIRSemantics MIRConcurrent PTXRelations.

(** A finite candidate-execution machine for the curated static fragment.

    Stores and non-memory steps reuse [MIRSemantics.step].  A load evaluates
    its address normally, then nondeterministically selects any already-emitted
    same-address, same-type store as its source.  The selected source index is
    recorded in [relaxed_rf].  Loads do not roll memory back: the shared memory
    still records the latest operational write.

    To make candidate enumeration finite and independent of scheduling, this
    layer uses a canonical scheduler.  Programs without shared barriers retain
    the original first-runnable schedule.  Barrier programs use a deterministic
    round schedule: all threads at the least completed-barrier count finish
    their pre-barrier work before barriers at that count are released.  This
    does not model arbitrary thread interleavings. *)
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

Definition nthreads : nat := 8%nat.

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

(** A conservative syntactic barrier detector.  Structured statements are
    inspected recursively; this predicate does not prove divergence freedom. *)
Fixpoint stmt_has_shared_barrier (stmt : M.stmt) : bool :=
  match stmt with
  | M.SBarrierShared => true
  | M.SIf _ yes no =>
      existsb stmt_has_shared_barrier yes ||
      existsb stmt_has_shared_barrier no
  | M.SSeq body => existsb stmt_has_shared_barrier body
  | M.SFor _ _ body => existsb stmt_has_shared_barrier body
  | _ => false
  end.

Definition code_has_shared_barrier (code : list M.stmt) : bool :=
  existsb stmt_has_shared_barrier code.

Definition threads_have_shared_barrier (threads : list MC.thread) : bool :=
  existsb (fun thread => code_has_shared_barrier (MC.th_code thread)) threads.

Definition no_thread_has_shared_barrier (threads : list MC.thread) : Prop :=
  Forall (fun thread => code_has_shared_barrier (MC.th_code thread) = false)
    threads.

Definition head_is_shared_barrier (thread : MC.thread) : bool :=
  match MC.th_code thread with
  | M.SBarrierShared :: _ => true
  | _ => false
  end.

(** Completed shared-barrier count for one thread in a MIR trace. *)
Fixpoint shared_barrier_count
    (trace : list (nat * M.event_mir)) (tid : nat) : nat :=
  match trace with
  | [] => O
  | (event_tid, event) :: rest =>
      let count := shared_barrier_count rest tid in
      match event with
      | M.EvBarrierShared =>
          if Nat.eqb event_tid tid then S count else count
      | _ => count
      end
  end.

Fixpoint min_barrier_count
    (trace : list (nat * M.event_mir)) (threads : list MC.thread)
    : option nat :=
  match threads with
  | [] => None
  | thread :: rest =>
      let tail_min := min_barrier_count trace rest in
      match MC.th_code thread, tail_min with
      | [], None => None
      | [], Some count => Some count
      | _ :: _, None => Some (shared_barrier_count trace (MC.th_id thread))
      | _ :: _, Some count =>
          Some (Nat.min (shared_barrier_count trace (MC.th_id thread)) count)
      end
  end.

(** Split at the first unfinished thread in [round].  When [nonbarrier_only]
    is true, threads currently waiting at a shared barrier are skipped. *)
Fixpoint split_first_at_round
    (trace : list (nat * M.event_mir)) (round : nat)
    (nonbarrier_only : bool) (threads : list MC.thread)
    : option (list MC.thread * MC.thread * list MC.thread) :=
  match threads with
  | [] => None
  | current :: after =>
      let eligible :=
        Nat.eqb (shared_barrier_count trace (MC.th_id current)) round &&
        match MC.th_code current with
        | [] => false
        | _ :: _ =>
            if nonbarrier_only then negb (head_is_shared_barrier current)
            else true
        end in
      if eligible then Some ([], current, after)
      else
        match split_first_at_round trace round nonbarrier_only after with
        | None => None
        | Some (before, next, suffix) =>
            Some (current :: before, next, suffix)
        end
  end.

(** Deterministic round-aware scheduler.  It first chooses non-barrier work at
    the least completed-barrier count; only when none remains does it release
    waiting barriers in thread-list order. *)
Definition split_round_scheduled
    (trace : list (nat * M.event_mir)) (threads : list MC.thread)
    : option (list MC.thread * MC.thread * list MC.thread) :=
  match min_barrier_count trace threads with
  | None => None
  | Some round =>
      match split_first_at_round trace round true threads with
      | Some split => Some split
      | None => split_first_at_round trace round false threads
      end
  end.

(** The canonical scheduler is exactly the legacy scheduler when no residual
    code contains a shared barrier. *)
Definition split_first_barrier_blocked
    (trace : list (nat * M.event_mir)) (threads : list MC.thread)
    : option (list MC.thread * MC.thread * list MC.thread) :=
  if threads_have_shared_barrier threads
  then split_round_scheduled trace threads
  else split_first_runnable threads.

Lemma no_thread_barrier_bool_false : forall threads,
  no_thread_has_shared_barrier threads ->
  threads_have_shared_barrier threads = false.
Proof.
  intros threads Hnone. induction Hnone as [|thread threads Hthread _ IH].
  - reflexivity.
  - change (code_has_shared_barrier (MC.th_code thread) ||
      threads_have_shared_barrier threads = false).
    rewrite Hthread, IH. reflexivity.
Qed.

Lemma scheduler_coincides_no_shared_barrier : forall trace threads,
  no_thread_has_shared_barrier threads ->
  split_first_barrier_blocked trace threads = split_first_runnable threads.
Proof.
  intros trace threads Hnone. unfold split_first_barrier_blocked.
  rewrite (no_thread_barrier_bool_false threads Hnone). reflexivity.
Qed.

(** Only load statements receive special nondeterministic semantics. *)
Definition non_load_head (code : list M.stmt) : Prop :=
  match code with
  | M.SLoad _ _ _ :: _ => False
  | M.SAtomicLoadAcquire _ _ _ :: _ => False
  | M.SLoadShared _ _ _ :: _ => False
  | M.SStoreShared _ _ _ :: _ => False
  | M.SBarrierShared :: _ => False
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

(** A candidate source for a shared load is an already-emitted shared store
    of exactly the same type, address, and value.  The main relaxed relation
    deliberately imposes no barrier-freshness gate: stale candidates remain
    executable and are rejected, when appropriate, by PTX consistency. *)
Inductive source_store_shared
    (trace : list (nat * M.event_mir))
    (source_idx : nat) (ty : M.mir_ty) (addr : M.addr) (value : M.val) : Prop :=
| SourceShared : forall tid,
    nth_error trace source_idx =
      Some (tid, M.EvStoreShared ty addr value) ->
    source_store_shared trace source_idx ty addr value.

(** A full round lies strictly between [i] and [j] when every one of the fixed
    eight thread ids has a same-numbered shared barrier in that interval.  The
    predicate assumes a single CTA and is not a general CUDA barrier model. *)
Definition separated_by_barrier
    (trace : list (nat * M.event_mir)) (i j : nat) : Prop :=
  (i < j)%nat /\
  exists round, forall tid,
    (tid < nthreads)%nat ->
    exists barrier_idx,
      (i < barrier_idx < j)%nat /\
      nth_error trace barrier_idx = Some (tid, M.EvBarrierShared) /\
      shared_barrier_count (firstn barrier_idx trace) tid = round.

(** An optional diagnostic predicate: a source is stale when a later
    same-address shared store is separated from it by a complete barrier
    round.  Same-round alternatives remain allowed.  This predicate is not a
    premise of [RelaxedLoadShared]. *)
Definition no_stale_shared_source
    (trace : list (nat * M.event_mir)) (source_idx : nat) (addr : M.addr)
    : Prop :=
  forall later_idx later_ty later_value,
    source_store_shared trace later_idx later_ty addr later_value ->
    (later_idx <= source_idx)%nat \/
    ~ separated_by_barrier trace source_idx later_idx.

Lemma single_shared_store_not_stale : forall tid ty addr value,
  no_stale_shared_source [(tid, M.EvStoreShared ty addr value)] 0%nat addr.
Proof.
  intros tid ty addr value later_idx later_ty later_value Hsource.
  inversion Hsource as [source_tid Hnth]; subst.
  destruct later_idx as [|later_idx].
  - left. lia.
  - destruct later_idx; cbn in Hnth; discriminate.
Qed.

(** A complete eight-thread round separates the old and new stores below.
    This regression checks the optional stale-source predicate independently
    of the deliberately gate-free transition relation. *)
Definition stale_shared_trace : list (nat * M.event_mir) :=
  [(0%nat, M.EvStoreShared M.TyF32 0 (M.VF32 0));
   (0%nat, M.EvBarrierShared); (1%nat, M.EvBarrierShared);
   (2%nat, M.EvBarrierShared); (3%nat, M.EvBarrierShared);
   (4%nat, M.EvBarrierShared); (5%nat, M.EvBarrierShared);
   (6%nat, M.EvBarrierShared); (7%nat, M.EvBarrierShared);
   (0%nat, M.EvStoreShared M.TyF32 0 (M.VF32 1))].

Lemma stale_shared_trace_separated :
  separated_by_barrier stale_shared_trace 0%nat 9%nat.
Proof.
  split; [lia|]. exists 0%nat. intros tid Htid.
  destruct tid as [|[|[|[|[|[|[|[|tid]]]]]]]].
  - exists 1%nat. repeat split; try lia; reflexivity.
  - exists 2%nat. repeat split; try lia; reflexivity.
  - exists 3%nat. repeat split; try lia; reflexivity.
  - exists 4%nat. repeat split; try lia; reflexivity.
  - exists 5%nat. repeat split; try lia; reflexivity.
  - exists 6%nat. repeat split; try lia; reflexivity.
  - exists 7%nat. repeat split; try lia; reflexivity.
  - exists 8%nat. repeat split; try lia; reflexivity.
  - unfold nthreads in Htid. lia.
Qed.

Lemma stale_shared_source_rejected :
  ~ no_stale_shared_source stale_shared_trace 0%nat 0.
Proof.
  intro Hgate.
  assert (Hsource : source_store_shared stale_shared_trace 9%nat
      M.TyF32 0 (M.VF32 1)).
  { apply SourceShared with (tid := 0%nat). reflexivity. }
  specialize (Hgate 9%nat M.TyF32 (M.VF32 1) Hsource).
  destruct Hgate as [Hle | Hnot]; [lia|].
  exact (Hnot stale_shared_trace_separated).
Qed.

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
    forall threads before current after memory shared trace rf oev next,
      split_first_barrier_blocked trace threads =
        Some (before, current, after) ->
      non_load_head (MC.th_code current) ->
      MS.step (MC.th_id current)
        (MS.mk_cfg (MC.th_code current) (MC.th_env current) memory)
        oev next ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory shared trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current)
                (MS.cfg_code next) (MS.cfg_env next) :: after)
            (MS.cfg_mem next)
            shared
            (MC.append_event (MC.th_id current) oev trace))
          rf)
| RelaxedLoad :
    forall threads before current after memory shared trace rf
           rest dst ptr ty addr value source_idx,
      split_first_barrier_blocked trace threads =
        Some (before, current, after) ->
      MC.th_code current = M.SLoad dst ptr ty :: rest ->
      MS.eval_addr (MC.th_id current) (MC.th_env current) ptr = Some addr ->
      source_store trace source_idx ty addr value ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory shared trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current) rest
                (MS.env_set (MC.th_env current) dst value) :: after)
            memory
            shared
            (trace ++ [(MC.th_id current, M.EvLoad ty addr value)]))
          (rf_set rf (length trace) source_idx))
| RelaxedAtomicLoadAcquire :
    forall threads before current after memory shared trace rf
           rest dst ptr ty addr value source_idx,
      split_first_barrier_blocked trace threads =
        Some (before, current, after) ->
      MC.th_code current = M.SAtomicLoadAcquire dst ptr ty :: rest ->
      MS.eval_addr (MC.th_id current) (MC.th_env current) ptr = Some addr ->
      source_store trace source_idx ty addr value ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory shared trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current) rest
                (MS.env_set (MC.th_env current) dst value) :: after)
            memory
            shared
            (trace ++
              [(MC.th_id current,
                M.EvAtomicLoadAcquire ty addr value)]))
          (rf_set rf (length trace) source_idx))
| RelaxedLoadShared :
    forall threads before current after memory shared trace rf
           rest dst ptr ty addr value source_idx,
      split_first_barrier_blocked trace threads =
        Some (before, current, after) ->
      MC.th_code current = M.SLoadShared dst ptr ty :: rest ->
      MS.eval_addr (MC.th_id current) (MC.th_env current) ptr = Some addr ->
      source_store_shared trace source_idx ty addr value ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory shared trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++
              MC.mk_thread (MC.th_id current) rest
                (MS.env_set (MC.th_env current) dst value) :: after)
            memory shared
            (trace ++
              [(MC.th_id current, M.EvLoadShared ty addr value)]))
          (rf_set rf (length trace) source_idx))
| RelaxedStoreShared :
    forall threads before current after memory shared trace rf
           rest ptr rhs ty addr value,
      split_first_barrier_blocked trace threads =
        Some (before, current, after) ->
      MC.th_code current = M.SStoreShared ptr rhs ty :: rest ->
      MS.eval_addr (MC.th_id current) (MC.th_env current) ptr = Some addr ->
      MS.eval_expr (MC.th_id current) (MC.th_env current) rhs = Some value ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory shared trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++ MC.mk_thread (MC.th_id current) rest
              (MC.th_env current) :: after)
            memory (MS.mem_write shared addr value)
            (trace ++
              [(MC.th_id current, M.EvStoreShared ty addr value)])) rf)
| RelaxedBarrierShared :
    forall threads before current after memory shared trace rf rest,
      split_first_barrier_blocked trace threads =
        Some (before, current, after) ->
      MC.th_code current = M.SBarrierShared :: rest ->
      relaxed_machine_step
        (mk_relaxed_state
          (MC.mk_machine threads memory shared trace) rf)
        (mk_relaxed_state
          (MC.mk_machine
            (before ++ MC.mk_thread (MC.th_id current) rest
              (MC.th_env current) :: after)
            memory shared
            (trace ++ [(MC.th_id current, M.EvBarrierShared)])) rf).

Inductive relaxed_state_steps : relaxed_state -> relaxed_state -> Prop :=
| RelaxedDone : forall state,
    relaxed_state_steps state state
| RelaxedMore : forall state state' final,
    relaxed_machine_step state state' ->
    relaxed_state_steps state' final ->
    relaxed_state_steps state final.

(** The original scheduler remains terminal on completed thread lists. *)
Lemma split_first_runnable_all_done : forall threads,
  threads_done threads -> split_first_runnable threads = None.
Proof.
  intros threads Hdone. induction Hdone as [|thread threads Hthread _ IH].
  - reflexivity.
  - unfold thread_done in Hthread. cbn. rewrite Hthread, IH. reflexivity.
Qed.

Lemma split_first_barrier_blocked_all_done : forall trace threads,
  threads_done threads -> split_first_barrier_blocked trace threads = None.
Proof.
  intros trace threads Hdone.
  assert (Hnone : no_thread_has_shared_barrier threads).
  { induction Hdone as [|thread threads Hthread _ IH].
    - constructor.
    - constructor; [unfold thread_done in Hthread; rewrite Hthread; reflexivity|].
      exact IH. }
  rewrite scheduler_coincides_no_shared_barrier by exact Hnone.
  now apply split_first_runnable_all_done.
Qed.

(** A completed machine is terminal under the canonical scheduler. *)
Lemma all_done_no_step : forall machine rf next,
  all_done machine ->
  relaxed_machine_step (mk_relaxed_state machine rf) next ->
  False.
Proof.
  intros [threads memory shared trace] rf next Hdone Hstep. cbn in *.
  pose proof (split_first_barrier_blocked_all_done trace threads Hdone) as Hnone.
  inversion Hstep; subst;
    match goal with
    | Hsplit : split_first_barrier_blocked trace threads = Some _ |- _ =>
        rewrite Hnone in Hsplit; discriminate
    end.
Qed.

Definition relaxed_machine_steps
    (initial final : MC.machine) (rf : R.rf_map) : Prop :=
  relaxed_state_steps
    (mk_relaxed_state initial empty_rf)
    (mk_relaxed_state final rf).

End MIRRelaxed.
