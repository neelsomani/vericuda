From Coq Require Import ZArith List String Bool Lia Relation_Operators
  FunctionalExtensionality.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax MIRSemantics MIRRun MIRConcurrent MIRRelaxed.
Require Import PTXEvents PTXRelations PTXHB Translate.

(** The fixed eight-thread tree reduction.

    [VF32] values in this development are raw bit patterns, and the combining
    operation is the development's existing bit-pattern addition.  The
    determinism result is about uniqueness of the combining tree, not about
    floating-point arithmetic.  The input at thread [t] is the distinct raw
    payload [Z.of_nat t + 1], making stale reads observably different. *)
Module Reduction.

Module M := MIR.
Module MS := MIRSemantics.
Module MR := MIRRun.
Module MC := MIRConcurrent.
Module RM := MIRRelaxed.
Module R := PTXRelations.
Module H := PTXHB.
Module T := Translate.
Module P := PTX.

Definition nthreads : nat := 8%nat.
Definition nrounds : Z := 3.

Definition u32 (z : Z) : M.expr := M.EVal (M.VU32 z).
Definition input_expr (t : nat) : M.expr :=
  M.EVal (M.VF32 (Z.of_nat t + 1)).
Definition shared_ptr (offset : M.expr) : M.expr :=
  M.EPtrAdd (M.EVal (M.VU64 0)) offset.
Definition stride_expr : M.expr := M.EShr (u32 4) (M.EVar "s").

(** One unrolled reduction round.  It says nothing about IEEE arithmetic;
    [EAdd] delegates to the existing raw-payload operation. *)
Definition reduction_round : list M.stmt :=
  [M.SIf (M.ELt M.ETid stride_expr)
    [M.SLoadShared "a" (shared_ptr M.ETid) M.TyF32;
     M.SLoadShared "b"
       (shared_ptr (M.EAdd M.ETid stride_expr)) M.TyF32;
     M.SStoreShared (shared_ptr M.ETid)
       (M.EAdd (M.EVar "a") (M.EVar "b")) M.TyF32]
    [];
   M.SBarrierShared].

(** Source form of thread [t].  Inputs are per-thread constants baked into the
    code; v1 does not model the global-to-shared staging load. *)
Definition reduction_thread (t : nat) : MC.thread :=
  MC.mk_thread t
    [M.SStoreShared (shared_ptr M.ETid) (input_expr t) M.TyF32;
     M.SBarrierShared;
     M.SFor "s" nrounds reduction_round]
    MS.empty_env.

(** Hand-written residual of the three-round static loop. *)
Definition reduction_thread_unrolled (t : nat) : list M.stmt :=
  [M.SAssign "s" (u32 0)] ++ reduction_round ++
  [M.SAssign "s" (u32 1)] ++ reduction_round ++
  [M.SAssign "s" (u32 2)] ++ reduction_round.

Lemma reduction_unroll_list :
  MS.unroll_for "s" 0 nrounds reduction_round =
  reduction_thread_unrolled 0%nat.
Proof. reflexivity. Qed.

(** One per-thread [SFor] step performs the complete static expansion.  The
    bound [t < 8] records the kernel domain but is not needed by unfolding. *)
Lemma reduction_unrolls : forall t,
  (t < nthreads)%nat ->
  MS.step t
    (MS.mk_cfg [M.SFor "s" nrounds reduction_round] MS.empty_env MS.empty_mem)
    None
    (MS.mk_cfg (reduction_thread_unrolled t) MS.empty_env MS.empty_mem).
Proof.
  intros t _. apply MS.StepForUnfold. unfold nrounds. lia.
Qed.

Definition reduction_threads : list MC.thread :=
  [reduction_thread 0%nat; reduction_thread 1%nat;
   reduction_thread 2%nat; reduction_thread 3%nat;
   reduction_thread 4%nat; reduction_thread 5%nat;
   reduction_thread 6%nat; reduction_thread 7%nat].

Definition reduction_initial_machine : MC.machine :=
  MC.mk_machine reduction_threads MS.empty_mem MS.empty_mem [].

Definition store_shared_event
    (tid addr : nat) (value : Z) : nat * M.event_mir :=
  (tid, M.EvStoreShared M.TyF32 (Z.of_nat addr) (M.VF32 value)).
Definition load_shared_event
    (tid addr : nat) (value : Z) : nat * M.event_mir :=
  (tid, M.EvLoadShared M.TyF32 (Z.of_nat addr) (M.VF32 value)).
Definition shared_barrier_event (tid : nat) : nat * M.event_mir :=
  (tid, M.EvBarrierShared).

Definition barrier_round : list (nat * M.event_mir) :=
  [shared_barrier_event 0; shared_barrier_event 1;
   shared_barrier_event 2; shared_barrier_event 3;
   shared_barrier_event 4; shared_barrier_event 5;
   shared_barrier_event 6; shared_barrier_event 7].

(** The unique 61-event canonical trace: eight initial stores and a barrier,
    then 12, 6, and 3 shared-memory operations in the three rounds, each
    followed by an eight-thread barrier round. *)
Definition reduction_final_trace : list (nat * M.event_mir) :=
  [store_shared_event 0 0 1; store_shared_event 1 1 2;
   store_shared_event 2 2 3; store_shared_event 3 3 4;
   store_shared_event 4 4 5; store_shared_event 5 5 6;
   store_shared_event 6 6 7; store_shared_event 7 7 8] ++
  barrier_round ++
  [load_shared_event 0 0 1; load_shared_event 0 4 5;
   store_shared_event 0 0 6;
   load_shared_event 1 1 2; load_shared_event 1 5 6;
   store_shared_event 1 1 8;
   load_shared_event 2 2 3; load_shared_event 2 6 7;
   store_shared_event 2 2 10;
   load_shared_event 3 3 4; load_shared_event 3 7 8;
   store_shared_event 3 3 12] ++
  barrier_round ++
  [load_shared_event 0 0 6; load_shared_event 0 2 10;
   store_shared_event 0 0 16;
   load_shared_event 1 1 8; load_shared_event 1 3 12;
   store_shared_event 1 1 20] ++
  barrier_round ++
  [load_shared_event 0 0 16; load_shared_event 0 1 20;
   store_shared_event 0 0 36] ++
  barrier_round.

Definition reduction_result : Z := 36.

(** Gate-free stale execution: the first stride-2 load at event 36 reads the
    initialization store at event 0, producing 1 instead of 6.  Later loads
    use the newest available stores, so the final payload becomes 31. *)
Definition reduction_stale_trace : list (nat * M.event_mir) :=
  firstn 36 reduction_final_trace ++
  [load_shared_event 0 0 1; load_shared_event 0 2 10;
   store_shared_event 0 0 11;
   load_shared_event 1 1 8; load_shared_event 1 3 12;
   store_shared_event 1 1 20] ++
  barrier_round ++
  [load_shared_event 0 0 11; load_shared_event 0 1 20;
   store_shared_event 0 0 31] ++
  barrier_round.

Lemma reduction_final_trace_length :
  List.length reduction_final_trace = 61%nat.
Proof. reflexivity. Qed.

(** Concrete round-structure regression.  Filtering out all non-barrier events
    yields exactly four complete id-ordered rounds. *)
Definition is_shared_barrier_event (tagged : nat * M.event_mir) : bool :=
  match snd tagged with M.EvBarrierShared => true | _ => false end.

Lemma barrier_round_structure :
  filter is_shared_barrier_event reduction_final_trace =
  (barrier_round ++ barrier_round ++ barrier_round ++ barrier_round)%list.
Proof. reflexivity. Qed.

Lemma tid_at_implies_in_map : forall trace idx tid,
  R.tid_at trace idx = Some tid -> In tid (map fst trace).
Proof.
  induction trace as [|[head_tid event] trace IH]; intros idx tid Htid.
  - destruct idx; discriminate.
  - destruct idx as [|idx].
    + cbn in Htid. inversion Htid; subst. now left.
    + right. cbn [R.tid_at R.tagged_event_at] in Htid.
      apply (IH idx tid). exact Htid.
Qed.

Lemma reduction_trace_tid_cases : forall tid,
  (exists idx, R.tid_at (T.translate_trace reduction_final_trace) idx =
    Some tid) ->
  tid = 0%nat \/ tid = 1%nat \/ tid = 2%nat \/ tid = 3%nat \/
  tid = 4%nat \/ tid = 5%nat \/ tid = 6%nat \/ tid = 7%nat.
Proof.
  intros tid [idx Htid].
  apply tid_at_implies_in_map in Htid.
  cbv [T.translate_trace reduction_final_trace barrier_round
       store_shared_event load_shared_event shared_barrier_event] in Htid.
  cbn in Htid.
  repeat (destruct Htid as [Htid | Htid]; [subst; tauto |]).
  contradiction.
Qed.

(** The concrete trace is barrier-uniform by computation.  This is not a
    source-level divergence-freedom theorem. *)
Lemma reduction_barrier_uniform :
  H.barrier_uniform (T.translate_trace reduction_final_trace).
Proof.
  unfold H.barrier_uniform.
  intros t t' Ht Ht'.
  destruct (reduction_trace_tid_cases t Ht) as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  destruct (reduction_trace_tid_cases t' Ht') as
    [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
  reflexivity.
Qed.

Ltac reduction_equalities :=
  repeat match goal with
  | H : Some _ = Some _ |- _ => inversion H; clear H; subst
  | H : (_, _) = (_, _) |- _ => inversion H; clear H; subst
  | H : _ :: _ = _ :: _ |- _ => inversion H; clear H; subst
  end.

Ltac reduction_resolve_shared_source Hsource :=
  inversion Hsource as [source_tid Hnth]; subst; clear Hsource;
  repeat lazymatch type of Hnth with
  | nth_error (_ :: _) ?source_idx = Some _ =>
      destruct source_idx as [|source_idx];
      [cbn in Hnth; inversion Hnth; clear Hnth; subst
      |cbn in Hnth]
  | nth_error [] ?source_idx = Some _ =>
      destruct source_idx; discriminate
  end.

Definition mir_ty_eqb (left right : M.mir_ty) : bool :=
  match left, right with
  | M.TyI32, M.TyI32 | M.TyU32, M.TyU32 | M.TyF32, M.TyF32
  | M.TyU64, M.TyU64 | M.TyBool, M.TyBool => true
  | _, _ => false
  end.

(** Executable source lookup used only to construct the negative witness. *)
Definition shared_source_value
    (trace : list (nat * M.event_mir)) (source_idx : nat)
    (ty : M.mir_ty) (addr : M.addr) : option M.val :=
  match nth_error trace source_idx with
  | Some (_, M.EvStoreShared source_ty source_addr value) =>
      if mir_ty_eqb source_ty ty && Z.eqb source_addr addr
      then Some value else None
  | _ => None
  end.

Definition source_value
    (trace : list (nat * M.event_mir)) (source_idx : nat)
    (ty : M.mir_ty) (addr : M.addr) : option M.val :=
  match nth_error trace source_idx with
  | Some (_, M.EvStore source_ty source_addr value)
  | Some (_, M.EvAtomicStoreRelease source_ty source_addr value) =>
      if mir_ty_eqb source_ty ty && Z.eqb source_addr addr
      then Some value else None
  | _ => None
  end.

Lemma mir_ty_eqb_refl : forall ty, mir_ty_eqb ty ty = true.
Proof. destruct ty; reflexivity. Qed.

Lemma shared_source_value_sound : forall trace source_idx ty addr value,
  shared_source_value trace source_idx ty addr = Some value ->
  RM.source_store_shared trace source_idx ty addr value.
Proof.
  intros trace source_idx ty addr value Hlookup.
  unfold shared_source_value in Hlookup.
  destruct (nth_error trace source_idx) as [[tid event]|] eqn:Hnth;
    try discriminate.
  destruct event as
    [event_ty event_addr event_value
    |event_ty event_addr event_value
    |event_ty event_addr event_value
    |event_ty event_addr event_value
    |
    |event_ty event_addr event_value
    |source_ty source_addr source_value
    |]; try discriminate.
  destruct source_ty; destruct ty; cbn in Hlookup; try discriminate;
    destruct (Z.eqb source_addr addr) eqn:Haddr; try discriminate;
    apply Z.eqb_eq in Haddr; subst;
    inversion Hlookup; subst;
    now apply RM.SourceShared with (tid := tid).
Qed.

Lemma shared_source_value_complete : forall trace source_idx ty addr value,
  RM.source_store_shared trace source_idx ty addr value ->
  shared_source_value trace source_idx ty addr = Some value.
Proof.
  intros trace source_idx ty addr value Hsource.
  inversion Hsource as [tid Hnth]; subst.
  unfold shared_source_value. rewrite Hnth, mir_ty_eqb_refl, Z.eqb_refl.
  reflexivity.
Qed.

Lemma source_value_sound : forall trace source_idx ty addr value,
  source_value trace source_idx ty addr = Some value ->
  RM.source_store trace source_idx ty addr value.
Proof.
  intros trace source_idx ty addr value Hlookup.
  unfold source_value in Hlookup.
  destruct (nth_error trace source_idx) as [[tid event]|] eqn:Hnth;
    try discriminate.
  destruct event as
    [event_ty event_addr event_value
    |source_ty source_addr source_value'
    |event_ty event_addr event_value
    |source_ty source_addr source_value'
    |
    |event_ty event_addr event_value
    |event_ty event_addr event_value
    |]; try discriminate;
  destruct source_ty; destruct ty; cbn in Hlookup; try discriminate;
  destruct (Z.eqb source_addr addr) eqn:Haddr; try discriminate;
  apply Z.eqb_eq in Haddr; subst;
  inversion Hlookup; subst.
  all: first
    [ now apply RM.SourcePlain with (tid := tid)
    | now apply RM.SourceRelease with (tid := tid) ].
Qed.

Lemma source_value_complete : forall trace source_idx ty addr value,
  RM.source_store trace source_idx ty addr value ->
  source_value trace source_idx ty addr = Some value.
Proof.
  intros trace source_idx ty addr value Hsource.
  inversion Hsource as [tid Hnth | tid Hnth]; subst;
    unfold source_value; rewrite Hnth, mir_ty_eqb_refl, Z.eqb_refl;
    reflexivity.
Qed.

Definition reduction_nonload_step
    (before : list MC.thread) (current : MC.thread)
    (after : list MC.thread) (memory shared : MS.mem)
    (trace : list (nat * M.event_mir)) (rf : R.rf_map)
    : option RM.relaxed_state :=
  match MR.step_fun (MC.th_id current)
      (MS.mk_cfg (MC.th_code current) (MC.th_env current) memory) with
  | Some (oev, next) =>
      Some (RM.mk_relaxed_state
        (MC.mk_machine
          (before ++ MC.mk_thread (MC.th_id current)
            (MS.cfg_code next) (MS.cfg_env next) :: after)
          (MS.cfg_mem next) shared
          (MC.append_event (MC.th_id current) oev trace)) rf)
  | None => None
  end.

(** A small executable presentation of the subset needed by this kernel.  Its
    [source_idx] argument makes the reads-from choice explicit. *)
Definition reduction_candidate_step
    (source_idx : nat) (state : RM.relaxed_state)
    : option RM.relaxed_state :=
  let machine := RM.relaxed_mach state in
  let threads := MC.mach_threads machine in
  let memory := MC.mach_mem machine in
  let shared := MC.mach_shared machine in
  let trace := MC.mach_trace machine in
  let rf := RM.relaxed_rf state in
  match RM.split_first_barrier_blocked trace threads with
  | None => None
  | Some (before, current, after) =>
      match MC.th_code current with
      | M.SLoad dst ptr ty :: rest =>
          match MS.eval_addr (MC.th_id current) (MC.th_env current) ptr with
          | None => None
          | Some addr =>
              match source_value trace source_idx ty addr with
              | None => None
              | Some value =>
                  Some (RM.mk_relaxed_state
                    (MC.mk_machine
                      (before ++ MC.mk_thread (MC.th_id current) rest
                        (MS.env_set (MC.th_env current) dst value) :: after)
                      memory shared
                      (trace ++ [(MC.th_id current,
                        M.EvLoad ty addr value)]))
                    (RM.rf_set rf (List.length trace) source_idx))
              end
          end
      | M.SAtomicLoadAcquire dst ptr ty :: rest =>
          match MS.eval_addr (MC.th_id current) (MC.th_env current) ptr with
          | None => None
          | Some addr =>
              match source_value trace source_idx ty addr with
              | None => None
              | Some value =>
                  Some (RM.mk_relaxed_state
                    (MC.mk_machine
                      (before ++ MC.mk_thread (MC.th_id current) rest
                        (MS.env_set (MC.th_env current) dst value) :: after)
                      memory shared
                      (trace ++ [(MC.th_id current,
                        M.EvAtomicLoadAcquire ty addr value)]))
                    (RM.rf_set rf (List.length trace) source_idx))
              end
          end
      | M.SLoadShared dst ptr ty :: rest =>
          match MS.eval_addr (MC.th_id current) (MC.th_env current) ptr with
          | None => None
          | Some addr =>
              match shared_source_value trace source_idx ty addr with
              | None => None
              | Some value =>
                  Some (RM.mk_relaxed_state
                    (MC.mk_machine
                      (before ++ MC.mk_thread (MC.th_id current) rest
                        (MS.env_set (MC.th_env current) dst value) :: after)
                      memory shared
                      (trace ++ [(MC.th_id current,
                        M.EvLoadShared ty addr value)]))
                    (RM.rf_set rf (List.length trace) source_idx))
              end
          end
      | M.SStoreShared ptr rhs ty :: rest =>
          match MS.eval_addr (MC.th_id current) (MC.th_env current) ptr,
                MS.eval_expr (MC.th_id current) (MC.th_env current) rhs with
          | Some addr, Some value =>
              Some (RM.mk_relaxed_state
                (MC.mk_machine
                  (before ++ MC.mk_thread (MC.th_id current) rest
                    (MC.th_env current) :: after)
                  memory (MS.mem_write shared addr value)
                  (trace ++ [(MC.th_id current,
                    M.EvStoreShared ty addr value)])) rf)
          | _, _ => None
          end
      | M.SBarrierShared :: rest =>
          Some (RM.mk_relaxed_state
            (MC.mk_machine
              (before ++ MC.mk_thread (MC.th_id current) rest
                (MC.th_env current) :: after)
              memory shared
              (trace ++ [(MC.th_id current, M.EvBarrierShared)])) rf)
      | [] => None
      | _ :: _ =>
          reduction_nonload_step before current after memory shared trace rf
      end
  end.

Lemma reduction_nonload_step_sound :
  forall threads before current after memory shared trace rf next,
    RM.split_first_barrier_blocked trace threads =
      Some (before, current, after) ->
    RM.non_load_head (MC.th_code current) ->
    reduction_nonload_step before current after memory shared trace rf =
      Some next ->
    RM.relaxed_machine_step
      (RM.mk_relaxed_state
        (MC.mk_machine threads memory shared trace) rf) next.
Proof.
  intros threads before current after memory shared trace rf next
    Hscheduled Hhead Hstep.
  unfold reduction_nonload_step in Hstep.
  destruct (MR.step_fun (MC.th_id current)
    (MS.mk_cfg (MC.th_code current) (MC.th_env current) memory))
    as [[oev stepped]|] eqn:Hfun; try discriminate.
  inversion Hstep; subst.
  eapply RM.RelaxedNonLoad with
    (threads := threads) (before := before) (current := current)
    (after := after) (memory := memory) (shared := shared)
    (trace := trace) (rf := rf) (oev := oev) (next := stepped).
  - exact Hscheduled.
  - exact Hhead.
  - now apply MR.step_fun_sound in Hfun.
Qed.

Lemma reduction_nonload_step_complete :
  forall before current after memory shared trace rf oev stepped,
    MS.step (MC.th_id current)
      (MS.mk_cfg (MC.th_code current) (MC.th_env current) memory)
      oev stepped ->
    reduction_nonload_step before current after memory shared trace rf =
      Some (RM.mk_relaxed_state
        (MC.mk_machine
          (before ++ MC.mk_thread (MC.th_id current)
            (MS.cfg_code stepped) (MS.cfg_env stepped) :: after)
          (MS.cfg_mem stepped) shared
          (MC.append_event (MC.th_id current) oev trace)) rf).
Proof.
  intros before current after memory shared trace rf oev stepped Hstep.
  unfold reduction_nonload_step.
  rewrite (MR.step_fun_complete _ _ _ _ Hstep). reflexivity.
Qed.

Lemma reduction_candidate_step_sound : forall source_idx state next,
  reduction_candidate_step source_idx state = Some next ->
  RM.relaxed_machine_step state next.
Proof.
  intros source_idx [[threads memory shared trace] rf] next Hstep.
  unfold reduction_candidate_step in Hstep; cbn in Hstep.
  destruct (RM.split_first_barrier_blocked trace threads)
    as [[[before current] after]|] eqn:Hscheduled; try discriminate.
  destruct current as [tid code rho]. cbn in *.
  destruct code as [|instruction rest]; try discriminate.
  destruct instruction as
    [assign_x assign_rhs
    |dst ptr ty
    |store_ptr store_rhs store_ty
    |dst ptr ty
    |atomic_store_ptr atomic_store_rhs atomic_store_ty
    |
    |dst ptr ty
    |ptr rhs ty
    |
    |condition yes no
    |body
    |counter bound body]; cbn in Hstep.
  all: try solve [
    eapply reduction_nonload_step_sound;
      [exact Hscheduled | exact I | exact Hstep]].
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr;
      try discriminate.
    destruct (source_value trace source_idx ty addr)
      as [value|] eqn:Hsource; try discriminate.
    inversion Hstep; subst.
    eapply RM.RelaxedLoad with
      (threads := threads) (before := before)
      (current := MC.mk_thread tid (M.SLoad dst ptr ty :: rest) rho)
      (after := after) (memory := memory) (shared := shared)
      (trace := trace) (rf := rf) (rest := rest) (dst := dst)
      (ptr := ptr) (ty := ty) (addr := addr) (value := value)
      (source_idx := source_idx);
      [exact Hscheduled | reflexivity | exact Haddr |
       now eapply source_value_sound].
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr;
      try discriminate.
    destruct (source_value trace source_idx ty addr)
      as [value|] eqn:Hsource; try discriminate.
    inversion Hstep; subst.
    eapply RM.RelaxedAtomicLoadAcquire with
      (threads := threads) (before := before)
      (current := MC.mk_thread tid
        (M.SAtomicLoadAcquire dst ptr ty :: rest) rho)
      (after := after) (memory := memory) (shared := shared)
      (trace := trace) (rf := rf) (rest := rest) (dst := dst)
      (ptr := ptr) (ty := ty) (addr := addr) (value := value)
      (source_idx := source_idx);
      [exact Hscheduled | reflexivity | exact Haddr |
       now eapply source_value_sound].
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr;
      try discriminate.
    destruct (shared_source_value trace source_idx ty addr)
      as [value|] eqn:Hsource; try discriminate.
    inversion Hstep; subst.
    eapply RM.RelaxedLoadShared with
      (threads := threads) (before := before)
      (current := MC.mk_thread tid (M.SLoadShared dst ptr ty :: rest) rho)
      (after := after) (memory := memory) (shared := shared)
      (trace := trace) (rf := rf) (rest := rest) (dst := dst)
      (ptr := ptr) (ty := ty) (addr := addr) (value := value)
      (source_idx := source_idx);
      [exact Hscheduled | reflexivity | exact Haddr |
       now eapply shared_source_value_sound].
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr;
      try discriminate.
    destruct (MS.eval_expr tid rho rhs) as [value|] eqn:Hvalue;
      try discriminate.
    inversion Hstep; subst.
    eapply RM.RelaxedStoreShared with
      (threads := threads) (before := before)
      (current := MC.mk_thread tid (M.SStoreShared ptr rhs ty :: rest) rho)
      (after := after) (memory := memory) (shared := shared)
      (trace := trace) (rf := rf) (rest := rest) (ptr := ptr)
      (rhs := rhs) (ty := ty) (addr := addr) (value := value);
      [exact Hscheduled | reflexivity | exact Haddr | exact Hvalue].
  - inversion Hstep; subst.
    eapply RM.RelaxedBarrierShared with
      (threads := threads) (before := before)
      (current := MC.mk_thread tid (M.SBarrierShared :: rest) rho)
      (after := after) (memory := memory) (shared := shared)
      (trace := trace) (rf := rf) (rest := rest);
      [exact Hscheduled | reflexivity].
Qed.

Lemma reduction_candidate_step_complete : forall state next,
  RM.relaxed_machine_step state next ->
  exists source_idx,
    reduction_candidate_step source_idx state = Some next.
Proof.
  intros state next Hstep. inversion Hstep; subst.
  - exists 0%nat. unfold reduction_candidate_step; cbn.
    rewrite H. destruct current as [tid code rho]. cbn in *.
    destruct code as [|instruction rest]; try contradiction.
    destruct instruction; try contradiction;
      now apply reduction_nonload_step_complete.
  - exists source_idx. unfold reduction_candidate_step; cbn.
    rewrite H, H0, H1, (source_value_complete _ _ _ _ _ H2).
    reflexivity.
  - exists source_idx. unfold reduction_candidate_step; cbn.
    rewrite H, H0, H1, (source_value_complete _ _ _ _ _ H2).
    reflexivity.
  - exists source_idx. unfold reduction_candidate_step; cbn.
    rewrite H, H0, H1, (shared_source_value_complete _ _ _ _ _ H2).
    reflexivity.
  - exists 0%nat. unfold reduction_candidate_step; cbn.
    rewrite H, H0, H1, H2. reflexivity.
  - exists 0%nat. unfold reduction_candidate_step; cbn.
    rewrite H, H0. reflexivity.
Qed.

Inductive reduction_candidate_state_steps
    : RM.relaxed_state -> RM.relaxed_state -> Prop :=
| ReductionCandidateDone : forall state,
    reduction_candidate_state_steps state state
| ReductionCandidateMore : forall state next final source_idx,
    reduction_candidate_step source_idx state = Some next ->
    reduction_candidate_state_steps next final ->
    reduction_candidate_state_steps state final.

Lemma reduction_candidate_steps_sound : forall first second,
  reduction_candidate_state_steps first second ->
  RM.relaxed_state_steps first second.
Proof.
  intros first second Hsteps. induction Hsteps.
  - apply RM.RelaxedDone.
  - eapply RM.RelaxedMore.
    + exact (reduction_candidate_step_sound _ _ _ H).
    + exact IHHsteps.
Qed.

Lemma reduction_candidate_steps_complete : forall first second,
  RM.relaxed_state_steps first second ->
  reduction_candidate_state_steps first second.
Proof.
  intros first second Hsteps. induction Hsteps.
  - apply ReductionCandidateDone.
  - destruct (reduction_candidate_step_complete _ _ H) as [source_idx Hsource].
    eapply ReductionCandidateMore; eauto.
Qed.

Definition reduction_stale_source (event_idx : nat) : nat :=
  match event_idx with
  | 16%nat => 0%nat | 17%nat => 4%nat
  | 19%nat => 1%nat | 20%nat => 5%nat
  | 22%nat => 2%nat | 23%nat => 6%nat
  | 25%nat => 3%nat | 26%nat => 7%nat
  | 36%nat => 0%nat | 37%nat => 24%nat
  | 39%nat => 21%nat | 40%nat => 27%nat
  | 50%nat => 38%nat | 51%nat => 41%nat
  | _ => 0%nat
  end.

Fixpoint reduction_candidate_run
    (fuel : nat) (state : RM.relaxed_state) : RM.relaxed_state :=
  match fuel with
  | O => state
  | S fuel' =>
      let source_idx := reduction_stale_source
        (List.length (MC.mach_trace (RM.relaxed_mach state))) in
      match reduction_candidate_step source_idx state with
      | Some next => reduction_candidate_run fuel' next
      | None => state
      end
  end.

(** The source map for the canonical reduction execution.  It differs from
    [reduction_stale_source] exactly at event 36, where consistency forces the
    post-barrier overwrite at event 18 rather than the initial store. *)
Definition reduction_canonical_source (event_idx : nat) : nat :=
  match event_idx with
  | 16%nat => 0%nat | 17%nat => 4%nat
  | 19%nat => 1%nat | 20%nat => 5%nat
  | 22%nat => 2%nat | 23%nat => 6%nat
  | 25%nat => 3%nat | 26%nat => 7%nat
  | 36%nat => 18%nat | 37%nat => 24%nat
  | 39%nat => 21%nat | 40%nat => 27%nat
  | 50%nat => 38%nat | 51%nat => 41%nat
  | _ => 0%nat
  end.

Fixpoint reduction_canonical_run
    (fuel : nat) (state : RM.relaxed_state) : RM.relaxed_state :=
  match fuel with
  | O => state
  | S fuel' =>
      let source_idx := reduction_canonical_source
        (List.length (MC.mach_trace (RM.relaxed_mach state))) in
      match reduction_candidate_step source_idx state with
      | Some next => reduction_canonical_run fuel' next
      | None => state
      end
  end.

(** Opaque proof checkpoints keep normalization of the 103-step execution
    bounded.  Each state advances ten deterministic candidate steps. *)
Definition reduction_state_0 : RM.relaxed_state :=
  Eval vm_compute in
    RM.mk_relaxed_state reduction_initial_machine RM.empty_rf.
Definition reduction_state_10 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_0.
Definition reduction_state_20 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_10.
Definition reduction_state_30 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_20.
Definition reduction_state_40 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_30.
Definition reduction_state_50 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_40.
Definition reduction_state_60 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_50.
Definition reduction_state_70 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_60.
Definition reduction_state_80 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_70.
Definition reduction_state_90 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_80.
Definition reduction_state_95 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 5%nat reduction_state_90.
Definition reduction_state_100 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 5%nat reduction_state_95.
Definition reduction_state_110 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 10%nat reduction_state_100.
Definition reduction_state_117 : RM.relaxed_state :=
  Eval vm_compute in reduction_canonical_run 7%nat reduction_state_110.

Lemma reduction_candidate_run_sound : forall fuel state,
  RM.relaxed_state_steps state (reduction_candidate_run fuel state).
Proof.
  induction fuel as [|fuel IH]; intros state; cbn.
  - apply RM.RelaxedDone.
  - destruct (reduction_candidate_step
      (reduction_stale_source
        (List.length (MC.mach_trace (RM.relaxed_mach state)))) state)
      as [next|] eqn:Hstep.
    + eapply RM.RelaxedMore.
      * exact (reduction_candidate_step_sound _ _ _ Hstep).
      * apply IH.
    + apply RM.RelaxedDone.
Qed.

Lemma relaxed_state_steps_trans : forall first second third,
  RM.relaxed_state_steps first second ->
  RM.relaxed_state_steps second third ->
  RM.relaxed_state_steps first third.
Proof.
  intros first second third Hfirst Hsecond.
  induction Hfirst.
  - exact Hsecond.
  - eapply RM.RelaxedMore; eauto.
Qed.

Lemma relaxed_machine_step_trace_extension : forall first second,
  RM.relaxed_machine_step first second ->
  exists suffix,
    MC.mach_trace (RM.relaxed_mach second) =
      List.app (MC.mach_trace (RM.relaxed_mach first)) suffix.
Proof.
  intros first second Hstep. inversion Hstep; subst; cbn.
  - unfold MC.append_event. destruct oev.
    + eexists. reflexivity.
    + exists []. now rewrite app_nil_r.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
  - eexists. reflexivity.
Qed.

Lemma relaxed_state_steps_trace_extension : forall first second,
  RM.relaxed_state_steps first second ->
  exists suffix,
    MC.mach_trace (RM.relaxed_mach second) =
      List.app (MC.mach_trace (RM.relaxed_mach first)) suffix.
Proof.
  intros first second Hsteps. induction Hsteps.
  - exists []. now rewrite app_nil_r.
  - destruct (relaxed_machine_step_trace_extension _ _ H) as [one Hone].
    destruct IHHsteps as [rest Hrest]. exists (List.app one rest).
    rewrite Hrest, Hone, app_assoc. reflexivity.
Qed.

Lemma relaxed_machine_step_rf_preserved_before : forall first second,
  RM.relaxed_machine_step first second ->
  forall idx,
    (idx < List.length (MC.mach_trace (RM.relaxed_mach first)))%nat ->
    RM.relaxed_rf second idx = RM.relaxed_rf first idx.
Proof.
  intros first second Hstep idx Hidx.
  inversion Hstep; subst; cbn in *; try reflexivity.
  all: unfold RM.rf_set;
    destruct (Nat.eqb idx (List.length trace)) eqn:Heq;
    [apply Nat.eqb_eq in Heq; lia | reflexivity].
Qed.

Lemma relaxed_state_steps_rf_preserved_before : forall first second,
  RM.relaxed_state_steps first second ->
  forall idx,
    (idx < List.length (MC.mach_trace (RM.relaxed_mach first)))%nat ->
    RM.relaxed_rf second idx = RM.relaxed_rf first idx.
Proof.
  intros first second Hsteps. induction Hsteps; intros idx Hidx.
  - reflexivity.
  - transitivity (RM.relaxed_rf state' idx).
    + apply IHHsteps.
      destruct (relaxed_machine_step_trace_extension _ _ H) as [suffix Htrace].
      rewrite Htrace, app_length. lia.
    + now eapply relaxed_machine_step_rf_preserved_before.
Qed.

Definition reduction_stale_final_state : RM.relaxed_state :=
  reduction_candidate_run 117%nat
    (RM.mk_relaxed_state reduction_initial_machine RM.empty_rf).

(** Search stops as soon as the requested event is present, avoiding a second
    normalization of the entire final trace in the negative proof. *)
Fixpoint reduction_candidate_find_event
    (fuel idx : nat) (state : RM.relaxed_state)
    : option (nat * M.event_mir) :=
  match nth_error (MC.mach_trace (RM.relaxed_mach state)) idx with
  | Some event => Some event
  | None =>
      match fuel with
      | O => None
      | S fuel' =>
          let source_idx := reduction_stale_source
            (List.length (MC.mach_trace (RM.relaxed_mach state))) in
          match reduction_candidate_step source_idx state with
          | Some next => reduction_candidate_find_event fuel' idx next
          | None => None
          end
      end
  end.

Lemma reduction_candidate_find_event_sound : forall fuel idx state event,
  reduction_candidate_find_event fuel idx state = Some event ->
  nth_error
    (MC.mach_trace
      (RM.relaxed_mach (reduction_candidate_run fuel state))) idx =
    Some event.
Proof.
  induction fuel as [|fuel IH]; intros idx state event Hfind.
  - cbn [reduction_candidate_find_event] in Hfind.
    destruct (nth_error (MC.mach_trace (RM.relaxed_mach state)) idx)
      as [present|] eqn:Hpresent; try discriminate.
    inversion Hfind; subst. cbn [reduction_candidate_run]. exact Hpresent.
  - cbn [reduction_candidate_find_event] in Hfind.
    destruct (nth_error (MC.mach_trace (RM.relaxed_mach state)) idx)
      as [present|] eqn:Hpresent.
    + inversion Hfind; subst.
      destruct (relaxed_state_steps_trace_extension _ _
        (reduction_candidate_run_sound (S fuel) state))
        as [suffix Htrace].
      rewrite Htrace, nth_error_app1.
      * exact Hpresent.
      * apply nth_error_Some. rewrite Hpresent. discriminate.
    + cbn [reduction_candidate_run].
      destruct (reduction_candidate_step
        (reduction_stale_source
          (List.length (MC.mach_trace (RM.relaxed_mach state)))) state)
        as [next|] eqn:Hstep; try discriminate.
      now eapply IH.
Qed.

Lemma reduction_stale_final_event :
  nth_error (MC.mach_trace (RM.relaxed_mach reduction_stale_final_state))
    36%nat = Some (load_shared_event 0 0 1).
Proof.
  eapply reduction_candidate_find_event_sound.
  vm_compute. reflexivity.
Qed.

Lemma relaxed_state_eta : forall state,
  RM.mk_relaxed_state (RM.relaxed_mach state) (RM.relaxed_rf state) = state.
Proof. intros [machine rf]. reflexivity. Qed.

Definition reduction_all_doneb (machine : MC.machine) : bool :=
  forallb (fun thread =>
    match MC.th_code thread with [] => true | _ => false end)
    (MC.mach_threads machine).

Fixpoint reduction_candidate_done_after
    (fuel : nat) (state : RM.relaxed_state) : bool :=
  match fuel with
  | O => reduction_all_doneb (RM.relaxed_mach state)
  | S fuel' =>
      let source_idx := reduction_stale_source
        (List.length (MC.mach_trace (RM.relaxed_mach state))) in
      match reduction_candidate_step source_idx state with
      | Some next => reduction_candidate_done_after fuel' next
      | None => reduction_all_doneb (RM.relaxed_mach state)
      end
  end.

Lemma reduction_candidate_done_after_correct : forall fuel state,
  reduction_candidate_done_after fuel state =
    reduction_all_doneb
      (RM.relaxed_mach (reduction_candidate_run fuel state)).
Proof.
  induction fuel as [|fuel IH]; intros state; cbn; [reflexivity|].
  destruct (reduction_candidate_step
    (reduction_stale_source
      (List.length (MC.mach_trace (RM.relaxed_mach state)))) state)
    as [next|] eqn:Hstep; [apply IH | reflexivity].
Qed.

Lemma reduction_stale_final_doneb :
  reduction_all_doneb (RM.relaxed_mach reduction_stale_final_state) = true.
Proof.
  change (reduction_all_doneb
    (RM.relaxed_mach
      (reduction_candidate_run 117%nat
        (RM.mk_relaxed_state reduction_initial_machine RM.empty_rf))) = true).
  rewrite <- reduction_candidate_done_after_correct.
  vm_compute. reflexivity.
Qed.

Lemma reduction_stale_final_result :
  MS.mem_read
    (MC.mach_shared (RM.relaxed_mach reduction_stale_final_state)) 0 =
  Some (M.VF32 31).
Proof. vm_compute. reflexivity. Qed.

Lemma reduction_all_doneb_sound : forall machine,
  reduction_all_doneb machine = true -> RM.all_done machine.
Proof.
  intros [threads memory shared trace] Hdone. cbn in *.
  induction threads as [|[tid code rho] threads IH]; cbn in *.
  - constructor.
  - destruct code as [|instruction rest]; try discriminate.
    constructor; [reflexivity | now apply IH].
Qed.

Lemma reduction_stale_execution_exists :
  exists final rf,
    RM.relaxed_machine_steps reduction_initial_machine final rf /\
    RM.all_done final /\
    nth_error (MC.mach_trace final) 36%nat =
      Some (load_shared_event 0 0 1).
Proof.
  exists (RM.relaxed_mach reduction_stale_final_state),
    (RM.relaxed_rf reduction_stale_final_state). split.
  - unfold RM.relaxed_machine_steps.
    rewrite relaxed_state_eta.
    exact (reduction_candidate_run_sound 117%nat
      (RM.mk_relaxed_state reduction_initial_machine RM.empty_rf)).
  - split.
    + apply reduction_all_doneb_sound. exact reduction_stale_final_doneb.
    + exact reduction_stale_final_event.
Qed.

Theorem reduction_determinism_needs_consistency :
  ~ (forall final rf,
      RM.relaxed_machine_steps reduction_initial_machine final rf ->
      RM.all_done final ->
      MC.mach_trace final = reduction_final_trace).
Proof.
  intros Hall.
  destruct reduction_stale_execution_exists as
    [final [rf [Hsteps [Hdone Hstale]]]].
  pose proof (Hall final rf Hsteps Hdone) as Hequal.
  rewrite Hequal in Hstale.
  vm_compute in Hstale. discriminate.
Qed.

Lemma reduction_stale_trace_inconsistent : forall rf,
  rf 36%nat = Some 0%nat ->
  H.consistent (T.translate_trace reduction_stale_trace) rf -> False.
Proof.
  intros rf Hrf [_ [Hoverwrite _]].
  assert (Hsource_overwrite :
    H.hb (T.translate_trace reduction_stale_trace) rf 0%nat 18%nat).
  { apply t_step. left. unfold H.po. cbn.
    split; [lia|]. exists 0%nat. repeat split; reflexivity.
  }
  assert (Hoverwrite_load :
    H.hb (T.translate_trace reduction_stale_trace) rf 18%nat 36%nat).
  { apply t_step. right. right. unfold H.bar.
    exists 28%nat, 28%nat. split.
    - unfold H.matching_barriers, H.is_barrier. cbn.
      split; [exact I|]. split; [exact I|].
      exists 0%nat, 0%nat. repeat split; reflexivity.
    - split.
      + unfold H.po. cbn. split; [lia|].
        exists 0%nat. repeat split; reflexivity.
      + unfold H.po. cbn. split; [lia|].
        exists 0%nat. repeat split; reflexivity.
  }
  exact (Hoverwrite 36%nat 0%nat 18%nat 0%Z
    Hrf eq_refl eq_refl Hsource_overwrite Hoverwrite_load).
Qed.

(** A small executable checker for exactly the [no_hb_overwrite] witness used
    by the reduction.  Its soundness is generic in the trace; concrete prefix
    checks below therefore normalize booleans rather than large HB proofs. *)
Definition option_nat_eqb (value : option nat) (expected : nat) : bool :=
  match value with
  | Some found => Nat.eqb found expected
  | None => false
  end.

Definition option_Z_eqb (value : option Z) (expected : Z) : bool :=
  match value with
  | Some found => Z.eqb found expected
  | None => false
  end.

Definition is_store_to_b (trace : R.trace) (idx : nat) (addr : Z) : bool :=
  match R.event_at trace idx with
  | Some (P.EvStore _ _ _ _ found_addr _) => Z.eqb found_addr addr
  | _ => false
  end.

Definition is_barrier_b (trace : R.trace) (idx : nat) : bool :=
  match R.event_at trace idx with
  | Some (P.EvBarrier P.ScopeCTA) => true
  | _ => false
  end.

Definition po_b (trace : R.trace) (i j : nat) : bool :=
  Nat.ltb i j &&
  match R.tid_at trace i, R.tid_at trace j with
  | Some ti, Some tj => Nat.eqb ti tj
  | _, _ => false
  end.

Definition matching_barriers_b (trace : R.trace) (i j : nat) : bool :=
  is_barrier_b trace i && is_barrier_b trace j &&
  match R.tid_at trace i, R.tid_at trace j with
  | Some ti, Some tj =>
      Nat.eqb (H.barrier_count_before trace ti i)
        (H.barrier_count_before trace tj j)
  | _, _ => false
  end.

Definition overwrite_witness_b
    (trace : R.trace) (rf : R.rf_map)
    (load_idx source_idx overwrite_idx : nat) (addr : Z)
    (bi bj : nat) : bool :=
  option_nat_eqb (rf load_idx) source_idx &&
  (option_Z_eqb (R.addr_at trace load_idx) addr &&
  (is_store_to_b trace overwrite_idx addr &&
  (po_b trace source_idx overwrite_idx &&
  (matching_barriers_b trace bi bj &&
  (po_b trace overwrite_idx bi &&
   po_b trace bj load_idx))))).

Lemma option_nat_eqb_sound : forall value expected,
  option_nat_eqb value expected = true -> value = Some expected.
Proof.
  intros [found|] expected Hcheck; cbn in Hcheck; try discriminate.
  apply Nat.eqb_eq in Hcheck. now subst.
Qed.

Lemma option_Z_eqb_sound : forall value expected,
  option_Z_eqb value expected = true -> value = Some expected.
Proof.
  intros [found|] expected Hcheck; cbn in Hcheck; try discriminate.
  apply Z.eqb_eq in Hcheck. now subst.
Qed.

Lemma is_store_to_b_sound : forall trace idx addr,
  is_store_to_b trace idx addr = true -> R.is_store_to trace idx addr.
Proof.
  intros trace idx addr Hcheck. unfold is_store_to_b in Hcheck.
  unfold R.is_store_to. destruct (R.event_at trace idx) as [event|];
    try discriminate. destruct event; try discriminate.
  cbn in Hcheck. now apply Z.eqb_eq.
Qed.

Lemma is_barrier_b_sound : forall trace idx,
  is_barrier_b trace idx = true -> H.is_barrier trace idx.
Proof.
  intros trace idx Hcheck. unfold is_barrier_b in Hcheck.
  unfold H.is_barrier. destruct (R.event_at trace idx) as [event|];
    try discriminate. destruct event; try discriminate.
  destruct sc; try discriminate. exact I.
Qed.

Lemma po_b_sound : forall trace i j,
  po_b trace i j = true -> H.po trace i j.
Proof.
  intros trace i j Hcheck. unfold po_b in Hcheck.
  apply andb_true_iff in Hcheck as [Hlt Htid].
  destruct (R.tid_at trace i) as [ti|] eqn:Hi;
    destruct (R.tid_at trace j) as [tj|] eqn:Hj; try discriminate.
  apply Nat.eqb_eq in Htid. subst tj.
  split; [now apply Nat.ltb_lt|]. exists ti. now split.
Qed.

Lemma matching_barriers_b_sound : forall trace i j,
  matching_barriers_b trace i j = true -> H.matching_barriers trace i j.
Proof.
  intros trace i j Hcheck. unfold matching_barriers_b in Hcheck.
  apply andb_true_iff in Hcheck as [Hij Hcount].
  apply andb_true_iff in Hij as [Hi Hj].
  destruct (R.tid_at trace i) as [ti|] eqn:Hti;
    destruct (R.tid_at trace j) as [tj|] eqn:Htj; try discriminate.
  apply Nat.eqb_eq in Hcount.
  split; [now apply is_barrier_b_sound|].
  split; [now apply is_barrier_b_sound|].
  exists ti, tj. repeat split; assumption.
Qed.

Lemma overwrite_witness_b_inconsistent : forall
    trace rf load_idx source_idx overwrite_idx addr bi bj,
  overwrite_witness_b trace rf load_idx source_idx overwrite_idx addr bi bj =
    true ->
  H.consistent trace rf -> False.
Proof.
  intros trace rf load_idx source_idx overwrite_idx addr bi bj
    Hcheck Hconsistent.
  destruct Hconsistent as [_ [Hno_hb_overwrite _]].
  unfold overwrite_witness_b in Hcheck.
  repeat rewrite andb_true_iff in Hcheck.
  destruct Hcheck as [Hrf [Haddr [Hstore [Hsource_overwrite
    [Hbarriers [Hoverwrite_bi Hbj_load]]]]]].
  eapply (Hno_hb_overwrite load_idx source_idx overwrite_idx addr).
  - now apply option_nat_eqb_sound.
  - now apply option_Z_eqb_sound.
  - now apply is_store_to_b_sound.
  - apply t_step. left. now apply po_b_sound.
  - apply t_step. right. right. exists bi, bj.
    split; [now apply matching_barriers_b_sound|].
    split; now apply po_b_sound.
Qed.

Ltac reduction_one_step Hstep :=
  inversion Hstep; subst; cbn in *;
  try fold MS.env_set in *;
  try fold MS.mem_write in *;
  reduction_equalities;
  try solve [contradiction | discriminate];
  try match goal with
  | Hsem : MS.step _ _ _ _ |- _ =>
      inversion Hsem; subst; cbn in *; reduction_equalities
  end;
  try match goal with
  | Hsource : RM.source_store_shared _ _ _ _ ?value |- _ =>
      reduction_resolve_shared_source Hsource
  end;
  cbn in *;
  try fold MS.env_set in *;
  try fold MS.mem_write in *;
  reduction_equalities;
  try solve [contradiction | discriminate | reflexivity].

Ltac reduction_kill_stale load_idx source_idx overwrite_idx addr bi bj :=
  match goal with
  | Hconsistent : H.consistent ?trace ?rf |- _ =>
      exfalso;
      destruct Hconsistent as [_ [Hoverwrite _]];
      eapply (Hoverwrite load_idx source_idx overwrite_idx addr);
      [ reflexivity
      | reflexivity
      | reflexivity
      | apply t_step; left; unfold H.po; cbn;
        split; [lia|]; eexists; repeat split; reflexivity
      | apply t_step; right; right; unfold H.bar;
        exists bi, bj; split;
        [ unfold H.matching_barriers, H.is_barrier; cbn;
          split; [exact I|]; split; [exact I|];
          eexists; eexists; repeat split; reflexivity
        | split;
          [ unfold H.po; cbn; split; [lia|];
            eexists; repeat split; reflexivity
          | unfold H.po; cbn; split; [lia|];
            eexists; repeat split; reflexivity ] ] ]
  end.

Ltac reduction_kill_stale_prefix
    Hrest load_idx source_idx overwrite_idx addr bi bj :=
  match goal with
  | Hconsistent : H.consistent ?final_trace ?final_rf |- _ =>
      let suffix := fresh "suffix" in
      let Htrace := fresh "Htrace" in
      destruct (relaxed_state_steps_trace_extension _ _ Hrest)
        as [suffix Htrace];
      let Hrf := fresh "Hrf" in
      pose proof
        (relaxed_state_steps_rf_preserved_before _ _ Hrest load_idx
          ltac:(cbn; lia)) as Hrf;
      let Hsource := fresh "Hsource" in
      assert (Hsource : final_rf load_idx = Some source_idx)
        by (cbn in Hrf; exact Hrf);
      exfalso;
      destruct Hconsistent as [_ [Hoverwrite _]];
      eapply (Hoverwrite load_idx source_idx overwrite_idx addr);
      [ exact Hsource
      | rewrite Htrace; reflexivity
      | rewrite Htrace; reflexivity
      | rewrite Htrace; apply t_step; left; unfold H.po; cbn;
        split; [lia|]; eexists; repeat split; reflexivity
      | rewrite Htrace; apply t_step; right; right; unfold H.bar;
        exists bi, bj; split;
        [ unfold H.matching_barriers, H.is_barrier; cbn;
          split; [exact I|]; split; [exact I|];
          eexists; eexists; repeat split; reflexivity
        | split;
          [ unfold H.po; cbn; split; [lia|];
            eexists; repeat split; reflexivity
          | unfold H.po; cbn; split; [lia|];
          eexists; repeat split; reflexivity ] ] ]
  end.

Ltac reduction_reject_overwrite
    Hrest load_idx source_idx overwrite_idx addr bi bj :=
  match goal with
  | Hconsistent : H.consistent ?final_trace ?final_rf |- _ =>
      let suffix := fresh "suffix" in
      let Htrace := fresh "Htrace" in
      destruct (relaxed_state_steps_trace_extension _ _ Hrest)
        as [suffix Htrace];
      let Hrf := fresh "Hrf" in
      pose proof
        (relaxed_state_steps_rf_preserved_before _ _ Hrest load_idx
          ltac:(cbn; lia)) as Hrf;
      let Hsource := fresh "Hsource" in
      assert (Hsource : final_rf load_idx = Some source_idx)
        by (cbn in Hrf; exact Hrf);
      let Hwitness := fresh "Hwitness" in
      assert (Hwitness : overwrite_witness_b final_trace final_rf
          load_idx source_idx overwrite_idx addr bi bj = true)
        by (rewrite Htrace; unfold overwrite_witness_b, option_nat_eqb;
            rewrite Hsource; vm_compute; reflexivity);
      exfalso;
      eapply overwrite_witness_b_inconsistent;
      [ exact Hwitness | exact Hconsistent ]
  end.

Ltac reduction_prune_stale Hrest :=
  lazymatch type of Hrest with
  | RM.relaxed_state_steps ?state _ =>
      let event_count := eval vm_compute in
        (List.length (MC.mach_trace (RM.relaxed_mach state))) in
      lazymatch event_count with
      | 37%nat => reduction_reject_overwrite Hrest
          36%nat 0%nat 18%nat 0%Z 28%nat 28%nat
      | 38%nat => reduction_reject_overwrite Hrest
          37%nat 2%nat 24%nat 2%Z 30%nat 28%nat
      | 40%nat => reduction_reject_overwrite Hrest
          39%nat 1%nat 21%nat 1%Z 29%nat 29%nat
      | 41%nat => reduction_reject_overwrite Hrest
          40%nat 3%nat 27%nat 3%Z 31%nat 29%nat
      | 51%nat => first
          [ reduction_reject_overwrite Hrest
              50%nat 0%nat 38%nat 0%Z 42%nat 42%nat
          | reduction_reject_overwrite Hrest
              50%nat 18%nat 38%nat 0%Z 42%nat 42%nat ]
      | 52%nat => first
          [ reduction_reject_overwrite Hrest
              51%nat 1%nat 41%nat 1%Z 43%nat 42%nat
          | reduction_reject_overwrite Hrest
              51%nat 21%nat 41%nat 1%Z 43%nat 42%nat ]
      end
  end.

Ltac reduction_done_contradiction Hdone :=
  lazymatch type of Hdone with
  | Forall _ [] => fail
  | Forall _ (_ :: _) =>
      inversion Hdone as [|thread threads Hthread Hthreads];
      clear Hdone; subst;
      first
        [ try unfold RM.thread_done in Hthread;
          cbn in Hthread; discriminate
        | reduction_done_contradiction Hthreads ]
  end.

Ltac reduction_finish :=
  first
    [ match goal with
      | Hdone : RM.all_done _ |- _ =>
          unfold RM.all_done, RM.threads_done in Hdone;
          cbn in Hdone; reduction_done_contradiction Hdone
      end
    | contradiction
    | discriminate
    | reflexivity
    | split; reflexivity
    | reduction_kill_stale 36%nat 0%nat 18%nat 0%Z 28%nat 28%nat
    | reduction_kill_stale 37%nat 2%nat 24%nat 2%Z 30%nat 28%nat
    | reduction_kill_stale 39%nat 1%nat 21%nat 1%Z 29%nat 29%nat
    | reduction_kill_stale 40%nat 3%nat 27%nat 3%Z 31%nat 29%nat
    | reduction_kill_stale 50%nat 0%nat 38%nat 0%Z 42%nat 42%nat
    | reduction_kill_stale 50%nat 18%nat 38%nat 0%Z 42%nat 42%nat
    | reduction_kill_stale 51%nat 1%nat 41%nat 1%Z 43%nat 42%nat
    | reduction_kill_stale 51%nat 21%nat 41%nat 1%Z 43%nat 42%nat
    ].

Ltac reduction_execution :=
  match goal with
  | Hsteps : RM.relaxed_state_steps ?initial ?final |- _ =>
      inversion Hsteps; clear Hsteps; subst
  end;
  [ cbn [RM.all_done RM.threads_done RM.thread_done
      reduction_initial_machine reduction_threads reduction_thread] in *;
    reduction_finish
  | match goal with
    | Hstep : RM.relaxed_machine_step _ _,
      Hrest : RM.relaxed_state_steps _ _ |- _ =>
        reduction_one_step Hstep;
        first [reduction_prune_stale Hrest | reduction_execution]
    end ].

Ltac reduction_candidate_source_scan Hstep fuel source_idx :=
  lazymatch fuel with
  | O => destruct source_idx; vm_compute in Hstep; discriminate
  | S ?fuel' =>
      destruct source_idx as [|source_idx];
      [ vm_compute in Hstep; try discriminate
      | reduction_candidate_source_scan Hstep fuel' source_idx ]
  end.

Ltac reduction_candidate_one_step Hstep :=
  try unfold reduction_initial_machine, reduction_threads, reduction_thread
    in Hstep;
  lazymatch type of Hstep with
  | reduction_candidate_step ?source_idx ?state = Some _ =>
      let threads := eval vm_compute in
        (MC.mach_threads (RM.relaxed_mach state)) in
      let trace := eval vm_compute in
        (MC.mach_trace (RM.relaxed_mach state)) in
      let scheduled := eval vm_compute in
        (RM.split_first_barrier_blocked trace threads) in
      lazymatch scheduled with
      | Some (_, ?current, _) =>
          let code := eval vm_compute in (MC.th_code current) in
          lazymatch code with
          | M.SLoad _ _ _ :: _ =>
              let fuel := eval cbv in (List.length trace) in
              reduction_candidate_source_scan Hstep fuel source_idx
          | M.SAtomicLoadAcquire _ _ _ :: _ =>
              let fuel := eval cbv in (List.length trace) in
              reduction_candidate_source_scan Hstep fuel source_idx
          | M.SLoadShared _ _ _ :: _ =>
              let fuel := eval cbv in (List.length trace) in
              reduction_candidate_source_scan Hstep fuel source_idx
          | _ => vm_compute in Hstep
          end
      | None => vm_compute in Hstep
      end
  end;
  inversion Hstep; clear Hstep; subst;
  try fold MS.env_set in *;
  try fold MS.mem_write in *.

Ltac reduction_prune_candidate_stale Hrest :=
  let Hrelaxed := fresh "Hrelaxed" in
  pose proof (reduction_candidate_steps_sound _ _ Hrest) as Hrelaxed;
  reduction_prune_stale Hrelaxed.

Ltac reduction_candidate_execution :=
  match goal with
  | Hsteps : reduction_candidate_state_steps ?initial ?final |- _ =>
      inversion Hsteps; clear Hsteps; subst
  end;
  [ cbn [RM.all_done RM.threads_done RM.thread_done
      reduction_initial_machine reduction_threads reduction_thread] in *;
    reduction_finish
  | match goal with
    | Hstep : reduction_candidate_step _ _ = Some _,
      Hrest : reduction_candidate_state_steps _ _ |- _ =>
        reduction_candidate_one_step Hstep;
        first
          [ reduction_prune_candidate_stale Hrest
          | reduction_candidate_execution ]
    end ].

Definition reduction_outcome (state : RM.relaxed_state) : Prop :=
  MC.mach_trace (RM.relaxed_mach state) = reduction_final_trace /\
  MS.mem_read (MC.mach_shared (RM.relaxed_mach state)) 0 =
    Some (M.VF32 reduction_result).

Fixpoint reduction_threads_doneb (threads : list MC.thread) : bool :=
  match threads with
  | [] => true
  | thread :: rest =>
      match MC.th_code thread with
      | [] => reduction_threads_doneb rest
      | _ :: _ => false
      end
  end.

Lemma reduction_threads_doneb_of_done : forall threads,
  RM.threads_done threads -> reduction_threads_doneb threads = true.
Proof.
  intros threads Hdone. induction Hdone as [|thread threads Hthread _ IH].
  - reflexivity.
  - unfold RM.thread_done in Hthread. cbn [reduction_threads_doneb].
    rewrite Hthread. exact IH.
Qed.

Lemma reduction_not_done_of_bool_false : forall machine,
  reduction_threads_doneb (MC.mach_threads machine) = false ->
  ~ RM.all_done machine.
Proof.
  intros machine Hfalse Hdone.
  unfold RM.all_done in Hdone.
  pose proof (reduction_threads_doneb_of_done _ Hdone) as Htrue.
  rewrite Hfalse in Htrue. discriminate.
Qed.

Lemma reduction_relaxed_state_ext : forall first second,
  RM.relaxed_mach first = RM.relaxed_mach second ->
  (forall idx, RM.relaxed_rf first idx = RM.relaxed_rf second idx) ->
  first = second.
Proof.
  intros [first_machine first_rf] [second_machine second_rf]. cbn.
  intros Hmachine Hrf. subst second_machine. f_equal.
  apply functional_extensionality. exact Hrf.
Qed.

(** Traverse one bounded proof chunk, then hand the remaining execution to an
    opaque checkpoint lemma. *)
Ltac reduction_candidate_chunk fuel next_state next_lemma :=
  lazymatch fuel with
  | O =>
      match goal with
      | Hsteps : reduction_candidate_state_steps ?state ?final |- _ =>
          first
            [ change (reduction_candidate_state_steps next_state final)
                in Hsteps
            | let Heq := fresh "Heq" in
              assert (Heq : state = next_state)
                by (apply reduction_relaxed_state_ext;
                    [ vm_compute
                    | intro idx; vm_compute ]);
              destruct Heq ];
          match goal with
          | Hdone : RM.all_done _,
            Hconsistent : H.consistent _ _ |- _ =>
              exact (next_lemma final Hsteps Hdone Hconsistent)
          end
      end
  | S ?fuel' =>
      match goal with
      | Hsteps : reduction_candidate_state_steps ?state ?final |- _ =>
          let Hnotdone := fresh "Hnotdone" in
          assert (Hnotdone : ~ RM.all_done (RM.relaxed_mach state))
            by (apply reduction_not_done_of_bool_false; vm_compute; reflexivity);
          inversion Hsteps; clear Hsteps; subst
      end;
      [ exfalso; contradiction
      | match goal with
        | Hstep : reduction_candidate_step _ _ = Some _,
          Hrest : reduction_candidate_state_steps _ _ |- _ =>
            reduction_candidate_one_step Hstep;
            first
              [ reduction_prune_candidate_stale Hrest
              | reduction_candidate_chunk fuel' next_state next_lemma ]
        end ]
  end.

Lemma reduction_state_117_no_candidate : forall source_idx,
  reduction_candidate_step source_idx reduction_state_117 = None.
Proof.
  intros source_idx. vm_compute. reflexivity.
Qed.

Lemma reduction_from_state_117 : forall final_state,
  reduction_candidate_state_steps reduction_state_117 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  inversion Hcandidate; clear Hcandidate; subst.
  - unfold reduction_outcome. vm_compute. split; reflexivity.
  - rewrite reduction_state_117_no_candidate in H. discriminate.
Qed.

Lemma reduction_from_state_110 : forall final_state,
  reduction_candidate_state_steps reduction_state_110 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 7%nat reduction_state_117
    reduction_from_state_117.
Qed.

Lemma reduction_from_state_100 : forall final_state,
  reduction_candidate_state_steps reduction_state_100 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_110
    reduction_from_state_110.
Qed.

Lemma reduction_from_state_95 : forall final_state,
  reduction_candidate_state_steps reduction_state_95 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 5%nat reduction_state_100
    reduction_from_state_100.
Qed.

Lemma reduction_from_state_90 : forall final_state,
  reduction_candidate_state_steps reduction_state_90 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 5%nat reduction_state_95 reduction_from_state_95.
Qed.

Lemma reduction_from_state_80 : forall final_state,
  reduction_candidate_state_steps reduction_state_80 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_90 reduction_from_state_90.
Qed.

Lemma reduction_from_state_70 : forall final_state,
  reduction_candidate_state_steps reduction_state_70 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_80 reduction_from_state_80.
Qed.

Lemma reduction_from_state_60 : forall final_state,
  reduction_candidate_state_steps reduction_state_60 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_70 reduction_from_state_70.
Qed.

Lemma reduction_from_state_50 : forall final_state,
  reduction_candidate_state_steps reduction_state_50 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_60 reduction_from_state_60.
Qed.

Lemma reduction_from_state_40 : forall final_state,
  reduction_candidate_state_steps reduction_state_40 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_50 reduction_from_state_50.
Qed.

Lemma reduction_from_state_30 : forall final_state,
  reduction_candidate_state_steps reduction_state_30 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_40 reduction_from_state_40.
Qed.

Lemma reduction_from_state_20 : forall final_state,
  reduction_candidate_state_steps reduction_state_20 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_30 reduction_from_state_30.
Qed.

Lemma reduction_from_state_10 : forall final_state,
  reduction_candidate_state_steps reduction_state_10 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_20 reduction_from_state_20.
Qed.

Lemma reduction_from_state_0 : forall final_state,
  reduction_candidate_state_steps reduction_state_0 final_state ->
  RM.all_done (RM.relaxed_mach final_state) ->
  H.consistent
    (T.translate_trace (MC.mach_trace (RM.relaxed_mach final_state)))
    (RM.relaxed_rf final_state) ->
  reduction_outcome final_state.
Proof.
  intros final_state Hcandidate Hdone Hconsistent.
  reduction_candidate_chunk 10%nat reduction_state_10 reduction_from_state_10.
Qed.

(** Every completed consistent execution under the fixed round scheduler has
    the same value-distinguishable trace. *)
Theorem reduction_deterministic : forall final rf,
  RM.relaxed_machine_steps reduction_initial_machine final rf ->
  RM.all_done final ->
  H.consistent (T.translate_trace (MC.mach_trace final)) rf ->
  MC.mach_trace final = reduction_final_trace.
Proof.
  intros final rf Hsteps Hdone Hconsistent.
  unfold RM.relaxed_machine_steps in Hsteps.
  change (RM.all_done (RM.relaxed_mach (RM.mk_relaxed_state final rf))) in Hdone.
  pose proof (reduction_candidate_steps_complete _ _ Hsteps) as Hcandidate.
  change (reduction_candidate_state_steps reduction_state_0
    (RM.mk_relaxed_state final rf)) in Hcandidate.
  destruct (reduction_from_state_0 _ Hcandidate Hdone Hconsistent)
    as [Htrace _].
  exact Htrace.
Qed.

(** The unique trace also fixes shared address zero to the fixed-tree result.
    This is a raw-bit result, not an IEEE-754 arithmetic theorem. *)
Corollary reduction_result_unique : forall final rf,
  RM.relaxed_machine_steps reduction_initial_machine final rf ->
  RM.all_done final ->
  H.consistent (T.translate_trace (MC.mach_trace final)) rf ->
  MS.mem_read (MC.mach_shared final) 0 = Some (M.VF32 reduction_result).
Proof.
  intros final rf Hsteps Hdone Hconsistent.
  unfold RM.relaxed_machine_steps in Hsteps.
  change (RM.all_done (RM.relaxed_mach (RM.mk_relaxed_state final rf))) in Hdone.
  pose proof (reduction_candidate_steps_complete _ _ Hsteps) as Hcandidate.
  change (reduction_candidate_state_steps reduction_state_0
    (RM.mk_relaxed_state final rf)) in Hcandidate.
  destruct (reduction_from_state_0 _ Hcandidate Hdone Hconsistent)
    as [_ Hresult].
  exact Hresult.
Qed.

End Reduction.
