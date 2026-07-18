From Coq Require Import ZArith List String Lia FunctionalExtensionality.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax MIRSemantics MIRConcurrent MIRRelaxed.
Require Import PTXRelations PTXHB Translate MP MPRealizable.

(** Finite candidate enumeration for the fixed, straight-line MP schedule.

    The generic relaxed load rule permits either earlier same-address store.
    For this six-event schedule that gives four unconditioned candidates:
    flag=0/data=0, flag=0/data=1, flag=1/data=0, and flag=1/data=1.
    The usual MP question conditions on the acquire load observing the release
    store ([rf 4 = Some 3]); under that condition exactly the good and weak
    traces remain. *)
Module MPCandidates.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConcurrent.
Module RM := MIRRelaxed.
Module R := PTXRelations.
Module H := PTXHB.
Module T := Translate.
Module MR := MPRealizable.

Definition rf_flag_release : R.rf_map :=
  RM.rf_set RM.empty_rf 4%nat 3%nat.
Definition rf_flag_init : R.rf_map :=
  RM.rf_set RM.empty_rf 4%nat 1%nat.

Definition rf_good : R.rf_map :=
  RM.rf_set rf_flag_release 5%nat 2%nat.
Definition rf_weak : R.rf_map :=
  RM.rf_set rf_flag_release 5%nat 0%nat.
Definition rf_flag0_data0 : R.rf_map :=
  RM.rf_set rf_flag_init 5%nat 0%nat.
Definition rf_flag0_data1 : R.rf_map :=
  RM.rf_set rf_flag_init 5%nat 2%nat.

Definition reader_r1_zero_env : MS.env :=
  MS.env_set MS.empty_env "r1" (M.VU32 0).
Definition reader_after_flag_zero : MC.thread :=
  MC.mk_thread 1%nat [MR.read_data] reader_r1_zero_env.

Definition trace_flag_load_zero : list (nat * M.event_mir) :=
  MR.trace_flag_one ++
  [(1%nat, M.EvAtomicLoadAcquire M.TyU32 MP.flag_addr (M.VU32 0))].

Definition after_flag_load_zero : MC.machine :=
  MC.mk_machine [MR.done0; MR.done0; reader_after_flag_zero]
    MR.mem_flag_one trace_flag_load_zero.

Definition reader_done_zero_zero_env : MS.env :=
  MS.env_set reader_r1_zero_env "r2" (M.VU32 0).
Definition reader_done_zero_one_env : MS.env :=
  MS.env_set reader_r1_zero_env "r2" (M.VU32 1).
Definition reader_done_one_zero_env : MS.env :=
  MS.env_set MR.reader_r1_env "r2" (M.VU32 0).

Definition trace_good : list (nat * M.event_mir) := MR.trace_data_load.
Definition trace_weak : list (nat * M.event_mir) :=
  MR.trace_flag_load ++
  [(1%nat, M.EvLoad M.TyU32 MP.data_addr (M.VU32 0))].
Definition trace_flag0_data0 : list (nat * M.event_mir) :=
  trace_flag_load_zero ++
  [(1%nat, M.EvLoad M.TyU32 MP.data_addr (M.VU32 0))].
Definition trace_flag0_data1 : list (nat * M.event_mir) :=
  trace_flag_load_zero ++
  [(1%nat, M.EvLoad M.TyU32 MP.data_addr (M.VU32 1))].

Definition final_good : MC.machine := MR.mp_final_machine.
Definition final_weak : MC.machine :=
  MC.mk_machine
    [MR.done0; MR.done0;
     MC.mk_thread 1%nat [] reader_done_one_zero_env]
    MR.mem_flag_one trace_weak.
Definition final_flag0_data0 : MC.machine :=
  MC.mk_machine
    [MR.done0; MR.done0;
     MC.mk_thread 1%nat [] reader_done_zero_zero_env]
    MR.mem_flag_one trace_flag0_data0.
Definition final_flag0_data1 : MC.machine :=
  MC.mk_machine
    [MR.done0; MR.done0;
     MC.mk_thread 1%nat [] reader_done_zero_one_env]
    MR.mem_flag_one trace_flag0_data1.

Definition state0 : RM.relaxed_state :=
  RM.mk_relaxed_state MR.mp_initial_machine RM.empty_rf.
Definition state1 : RM.relaxed_state :=
  RM.mk_relaxed_state MR.after_init_data RM.empty_rf.
Definition state2 : RM.relaxed_state :=
  RM.mk_relaxed_state MR.after_init_flag RM.empty_rf.
Definition state3 : RM.relaxed_state :=
  RM.mk_relaxed_state MR.after_data_one RM.empty_rf.
Definition state4 : RM.relaxed_state :=
  RM.mk_relaxed_state MR.after_flag_one RM.empty_rf.
Definition state5_release : RM.relaxed_state :=
  RM.mk_relaxed_state MR.after_flag_load rf_flag_release.
Definition state5_init : RM.relaxed_state :=
  RM.mk_relaxed_state after_flag_load_zero rf_flag_init.
Definition state6_good : RM.relaxed_state :=
  RM.mk_relaxed_state final_good rf_good.
Definition state6_weak : RM.relaxed_state :=
  RM.mk_relaxed_state final_weak rf_weak.
Definition state6_flag0_data0 : RM.relaxed_state :=
  RM.mk_relaxed_state final_flag0_data0 rf_flag0_data0.
Definition state6_flag0_data1 : RM.relaxed_state :=
  RM.mk_relaxed_state final_flag0_data1 rf_flag0_data1.

Lemma rstep_init_data : RM.relaxed_machine_step state0 state1.
Proof.
  unfold state0, state1, MR.mp_initial_machine, MR.after_init_data,
    MR.initializer, MR.initializer_after_data, MR.init_data, MR.init_flag,
    MR.mem_init_data, MR.trace_init_data.
  eapply RM.RelaxedNonLoad with
    (before := [])
    (current := MC.mk_thread 0%nat
      [M.SStore (MR.ptr MP.data_addr) (MR.u32 0) M.TyU32;
       M.SStore (MR.ptr MP.flag_addr) (MR.u32 0) M.TyU32] MS.empty_env)
    (after := [MR.writer; MR.reader])
    (oev := Some (M.EvStore M.TyU32 MP.data_addr (M.VU32 0)))
    (next := MS.mk_cfg
      [M.SStore (MR.ptr MP.flag_addr) (MR.u32 0) M.TyU32]
      MS.empty_env MR.mem_init_data).
  - reflexivity.
  - exact I.
  - apply MS.StepStore with (addr := MP.data_addr) (v := M.VU32 0);
      reflexivity.
Qed.

Lemma rstep_init_flag : RM.relaxed_machine_step state1 state2.
Proof.
  unfold state1, state2, MR.after_init_data, MR.after_init_flag,
    MR.initializer_after_data, MR.done0, MR.init_flag,
    MR.mem_init_flag, MR.trace_init_flag.
  eapply RM.RelaxedNonLoad with
    (before := [])
    (current := MC.mk_thread 0%nat
      [M.SStore (MR.ptr MP.flag_addr) (MR.u32 0) M.TyU32] MS.empty_env)
    (after := [MR.writer; MR.reader])
    (oev := Some (M.EvStore M.TyU32 MP.flag_addr (M.VU32 0)))
    (next := MS.mk_cfg [] MS.empty_env MR.mem_init_flag).
  - reflexivity.
  - exact I.
  - apply MS.StepStore with (addr := MP.flag_addr) (v := M.VU32 0);
      reflexivity.
Qed.

Lemma rstep_data_one : RM.relaxed_machine_step state2 state3.
Proof.
  unfold state2, state3, MR.after_init_flag, MR.after_data_one,
    MR.writer, MR.writer_after_data, MR.write_data, MR.release_flag,
    MR.mem_data_one, MR.trace_data_one.
  eapply RM.RelaxedNonLoad with
    (before := [MR.done0])
    (current := MC.mk_thread 0%nat
      [M.SStore (MR.ptr MP.data_addr) (MR.u32 1) M.TyU32;
       M.SAtomicStoreRelease (MR.ptr MP.flag_addr) (MR.u32 1) M.TyU32]
      MS.empty_env)
    (after := [MR.reader])
    (oev := Some (M.EvStore M.TyU32 MP.data_addr (M.VU32 1)))
    (next := MS.mk_cfg
      [M.SAtomicStoreRelease (MR.ptr MP.flag_addr) (MR.u32 1) M.TyU32]
      MS.empty_env MR.mem_data_one).
  - reflexivity.
  - exact I.
  - apply MS.StepStore with (addr := MP.data_addr) (v := M.VU32 1);
      reflexivity.
Qed.

Lemma rstep_flag_one : RM.relaxed_machine_step state3 state4.
Proof.
  unfold state3, state4, MR.after_data_one, MR.after_flag_one,
    MR.writer_after_data, MR.done0, MR.release_flag,
    MR.mem_flag_one, MR.trace_flag_one.
  eapply RM.RelaxedNonLoad with
    (before := [MR.done0])
    (current := MC.mk_thread 0%nat
      [M.SAtomicStoreRelease (MR.ptr MP.flag_addr) (MR.u32 1) M.TyU32]
      MS.empty_env)
    (after := [MR.reader])
    (oev := Some
      (M.EvAtomicStoreRelease M.TyU32 MP.flag_addr (M.VU32 1)))
    (next := MS.mk_cfg [] MS.empty_env MR.mem_flag_one).
  - reflexivity.
  - exact I.
  - apply MS.StepAtomicStoreRelease with
      (addr := MP.flag_addr) (v := M.VU32 1); reflexivity.
Qed.

Lemma rstep_flag_from_release :
  RM.relaxed_machine_step state4 state5_release.
Proof.
  unfold state4, state5_release, MR.after_flag_one, MR.after_flag_load,
    MR.reader, MR.reader_after_flag, MR.acquire_flag, MR.read_data,
    MR.reader_r1_env, MR.trace_flag_load, rf_flag_release.
  eapply RM.RelaxedAtomicLoadAcquire with
    (before := [MR.done0; MR.done0])
    (current := MC.mk_thread 1%nat
      [M.SAtomicLoadAcquire "r1" (MR.ptr MP.flag_addr) M.TyU32;
       M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32] MS.empty_env)
    (after := []) (rest := [M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32])
    (dst := "r1") (ptr := MR.ptr MP.flag_addr) (ty := M.TyU32)
    (addr := MP.flag_addr) (value := M.VU32 1) (source_idx := 3%nat).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply RM.SourceRelease with (tid := 0%nat). reflexivity.
Qed.

Lemma rstep_flag_from_init :
  RM.relaxed_machine_step state4 state5_init.
Proof.
  unfold state4, state5_init, MR.after_flag_one,
    after_flag_load_zero, reader_after_flag_zero, reader_r1_zero_env,
    MR.reader, MR.acquire_flag, MR.read_data,
    trace_flag_load_zero, rf_flag_init.
  eapply RM.RelaxedAtomicLoadAcquire with
    (before := [MR.done0; MR.done0])
    (current := MC.mk_thread 1%nat
      [M.SAtomicLoadAcquire "r1" (MR.ptr MP.flag_addr) M.TyU32;
       M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32] MS.empty_env)
    (after := []) (rest := [M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32])
    (dst := "r1") (ptr := MR.ptr MP.flag_addr) (ty := M.TyU32)
    (addr := MP.flag_addr) (value := M.VU32 0) (source_idx := 1%nat).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply RM.SourcePlain with (tid := 0%nat). reflexivity.
Qed.

Lemma rstep_release_data_one :
  RM.relaxed_machine_step state5_release state6_good.
Proof.
  unfold state5_release, state6_good, final_good, rf_good,
    MR.after_flag_load, MR.mp_final_machine, MR.reader_after_flag,
    MR.done1, MR.read_data, MR.reader_done_env, MR.trace_data_load.
  eapply RM.RelaxedLoad with
    (before := [MR.done0; MR.done0])
    (current := MC.mk_thread 1%nat
      [M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32] MR.reader_r1_env)
    (after := []) (rest := []) (dst := "r2")
    (ptr := MR.ptr MP.data_addr) (ty := M.TyU32)
    (addr := MP.data_addr) (value := M.VU32 1) (source_idx := 2%nat).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply RM.SourcePlain with (tid := 0%nat). reflexivity.
Qed.

Lemma rstep_release_data_zero :
  RM.relaxed_machine_step state5_release state6_weak.
Proof.
  unfold state5_release, state6_weak, final_weak, rf_weak,
    MR.after_flag_load, MR.reader_after_flag, MR.read_data,
    reader_done_one_zero_env, trace_weak.
  eapply RM.RelaxedLoad with
    (before := [MR.done0; MR.done0])
    (current := MC.mk_thread 1%nat
      [M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32] MR.reader_r1_env)
    (after := []) (rest := []) (dst := "r2")
    (ptr := MR.ptr MP.data_addr) (ty := M.TyU32)
    (addr := MP.data_addr) (value := M.VU32 0) (source_idx := 0%nat).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply RM.SourcePlain with (tid := 0%nat). reflexivity.
Qed.

Lemma rstep_init_data_zero :
  RM.relaxed_machine_step state5_init state6_flag0_data0.
Proof.
  unfold state5_init, state6_flag0_data0, after_flag_load_zero,
    final_flag0_data0, reader_after_flag_zero, MR.read_data,
    reader_done_zero_zero_env, trace_flag0_data0, rf_flag0_data0.
  eapply RM.RelaxedLoad with
    (before := [MR.done0; MR.done0])
    (current := MC.mk_thread 1%nat
      [M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32] reader_r1_zero_env)
    (after := []) (rest := []) (dst := "r2")
    (ptr := MR.ptr MP.data_addr) (ty := M.TyU32)
    (addr := MP.data_addr) (value := M.VU32 0) (source_idx := 0%nat).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply RM.SourcePlain with (tid := 0%nat). reflexivity.
Qed.

Lemma rstep_init_data_one :
  RM.relaxed_machine_step state5_init state6_flag0_data1.
Proof.
  unfold state5_init, state6_flag0_data1, after_flag_load_zero,
    final_flag0_data1, reader_after_flag_zero, MR.read_data,
    reader_done_zero_one_env, trace_flag0_data1, rf_flag0_data1.
  eapply RM.RelaxedLoad with
    (before := [MR.done0; MR.done0])
    (current := MC.mk_thread 1%nat
      [M.SLoad "r2" (MR.ptr MP.data_addr) M.TyU32] reader_r1_zero_env)
    (after := []) (rest := []) (dst := "r2")
    (ptr := MR.ptr MP.data_addr) (ty := M.TyU32)
    (addr := MP.data_addr) (value := M.VU32 1) (source_idx := 2%nat).
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply RM.SourcePlain with (tid := 0%nat). reflexivity.
Qed.

Definition relaxed_path_to
    (final : RM.relaxed_state) (last_step : RM.relaxed_machine_step state5_release final)
    : RM.relaxed_state_steps state0 final.
Proof.
  eapply RM.RelaxedMore; [apply rstep_init_data|].
  eapply RM.RelaxedMore; [apply rstep_init_flag|].
  eapply RM.RelaxedMore; [apply rstep_data_one|].
  eapply RM.RelaxedMore; [apply rstep_flag_one|].
  eapply RM.RelaxedMore; [apply rstep_flag_from_release|].
  eapply RM.RelaxedMore; [exact last_step|].
  apply RM.RelaxedDone.
Defined.

Definition relaxed_init_path_to
    (final : RM.relaxed_state)
    (last_step : RM.relaxed_machine_step state5_init final)
    : RM.relaxed_state_steps state0 final.
Proof.
  eapply RM.RelaxedMore; [apply rstep_init_data|].
  eapply RM.RelaxedMore; [apply rstep_init_flag|].
  eapply RM.RelaxedMore; [apply rstep_data_one|].
  eapply RM.RelaxedMore; [apply rstep_flag_one|].
  eapply RM.RelaxedMore; [apply rstep_flag_from_init|].
  eapply RM.RelaxedMore; [exact last_step|].
  apply RM.RelaxedDone.
Defined.

Theorem mp_good_relaxed_realizable :
  RM.relaxed_machine_steps MR.mp_initial_machine final_good rf_good /\
  RM.all_done final_good /\
  T.translate_trace (MC.mach_trace final_good) = MP.mp_trace_acqrel_good.
Proof.
  split.
  - exact (relaxed_path_to state6_good rstep_release_data_one).
  - split.
    + unfold RM.all_done, RM.threads_done, RM.thread_done,
        final_good, MR.mp_final_machine, MR.done0, MR.done1.
      repeat constructor.
    + reflexivity.
Qed.

Theorem mp_weak_relaxed_realizable :
  RM.relaxed_machine_steps MR.mp_initial_machine final_weak rf_weak /\
  RM.all_done final_weak /\
  T.translate_trace (MC.mach_trace final_weak) = MP.mp_trace_acqrel_weak.
Proof.
  split.
  - exact (relaxed_path_to state6_weak rstep_release_data_zero).
  - split.
    + unfold RM.all_done, RM.threads_done, RM.thread_done,
        final_weak, MR.done0.
      repeat constructor.
    + reflexivity.
Qed.

(** Exhaustiveness of the finite source choices. *)
Lemma flag_sources_exact : forall source_idx value,
  RM.source_store MR.trace_flag_one source_idx M.TyU32 MP.flag_addr value ->
  (source_idx = 1%nat /\ value = M.VU32 0) \/
  (source_idx = 3%nat /\ value = M.VU32 1).
Proof.
  intros source_idx value Hsource.
  inversion Hsource as [tid Hnth | tid Hnth]; subst.
  - assert (Hbound : (source_idx < List.length MR.trace_flag_one)%nat).
    { apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
    unfold MR.trace_flag_one, MR.trace_data_one, MR.trace_init_flag,
      MR.trace_init_data in Hnth, Hbound.
    destruct source_idx as [|[|[|[|source_idx]]]]; simpl in Hnth, Hbound;
      try discriminate; try lia.
    inversion Hnth; subst. left. auto.
  - assert (Hbound : (source_idx < List.length MR.trace_flag_one)%nat).
    { apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
    unfold MR.trace_flag_one, MR.trace_data_one, MR.trace_init_flag,
      MR.trace_init_data in Hnth, Hbound.
    destruct source_idx as [|[|[|[|source_idx]]]]; simpl in Hnth, Hbound;
      try discriminate; try lia.
    inversion Hnth; subst. right. auto.
Qed.

Lemma data_sources_release_exact : forall source_idx value,
  RM.source_store MR.trace_flag_load source_idx M.TyU32 MP.data_addr value ->
  (source_idx = 0%nat /\ value = M.VU32 0) \/
  (source_idx = 2%nat /\ value = M.VU32 1).
Proof.
  intros source_idx value Hsource.
  inversion Hsource as [tid Hnth | tid Hnth]; subst.
  - assert (Hbound : (source_idx < List.length MR.trace_flag_load)%nat).
    { apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
    unfold MR.trace_flag_load, MR.trace_flag_one, MR.trace_data_one,
      MR.trace_init_flag, MR.trace_init_data in Hnth, Hbound.
    destruct source_idx as [|[|[|[|[|source_idx]]]]];
      simpl in Hnth, Hbound; try discriminate; try lia.
    + inversion Hnth; subst. left. auto.
    + inversion Hnth; subst. right. auto.
  - assert (Hbound : (source_idx < List.length MR.trace_flag_load)%nat).
    { apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
    unfold MR.trace_flag_load, MR.trace_flag_one, MR.trace_data_one,
      MR.trace_init_flag, MR.trace_init_data in Hnth, Hbound.
    destruct source_idx as [|[|[|[|[|source_idx]]]]];
      simpl in Hnth, Hbound; try discriminate; lia.
Qed.

Lemma data_sources_init_exact : forall source_idx value,
  RM.source_store trace_flag_load_zero source_idx M.TyU32 MP.data_addr value ->
  (source_idx = 0%nat /\ value = M.VU32 0) \/
  (source_idx = 2%nat /\ value = M.VU32 1).
Proof.
  intros source_idx value Hsource.
  inversion Hsource as [tid Hnth | tid Hnth]; subst.
  - assert (Hbound : (source_idx < List.length trace_flag_load_zero)%nat).
    { apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
    unfold trace_flag_load_zero, MR.trace_flag_one, MR.trace_data_one,
      MR.trace_init_flag, MR.trace_init_data in Hnth, Hbound.
    destruct source_idx as [|[|[|[|[|source_idx]]]]];
      simpl in Hnth, Hbound; try discriminate; try lia.
    + inversion Hnth; subst. left. auto.
    + inversion Hnth; subst. right. auto.
  - assert (Hbound : (source_idx < List.length trace_flag_load_zero)%nat).
    { apply (proj1 (nth_error_Some _ _)). rewrite Hnth. discriminate. }
    unfold trace_flag_load_zero, MR.trace_flag_one, MR.trace_data_one,
      MR.trace_init_flag, MR.trace_init_data in Hnth, Hbound.
    destruct source_idx as [|[|[|[|[|source_idx]]]]];
      simpl in Hnth, Hbound; try discriminate; lia.
Qed.

Lemma flag_release_is_latest :
  RM.latest_source_store MR.trace_flag_one 3%nat M.TyU32 MP.flag_addr
    (M.VU32 1).
Proof.
  split.
  - apply RM.SourceRelease with (tid := 0%nat). reflexivity.
  - intros later_idx later_value Hlater Hsource.
    destruct (flag_sources_exact later_idx later_value Hsource)
      as [[Hidx _] | [Hidx _]]; lia.
Qed.

Lemma data_one_is_latest :
  RM.latest_source_store MR.trace_flag_load 2%nat M.TyU32 MP.data_addr
    (M.VU32 1).
Proof.
  split.
  - apply RM.SourcePlain with (tid := 0%nat). reflexivity.
  - intros later_idx later_value Hlater Hsource.
    destruct (data_sources_release_exact later_idx later_value Hsource)
      as [[Hidx _] | [Hidx _]]; lia.
Qed.

Lemma mp_sc_machine_steps_exact :
  MC.machine_steps MR.mp_initial_machine final_good.
Proof.
  unfold final_good.
  eapply MC.MachineMore; [apply MR.step_init_data|].
  eapply MC.MachineMore; [apply MR.step_init_flag|].
  eapply MC.MachineMore; [apply MR.step_data_one|].
  eapply MC.MachineMore; [apply MR.step_flag_one|].
  eapply MC.MachineMore; [apply MR.step_flag_load|].
  eapply MC.MachineMore; [apply MR.step_data_load|].
  apply MC.MachineDone.
Qed.

(** The ordinary current-memory execution is also the relaxed execution whose
    two loads choose the latest matching stores (indices 3 and 2). *)
Theorem mp_sc_is_relaxed_latest_special_case :
  MC.machine_steps MR.mp_initial_machine final_good /\
  RM.relaxed_machine_steps MR.mp_initial_machine final_good rf_good /\
  RM.latest_source_store MR.trace_flag_one 3%nat M.TyU32 MP.flag_addr
    (M.VU32 1) /\
  RM.latest_source_store MR.trace_flag_load 2%nat M.TyU32 MP.data_addr
    (M.VU32 1).
Proof.
  split.
  - apply mp_sc_machine_steps_exact.
  - split.
    + exact (proj1 mp_good_relaxed_realizable).
    + split.
      * apply flag_release_is_latest.
      * apply data_one_is_latest.
Qed.

Ltac solve_fixed_nonload Hstep :=
  inversion Hstep; subst; cbn in *;
    repeat match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    end;
  [ match goal with
    | H : MS.step _ _ _ |- _ => inversion H; subst; cbn in *
    end;
      try discriminate;
      repeat match goal with
      | H : Some _ = Some _ |- _ => inversion H; clear H; subst
      end;
      reflexivity
  | discriminate
  | discriminate ].

Lemma step_from_state0 : forall next,
  RM.relaxed_machine_step state0 next -> next = state1.
Proof.
  intros next Hstep.
  unfold state0, state1, MR.mp_initial_machine, MR.after_init_data,
    MR.initializer, MR.initializer_after_data, MR.init_data, MR.init_flag,
    MR.mem_init_data, MR.trace_init_data in *.
  solve_fixed_nonload Hstep.
Qed.

Lemma step_from_state1 : forall next,
  RM.relaxed_machine_step state1 next -> next = state2.
Proof.
  intros next Hstep.
  unfold state1, state2, MR.after_init_data, MR.after_init_flag,
    MR.initializer_after_data, MR.done0, MR.init_flag,
    MR.mem_init_flag, MR.trace_init_flag in *.
  solve_fixed_nonload Hstep.
Qed.

Lemma step_from_state2 : forall next,
  RM.relaxed_machine_step state2 next -> next = state3.
Proof.
  intros next Hstep.
  unfold state2, state3, MR.after_init_flag, MR.after_data_one,
    MR.done0, MR.writer, MR.writer_after_data, MR.write_data,
    MR.release_flag, MR.mem_data_one, MR.trace_data_one in *.
  solve_fixed_nonload Hstep.
Qed.

Lemma step_from_state3 : forall next,
  RM.relaxed_machine_step state3 next -> next = state4.
Proof.
  intros next Hstep.
  unfold state3, state4, MR.after_data_one, MR.after_flag_one,
    MR.done0, MR.writer_after_data, MR.release_flag,
    MR.mem_flag_one, MR.trace_flag_one in *.
  solve_fixed_nonload Hstep.
Qed.

Lemma step_from_state4 : forall next,
  RM.relaxed_machine_step state4 next ->
  next = state5_release \/ next = state5_init.
Proof.
  intros next Hstep.
  unfold state4, MR.after_flag_one, MR.done0, MR.reader,
    MR.acquire_flag, MR.read_data in Hstep.
  inversion Hstep; subst; cbn in *;
    repeat match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    end.
  - contradiction.
  - cbn in H5. discriminate.
  - cbn in H5. inversion H5; subst. cbn in H6. inversion H6; subst.
    destruct (flag_sources_exact source_idx value H7)
      as [[Hidx Hvalue] | [Hidx Hvalue]]; subst.
    + right. reflexivity.
    + left. reflexivity.
Qed.

Lemma step_from_state5_release : forall next,
  RM.relaxed_machine_step state5_release next ->
  next = state6_good \/ next = state6_weak.
Proof.
  intros next Hstep.
  unfold state5_release, MR.after_flag_load, MR.done0,
    MR.reader_after_flag, MR.read_data in Hstep.
  inversion Hstep; subst; cbn in *;
    repeat match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    end.
  - contradiction.
  - cbn in H5. inversion H5; subst. cbn in H6. inversion H6; subst.
    destruct (data_sources_release_exact source_idx value H7)
      as [[Hidx Hvalue] | [Hidx Hvalue]]; subst.
    + right. reflexivity.
    + left. reflexivity.
  - cbn in H5. discriminate.
Qed.

Lemma step_from_state5_init : forall next,
  RM.relaxed_machine_step state5_init next ->
  next = state6_flag0_data0 \/ next = state6_flag0_data1.
Proof.
  intros next Hstep.
  unfold state5_init, after_flag_load_zero, MR.done0,
    reader_after_flag_zero, MR.read_data in Hstep.
  inversion Hstep; subst; cbn in *;
    repeat match goal with
    | H : Some _ = Some _ |- _ => inversion H; clear H; subst
    end.
  - contradiction.
  - cbn in H5. inversion H5; subst. cbn in H6. inversion H6; subst.
    destruct (data_sources_init_exact source_idx value H7)
      as [[Hidx Hvalue] | [Hidx Hvalue]]; subst.
    + left. reflexivity.
    + right. reflexivity.
  - cbn in H5. discriminate.
Qed.

Lemma final_good_done : RM.all_done final_good.
Proof.
  unfold RM.all_done, RM.threads_done, RM.thread_done,
    final_good, MR.mp_final_machine, MR.done0, MR.done1.
  repeat constructor.
Qed.

Lemma final_weak_done : RM.all_done final_weak.
Proof.
  unfold RM.all_done, RM.threads_done, RM.thread_done,
    final_weak, MR.done0. repeat constructor.
Qed.

Lemma final_flag0_data0_done : RM.all_done final_flag0_data0.
Proof.
  unfold RM.all_done, RM.threads_done, RM.thread_done,
    final_flag0_data0, MR.done0. repeat constructor.
Qed.

Lemma final_flag0_data1_done : RM.all_done final_flag0_data1.
Proof.
  unfold RM.all_done, RM.threads_done, RM.thread_done,
    final_flag0_data1, MR.done0. repeat constructor.
Qed.

Inductive mp_phase : RM.relaxed_state -> Prop :=
| Phase0 : mp_phase state0
| Phase1 : mp_phase state1
| Phase2 : mp_phase state2
| Phase3 : mp_phase state3
| Phase4 : mp_phase state4
| Phase5Release : mp_phase state5_release
| Phase5Init : mp_phase state5_init
| Phase6Good : mp_phase state6_good
| Phase6Weak : mp_phase state6_weak
| Phase6Flag0Data0 : mp_phase state6_flag0_data0
| Phase6Flag0Data1 : mp_phase state6_flag0_data1.

Lemma mp_phase_step : forall current next,
  mp_phase current ->
  RM.relaxed_machine_step current next ->
  mp_phase next.
Proof.
  intros current next Hphase Hstep. inversion Hphase; subst.
  - rewrite (step_from_state0 next Hstep). constructor.
  - rewrite (step_from_state1 next Hstep). constructor.
  - rewrite (step_from_state2 next Hstep). constructor.
  - rewrite (step_from_state3 next Hstep). constructor.
  - destruct (step_from_state4 next Hstep); subst; constructor.
  - destruct (step_from_state5_release next Hstep); subst; constructor.
  - destruct (step_from_state5_init next Hstep); subst; constructor.
  - exfalso. eapply RM.all_done_no_step; [apply final_good_done|exact Hstep].
  - exfalso. eapply RM.all_done_no_step; [apply final_weak_done|exact Hstep].
  - exfalso. eapply RM.all_done_no_step;
      [apply final_flag0_data0_done|exact Hstep].
  - exfalso. eapply RM.all_done_no_step;
      [apply final_flag0_data1_done|exact Hstep].
Qed.

Lemma mp_phase_steps : forall current final,
  RM.relaxed_state_steps current final ->
  mp_phase current ->
  mp_phase final.
Proof.
  intros current final Hsteps Hphase.
  induction Hsteps as [state | state state' final Hstep Hsteps IH].
  - exact Hphase.
  - apply IH. eapply mp_phase_step; eauto.
Qed.

(** The complete, unconditioned result has four candidates.  Keeping the
    final machine and reads-from map paired is useful to eliminate the two
    flag=0 cases under the handoff condition below. *)
Theorem mp_candidates_classified : forall final rf,
  RM.relaxed_machine_steps MR.mp_initial_machine final rf ->
  RM.all_done final ->
  (final = final_good /\ rf = rf_good) \/
  (final = final_weak /\ rf = rf_weak) \/
  (final = final_flag0_data0 /\ rf = rf_flag0_data0) \/
  (final = final_flag0_data1 /\ rf = rf_flag0_data1).
Proof.
  intros final rf Hsteps Hdone.
  assert (Hphase : mp_phase (RM.mk_relaxed_state final rf)).
  { eapply mp_phase_steps.
    - exact Hsteps.
    - apply Phase0. }
  inversion Hphase; subst.
  - exfalso. eapply RM.all_done_no_step; [exact Hdone|apply rstep_init_data].
  - exfalso. eapply RM.all_done_no_step; [exact Hdone|apply rstep_init_flag].
  - exfalso. eapply RM.all_done_no_step; [exact Hdone|apply rstep_data_one].
  - exfalso. eapply RM.all_done_no_step; [exact Hdone|apply rstep_flag_one].
  - exfalso. eapply RM.all_done_no_step;
      [exact Hdone|apply rstep_flag_from_release].
  - exfalso. eapply RM.all_done_no_step;
      [exact Hdone|apply rstep_release_data_one].
  - exfalso. eapply RM.all_done_no_step;
      [exact Hdone|apply rstep_init_data_zero].
  - left. auto.
  - right. left. auto.
  - right. right. left. auto.
  - right. right. right. auto.
Qed.

Theorem mp_candidates_all : forall final rf,
  RM.relaxed_machine_steps MR.mp_initial_machine final rf ->
  RM.all_done final ->
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_good \/
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_weak \/
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_flag0_data0 \/
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_flag0_data1.
Proof.
  intros final rf Hsteps Hdone.
  destruct (mp_candidates_classified final rf Hsteps Hdone)
    as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
  - right. right. right. reflexivity.
Qed.

(** The two-candidate statement without a release-read premise is not true for
    an honest relaxed machine: this completed execution reads flag
    initialization and is distinct from both flag=1 traces. *)
Theorem mp_unconditioned_two_candidate_statement_false :
  ~ (forall final rf,
      RM.relaxed_machine_steps MR.mp_initial_machine final rf ->
      RM.all_done final ->
      T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_good \/
      T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_weak).
Proof.
  intro Hall.
  specialize (Hall final_flag0_data0 rf_flag0_data0).
  assert (Hsteps :
      RM.relaxed_machine_steps MR.mp_initial_machine
        final_flag0_data0 rf_flag0_data0).
  { exact (relaxed_init_path_to state6_flag0_data0 rstep_init_data_zero). }
  specialize (Hall Hsteps final_flag0_data0_done).
  destruct Hall as [Heq | Heq]; discriminate.
Qed.

(** Once the acquire is required to read the release store, exactly the usual
    good and weak MP candidates remain. *)
Theorem mp_candidates_exact : forall final rf,
  RM.relaxed_machine_steps MR.mp_initial_machine final rf ->
  RM.all_done final ->
  rf 4%nat = Some 3%nat ->
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_good \/
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_weak.
Proof.
  intros final rf Hsteps Hdone Hhandoff.
  destruct (mp_candidates_classified final rf Hsteps Hdone)
    as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
  - left. reflexivity.
  - right. reflexivity.
  - cbv [rf_flag0_data0 rf_flag_init RM.rf_set RM.empty_rf] in Hhandoff.
    discriminate.
  - cbv [rf_flag0_data1 rf_flag_init RM.rf_set RM.empty_rf] in Hhandoff.
    discriminate.
Qed.

(** Consistency is now a payoff theorem over machine-derived candidates:
    after a real release/acquire handoff, the weak candidate is rejected and
    the good execution is the only completed result. *)
Theorem mp_consistent_execution_good : forall final rf,
  RM.relaxed_machine_steps MR.mp_initial_machine final rf ->
  RM.all_done final ->
  rf 4%nat = Some 3%nat ->
  H.consistent (T.translate_trace (MC.mach_trace final)) rf ->
  T.translate_trace (MC.mach_trace final) = MP.mp_trace_acqrel_good.
Proof.
  intros final rf Hsteps Hdone Hhandoff Hconsistent.
  destruct (mp_candidates_classified final rf Hsteps Hdone)
    as [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]].
  - reflexivity.
  - exfalso. apply (MP.mp_acqrel_forbids_weak rf_weak Hconsistent).
    unfold MP.weak_outcome, rf_weak, rf_flag_release,
      RM.rf_set, RM.empty_rf. repeat split; reflexivity.
  - cbv [rf_flag0_data0 rf_flag_init RM.rf_set RM.empty_rf] in Hhandoff.
    discriminate.
  - cbv [rf_flag0_data1 rf_flag_init RM.rf_set RM.empty_rf] in Hhandoff.
    discriminate.
Qed.

End MPCandidates.
