From Coq Require Import ZArith List String.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax MIRSemantics MIRConcurrent Translate MP.

(** A concrete MIR-machine execution of the good acquire/release
    message-passing trace.

    The initializer is an explicit thread, not a pre-populated memory: its two
    stores therefore occupy trace indices 0 and 1.  It intentionally uses tid
    0, as does the writer; the reader uses tid 1.  The selected schedule is
    initializer, writer, reader, yielding indices 4 and 5 for the two loads.

    This MIR machine is sequentially consistent by construction: every load
    reads the current shared memory.  It therefore emits the good execution,
    not [MP.mp_trace_acqrel_weak].  The weak trace is a model-level candidate
    rejected by the consistency predicate, not a machine execution.

    Likewise, [MP.mp_trace_relaxed] is not claimed to be a MIR execution.  The
    MIR syntax has acquire-load and release-store atomic statements but no
    relaxed atomic statements.  The companion [MIRRelaxed]/[MPCandidates]
    development derives the finite acquire/release MP candidate space using
    nondeterministic reads-from choices; this file remains the ordinary
    current-memory execution. *)
Module MPRealizable.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConcurrent.
Module T := Translate.

Definition ptr (address : Z) : M.expr := M.EVal (M.VU64 address).
Definition u32 (value : Z) : M.expr := M.EVal (M.VU32 value).

Definition init_data : M.stmt :=
  M.SStore (ptr MP.data_addr) (u32 0) M.TyU32.
Definition init_flag : M.stmt :=
  M.SStore (ptr MP.flag_addr) (u32 0) M.TyU32.
Definition write_data : M.stmt :=
  M.SStore (ptr MP.data_addr) (u32 1) M.TyU32.
Definition release_flag : M.stmt :=
  M.SAtomicStoreRelease (ptr MP.flag_addr) (u32 1) M.TyU32.
Definition acquire_flag : M.stmt :=
  M.SAtomicLoadAcquire "r1" (ptr MP.flag_addr) M.TyU32.
Definition read_data : M.stmt :=
  M.SLoad "r2" (ptr MP.data_addr) M.TyU32.

Definition initializer : MC.thread :=
  MC.mk_thread 0%nat [init_data; init_flag] MS.empty_env.
Definition initializer_after_data : MC.thread :=
  MC.mk_thread 0%nat [init_flag] MS.empty_env.

Definition writer : MC.thread :=
  MC.mk_thread 0%nat [write_data; release_flag] MS.empty_env.
Definition writer_after_data : MC.thread :=
  MC.mk_thread 0%nat [release_flag] MS.empty_env.

Definition reader : MC.thread :=
  MC.mk_thread 1%nat [acquire_flag; read_data] MS.empty_env.
Definition reader_r1_env : MS.env :=
  MS.env_set MS.empty_env "r1" (M.VU32 1).
Definition reader_after_flag : MC.thread :=
  MC.mk_thread 1%nat [read_data] reader_r1_env.
Definition reader_done_env : MS.env :=
  MS.env_set reader_r1_env "r2" (M.VU32 1).

Definition done0 : MC.thread := MC.mk_thread 0%nat [] MS.empty_env.
Definition done1 : MC.thread := MC.mk_thread 1%nat [] reader_done_env.

Definition mem_init_data : MS.mem :=
  MS.mem_write MS.empty_mem MP.data_addr (M.VU32 0).
Definition mem_init_flag : MS.mem :=
  MS.mem_write mem_init_data MP.flag_addr (M.VU32 0).
Definition mem_data_one : MS.mem :=
  MS.mem_write mem_init_flag MP.data_addr (M.VU32 1).
Definition mem_flag_one : MS.mem :=
  MS.mem_write mem_data_one MP.flag_addr (M.VU32 1).

Definition trace_init_data : list (nat * M.event_mir) :=
  [(0%nat, M.EvStore M.TyU32 MP.data_addr (M.VU32 0))].
Definition trace_init_flag : list (nat * M.event_mir) :=
  trace_init_data ++
  [(0%nat, M.EvStore M.TyU32 MP.flag_addr (M.VU32 0))].
Definition trace_data_one : list (nat * M.event_mir) :=
  trace_init_flag ++
  [(0%nat, M.EvStore M.TyU32 MP.data_addr (M.VU32 1))].
Definition trace_flag_one : list (nat * M.event_mir) :=
  trace_data_one ++
  [(0%nat, M.EvAtomicStoreRelease M.TyU32 MP.flag_addr (M.VU32 1))].
Definition trace_flag_load : list (nat * M.event_mir) :=
  trace_flag_one ++
  [(1%nat, M.EvAtomicLoadAcquire M.TyU32 MP.flag_addr (M.VU32 1))].
Definition trace_data_load : list (nat * M.event_mir) :=
  trace_flag_load ++
  [(1%nat, M.EvLoad M.TyU32 MP.data_addr (M.VU32 1))].

Definition mp_initial_machine : MC.machine :=
  MC.mk_machine [initializer; writer; reader]
    MS.empty_mem MS.empty_mem [].

Definition after_init_data : MC.machine :=
  MC.mk_machine [initializer_after_data; writer; reader]
    mem_init_data MS.empty_mem trace_init_data.
Definition after_init_flag : MC.machine :=
  MC.mk_machine [done0; writer; reader]
    mem_init_flag MS.empty_mem trace_init_flag.
Definition after_data_one : MC.machine :=
  MC.mk_machine [done0; writer_after_data; reader]
    mem_data_one MS.empty_mem trace_data_one.
Definition after_flag_one : MC.machine :=
  MC.mk_machine [done0; done0; reader]
    mem_flag_one MS.empty_mem trace_flag_one.
Definition after_flag_load : MC.machine :=
  MC.mk_machine [done0; done0; reader_after_flag]
    mem_flag_one MS.empty_mem trace_flag_load.
Definition mp_final_machine : MC.machine :=
  MC.mk_machine [done0; done0; done1]
    mem_flag_one MS.empty_mem trace_data_load.

Definition mach_threads_all_done (machine : MC.machine) : Prop :=
  Forall (fun thread => MC.th_code thread = []) (MC.mach_threads machine).

Lemma step_init_data :
  MC.machine_step mp_initial_machine after_init_data.
Proof.
  unfold mp_initial_machine, after_init_data,
    initializer, initializer_after_data, init_data, init_flag,
    mem_init_data, trace_init_data.
  eapply MC.MachineStep with
    (before := [])
    (current := MC.mk_thread 0%nat
      [M.SStore (ptr MP.data_addr) (u32 0) M.TyU32;
       M.SStore (ptr MP.flag_addr) (u32 0) M.TyU32] MS.empty_env)
    (after := [writer; reader])
    (oev := Some (M.EvStore M.TyU32 MP.data_addr (M.VU32 0)))
    (next := MS.mk_cfg
      [M.SStore (ptr MP.flag_addr) (u32 0) M.TyU32]
      MS.empty_env mem_init_data).
  apply MS.StepStore with (addr := MP.data_addr) (v := M.VU32 0);
    reflexivity.
Qed.

Lemma step_init_flag :
  MC.machine_step after_init_data after_init_flag.
Proof.
  unfold after_init_data, after_init_flag,
    initializer_after_data, done0, init_flag,
    mem_init_flag, trace_init_flag.
  eapply MC.MachineStep with
    (before := [])
    (current := MC.mk_thread 0%nat
      [M.SStore (ptr MP.flag_addr) (u32 0) M.TyU32] MS.empty_env)
    (after := [writer; reader])
    (oev := Some (M.EvStore M.TyU32 MP.flag_addr (M.VU32 0)))
    (next := MS.mk_cfg [] MS.empty_env mem_init_flag).
  apply MS.StepStore with (addr := MP.flag_addr) (v := M.VU32 0);
    reflexivity.
Qed.

Lemma step_data_one :
  MC.machine_step after_init_flag after_data_one.
Proof.
  unfold after_init_flag, after_data_one,
    writer, writer_after_data, write_data, release_flag,
    mem_data_one, trace_data_one.
  eapply MC.MachineStep with
    (before := [done0])
    (current := MC.mk_thread 0%nat
      [M.SStore (ptr MP.data_addr) (u32 1) M.TyU32;
       M.SAtomicStoreRelease (ptr MP.flag_addr) (u32 1) M.TyU32]
      MS.empty_env)
    (after := [reader])
    (oev := Some (M.EvStore M.TyU32 MP.data_addr (M.VU32 1)))
    (next := MS.mk_cfg
      [M.SAtomicStoreRelease (ptr MP.flag_addr) (u32 1) M.TyU32]
      MS.empty_env mem_data_one).
  apply MS.StepStore with (addr := MP.data_addr) (v := M.VU32 1);
    reflexivity.
Qed.

Lemma step_flag_one :
  MC.machine_step after_data_one after_flag_one.
Proof.
  unfold after_data_one, after_flag_one,
    writer_after_data, done0, release_flag,
    mem_flag_one, trace_flag_one.
  eapply MC.MachineStep with
    (before := [done0])
    (current := MC.mk_thread 0%nat
      [M.SAtomicStoreRelease (ptr MP.flag_addr) (u32 1) M.TyU32]
      MS.empty_env)
    (after := [reader])
    (oev := Some
      (M.EvAtomicStoreRelease M.TyU32 MP.flag_addr (M.VU32 1)))
    (next := MS.mk_cfg [] MS.empty_env mem_flag_one).
  apply MS.StepAtomicStoreRelease with
    (addr := MP.flag_addr) (v := M.VU32 1); reflexivity.
Qed.

Lemma step_flag_load :
  MC.machine_step after_flag_one after_flag_load.
Proof.
  unfold after_flag_one, after_flag_load,
    reader, reader_after_flag, acquire_flag, read_data,
    reader_r1_env, trace_flag_load.
  eapply MC.MachineStep with
    (before := [done0; done0])
    (current := MC.mk_thread 1%nat
      [M.SAtomicLoadAcquire "r1" (ptr MP.flag_addr) M.TyU32;
       M.SLoad "r2" (ptr MP.data_addr) M.TyU32] MS.empty_env)
    (after := [])
    (oev := Some
      (M.EvAtomicLoadAcquire M.TyU32 MP.flag_addr (M.VU32 1)))
    (next := MS.mk_cfg
      [M.SLoad "r2" (ptr MP.data_addr) M.TyU32]
      reader_r1_env mem_flag_one).
  apply MS.StepAtomicLoadAcquire with
    (addr := MP.flag_addr) (v := M.VU32 1); reflexivity.
Qed.

Lemma step_data_load :
  MC.machine_step after_flag_load mp_final_machine.
Proof.
  unfold after_flag_load, mp_final_machine,
    reader_after_flag, done1, read_data,
    reader_done_env, trace_data_load.
  eapply MC.MachineStep with
    (before := [done0; done0])
    (current := MC.mk_thread 1%nat
      [M.SLoad "r2" (ptr MP.data_addr) M.TyU32] reader_r1_env)
    (after := [])
    (oev := Some (M.EvLoad M.TyU32 MP.data_addr (M.VU32 1)))
    (next := MS.mk_cfg [] reader_done_env mem_flag_one).
  apply MS.StepLoad with
    (addr := MP.data_addr) (v := M.VU32 1); reflexivity.
Qed.

Lemma mp_acqrel_realizable : exists m,
  MC.machine_steps mp_initial_machine m /\
  mach_threads_all_done m /\
  T.translate_trace (MC.mach_trace m) = MP.mp_trace_acqrel_good.
Proof.
  exists mp_final_machine. split.
  - eapply MC.MachineMore; [apply step_init_data|].
    eapply MC.MachineMore; [apply step_init_flag|].
    eapply MC.MachineMore; [apply step_data_one|].
    eapply MC.MachineMore; [apply step_flag_one|].
    eapply MC.MachineMore; [apply step_flag_load|].
    eapply MC.MachineMore; [apply step_data_load|].
    apply MC.MachineDone.
  - split.
    + unfold mach_threads_all_done, mp_final_machine, done0, done1.
      repeat constructor.
    + reflexivity.
Qed.

End MPRealizable.
