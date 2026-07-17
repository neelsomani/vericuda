From Coq Require Import ZArith List String Bool Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax MIRSemantics MIRRun MIRConcurrent.
Require Import PTXEvents PTXRelations Translate.
Require Import saxpy_gen atomic_flag_gen.

Module M := MIR.
Module MS := MIRSemantics.
Module MR := MIRRun.
Module MC := MIRConcurrent.
Module P := PTX.
Module RF := PTXRelations.
Module TR := Translate.
Module SG := Saxpy_gen.
Module AF := Atomic_flag_gen.

Fixpoint lookup_mem (k : M.addr) (ps : list (M.addr * M.val)) : option M.val :=
  match ps with
  | [] => None
  | (a, v) :: ps' => if Z.eqb k a then Some v else lookup_mem k ps'
  end.

Definition mem_of_pairs (ps : list (M.addr * M.val)) : MS.mem :=
  {| MS.mem_get := fun k => lookup_mem k ps |}.

Fixpoint env_of_pairs (ps : list (M.var * M.val)) : MS.env :=
  match ps with
  | [] => MS.empty_env
  | (x, v) :: ps' => MS.env_set (env_of_pairs ps') x v
  end.

(* === Sequential interpreter smoke tests === *)

Definition prog_load_store : list M.stmt :=
  [ M.SLoad "t" (M.EVal (M.VU64 1000)) M.TyF32
  ; M.SStore (M.EVal (M.VU64 2000)) (M.EVar "t") M.TyF32
  ].

Definition mu_ls : MS.mem :=
  mem_of_pairs [(1000, M.VF32 42%Z); (2000, M.VF32 0%Z)].
Definition cfg_ls : MS.cfg := MS.mk_cfg prog_load_store MS.empty_env mu_ls.

Definition prog_barrier : list M.stmt := [M.SBarrier].
Definition cfg_barrier : MS.cfg := MS.mk_cfg prog_barrier MS.empty_env mu_ls.

Definition prog_acqrel : list M.stmt :=
  [ M.SAtomicStoreRelease (M.EVal (M.VU64 3000))
      (M.EVal (M.VU32 1)) M.TyU32
  ; M.SAtomicLoadAcquire "f" (M.EVal (M.VU64 3000)) M.TyU32
  ].

Definition mu_flag : MS.mem := mem_of_pairs [(3000, M.VU32 0%Z)].
Definition cfg_flag : MS.cfg := MS.mk_cfg prog_acqrel MS.empty_env mu_flag.

Definition trace_ls : list M.event_mir := fst (MR.run 10 cfg_ls).
Definition trace_barrier : list M.event_mir := fst (MR.run 3 cfg_barrier).
Definition trace_acqrel : list M.event_mir := fst (MR.run 10 cfg_flag).

Example run_load_store_ok :
  trace_ls =
    [ M.EvLoad M.TyF32 1000 (M.VF32 42%Z)
    ; M.EvStore M.TyF32 2000 (M.VF32 42%Z) ].
Proof. reflexivity. Qed.

Example run_barrier_ok : trace_barrier = [M.EvBarrier].
Proof. reflexivity. Qed.

Example run_acqrel_ok :
  trace_acqrel =
    [ M.EvAtomicStoreRelease M.TyU32 3000 (M.VU32 1%Z)
    ; M.EvAtomicLoadAcquire M.TyU32 3000 (M.VU32 1%Z) ].
Proof. reflexivity. Qed.

(* === Thread tags survive MIR-to-PTX translation === *)

Example trans_load_store_ok :
  TR.translate_trace (TR.tag_trace 7%nat trace_ls) =
    [ (7%nat, P.EvLoad P.space_global P.sem_relaxed None P.MemF32 1000 42)
    ; (7%nat, P.EvStore P.space_global P.sem_relaxed None P.MemF32 2000 42) ].
Proof. reflexivity. Qed.

Example trans_barrier_ok :
  TR.translate_trace (TR.tag_trace 7%nat trace_barrier) =
    [(7%nat, P.EvBarrier P.scope_cta)].
Proof. reflexivity. Qed.

Example trans_acqrel_ok :
  TR.translate_trace (TR.tag_trace 7%nat trace_acqrel) =
    [ (7%nat, P.EvStore P.space_global P.sem_release
          (Some P.scope_sys) P.MemU32 3000 1)
    ; (7%nat, P.EvLoad P.space_global P.sem_acquire
          (Some P.scope_sys) P.MemU32 3000 1) ].
Proof. reflexivity. Qed.

(* === Generated programs via mir2coq === *)

Definition env_saxpy_gen : MS.env :=
  env_of_pairs [ ("_2", M.VU64 1000%Z)
               ; ("_3", M.VU64 2000%Z)
               ; ("_8", M.VU32 0%Z)
               ; ("_14", M.VF32 42%Z) ].

Definition mu_saxpy_gen : MS.mem :=
  mem_of_pairs [(1000, M.VF32 42%Z); (2000, M.VF32 0%Z)].

Definition trace_saxpy_gen : list M.event_mir :=
  fst (MR.run 10 (MS.mk_cfg SG.prog env_saxpy_gen mu_saxpy_gen)).

Example saxpy_gen_events_ok :
  trace_saxpy_gen =
    [ M.EvLoad M.TyF32 1000 (M.VF32 42%Z)
    ; M.EvLoad M.TyF32 2000 (M.VF32 0%Z)
    ; M.EvStore M.TyF32 2000 (M.VF32 42%Z) ].
Proof. reflexivity. Qed.

Example saxpy_gen_translate_ok :
  TR.translate_trace (TR.tag_trace 0%nat trace_saxpy_gen) =
    [ (0%nat, P.EvLoad P.space_global P.sem_relaxed None P.MemF32 1000 42)
    ; (0%nat, P.EvLoad P.space_global P.sem_relaxed None P.MemF32 2000 0)
    ; (0%nat, P.EvStore P.space_global P.sem_relaxed None P.MemF32 2000 42) ].
Proof. reflexivity. Qed.

Definition env_atomic_gen : MS.env :=
  env_of_pairs [("_3", M.VU64 3000%Z); ("_2", M.VU64 4000%Z)].

Definition mu_atomic_gen : MS.mem :=
  mem_of_pairs [(3000, M.VU32 0%Z); (4000, M.VU32 0%Z)].

Definition trace_atomic_gen : list M.event_mir :=
  fst (MR.run 10 (MS.mk_cfg AF.prog env_atomic_gen mu_atomic_gen)).

Example atomic_gen_events_ok :
  trace_atomic_gen =
    [ M.EvAtomicLoadAcquire M.TyU32 3000 (M.VU32 0%Z)
    ; M.EvStore M.TyU32 4000 (M.VU32 0%Z)
    ; M.EvAtomicStoreRelease M.TyU32 3000 (M.VU32 1%Z) ].
Proof. reflexivity. Qed.

Example atomic_gen_translate_ok :
  TR.translate_trace (TR.tag_trace 0%nat trace_atomic_gen) =
    [ (0%nat, P.EvLoad P.space_global P.sem_acquire
          (Some P.scope_sys) P.MemU32 3000 0)
    ; (0%nat, P.EvStore P.space_global P.sem_relaxed None P.MemU32 4000 0)
    ; (0%nat, P.EvStore P.space_global P.sem_release
          (Some P.scope_sys) P.MemU32 3000 1) ].
Proof. reflexivity. Qed.

(* === Reads-from is supplied as a candidate, not inferred from list order === *)

Definition candidate_trace : RF.trace :=
  [ (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 3000 1)
  ; (0%nat, P.EvStore P.SpaceGlobal P.SemRelaxed None P.MemU32 3000 2)
  ; (1%nat, P.EvLoad P.SpaceGlobal P.SemRelaxed None P.MemU32 3000 1) ].

Definition candidate_rf : RF.rf_map :=
  fun idx => if Nat.eqb idx 2%nat then Some 0%nat else None.

Example candidate_rf_can_select_nonlatest_store :
  RF.candidate_rf_edge candidate_trace candidate_rf 0%nat 2%nat.
Proof.
  unfold RF.candidate_rf_edge. split; [reflexivity|].
  exists 3000, 1.
  cbv [RF.load_at RF.store_at RF.event_at RF.tagged_event_at candidate_trace].
  repeat split; reflexivity.
Qed.

(* === Interleaving semantics can choose either runnable thread === *)

Definition thread0 : MC.thread :=
  MC.mk_thread 0%nat
    [M.SStore (M.EVal (M.VU64 10)) (M.EVal (M.VU32 1)) M.TyU32]
    MS.empty_env.

Definition thread1 : MC.thread :=
  MC.mk_thread 1%nat
    [M.SStore (M.EVal (M.VU64 20)) (M.EVal (M.VU32 2)) M.TyU32]
    MS.empty_env.

Definition concurrent_start : MC.machine :=
  MC.mk_machine [thread0; thread1] MS.empty_mem [].

Definition concurrent_after_thread0 : MC.machine :=
  MC.mk_machine
    [MC.mk_thread 0%nat [] MS.empty_env; thread1]
    (MS.mem_write MS.empty_mem 10 (M.VU32 1))
    [(0%nat, M.EvStore M.TyU32 10 (M.VU32 1))].

Definition concurrent_after_thread1 : MC.machine :=
  MC.mk_machine
    [thread0; MC.mk_thread 1%nat [] MS.empty_env]
    (MS.mem_write MS.empty_mem 20 (M.VU32 2))
    [(1%nat, M.EvStore M.TyU32 20 (M.VU32 2))].

Example concurrent_can_choose_thread0 :
  MC.machine_step concurrent_start concurrent_after_thread0.
Proof.
  eapply MC.MachineStep with
    (before := []) (current := thread0) (after := [thread1])
    (oev := Some (M.EvStore M.TyU32 10 (M.VU32 1)))
    (next := MS.mk_cfg [] MS.empty_env
      (MS.mem_write MS.empty_mem 10 (M.VU32 1))).
  apply MS.StepStore with (addr := 10) (v := M.VU32 1); reflexivity.
Qed.

Example concurrent_can_choose_thread1 :
  MC.machine_step concurrent_start concurrent_after_thread1.
Proof.
  eapply MC.MachineStep with
    (before := [thread0]) (current := thread1) (after := [])
    (oev := Some (M.EvStore M.TyU32 20 (M.VU32 2)))
    (next := MS.mk_cfg [] MS.empty_env
      (MS.mem_write MS.empty_mem 20 (M.VU32 2))).
  apply MS.StepStore with (addr := 20) (v := M.VU32 2); reflexivity.
Qed.

(* === Signed payload and scope regressions === *)

Definition trace_i32 : list M.event_mir :=
  [M.EvLoad M.TyI32 5000 (M.VI32 7%Z)].

Example trans_i32_ok :
  TR.translate_trace (TR.tag_trace 0%nat trace_i32) =
    [(0%nat, P.EvLoad P.space_global P.sem_relaxed None P.MemS32 5000 7)].
Proof. reflexivity. Qed.

Goal True.
  Fail unify (TR.translate_event M.EvBarrier) (P.EvBarrier P.scope_sys).
  Fail unify (TR.translate_trace (TR.tag_trace 0%nat trace_i32))
    [(0%nat, P.EvLoad P.space_global P.sem_relaxed None P.MemU32 5000 7)].
  exact I.
Qed.
