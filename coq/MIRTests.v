From Coq Require Import ZArith List String Bool Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax.
Require Import MIRSemantics.
Require Import MIRRun.
Require Import PTXImports.
Require Import PTXRelations.
Require Import Translate.
Require Import saxpy_gen.
Require Import atomic_flag_gen.

Module M := MIR.
Module MS := MIRSemantics.
Module MR := MIRRun.
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

Definition extend_env (ρ : MS.env) (x : M.var) (v : M.val) : MS.env :=
  MS.env_set ρ x v.

Definition empty_env : MS.env := MS.empty_env.

Fixpoint env_of_pairs (ps : list (M.var * M.val)) : MS.env :=
  match ps with
  | [] => MS.empty_env
  | (x, v) :: ps' => MS.env_set (env_of_pairs ps') x v
  end.

(* === Test 1: relaxed load followed by store === *)

Definition prog_load_store : list M.stmt :=
  [ M.SLoad "t" (M.EVal (M.VU64 1000)) M.TyF32
  ; M.SStore (M.EVal (M.VU64 2000)) (M.EVar "t") M.TyF32
  ].

Definition μ_ls : MS.mem := mem_of_pairs [(1000, M.VF32 42%Z); (2000, M.VF32 0%Z)].
Definition cfg_ls : MS.cfg := MS.mk_cfg prog_load_store empty_env μ_ls.

Eval compute in (MR.run 10 cfg_ls).

(* === Test 2: barrier emits exactly one event === *)

Definition prog_barrier : list M.stmt := [M.SBarrier].
Definition cfg_barrier : MS.cfg := MS.mk_cfg prog_barrier empty_env μ_ls.

Eval compute in (MR.run 3 cfg_barrier).

(* === Test 3: acquire/release flag round trip === *)

Definition prog_acqrel : list M.stmt :=
  [ M.SAtomicStoreRelease (M.EVal (M.VU64 3000)) (M.EVal (M.VU32 1)) M.TyU32
  ; M.SAtomicLoadAcquire "f" (M.EVal (M.VU64 3000)) M.TyU32
  ].

Definition μ_flag : MS.mem := mem_of_pairs [(3000, M.VU32 0%Z)].
Definition cfg_flag : MS.cfg := MS.mk_cfg prog_acqrel empty_env μ_flag.

Eval compute in (MR.run 10 cfg_flag).

(* === Step 3: translating MIR traces to PTX events === *)

Definition trace_ls : list M.event_mir := fst (MR.run 10 cfg_ls).
Definition trace_barrier : list M.event_mir := fst (MR.run 3 cfg_barrier).
Definition trace_acqrel : list M.event_mir := fst (MR.run 10 cfg_flag).

Example trans_load_store_ok :
  TR.translate_trace trace_ls =
    [ P.EvLoad  P.space_global P.sem_relaxed None P.MemF32 1000 42
    ; P.EvStore P.space_global P.sem_relaxed None P.MemF32 2000 42 ].
Proof. reflexivity. Qed.

Example trans_barrier_ok :
  TR.translate_trace trace_barrier =
    [ P.EvBarrier P.scope_cta ].
Proof. reflexivity. Qed.

Example trans_acqrel_ok :
  TR.translate_trace trace_acqrel =
    [ P.EvStore P.space_global P.sem_release (Some P.scope_sys) P.MemU32 3000 1
    ; P.EvLoad  P.space_global P.sem_acquire (Some P.scope_sys) P.MemU32 3000 1 ].
Proof. reflexivity. Qed.

(* === Step 4: generated programs via mir2coq === *)

Definition env_saxpy_gen : MS.env :=
  env_of_pairs [ ("_2", M.VU64 1000%Z)
               ; ("_3", M.VU64 2000%Z)
               ; ("_6", M.VBool true)
               ; ("_8", M.VU32 0%Z)
               ; ("_14", M.VF32 42%Z)
               ].

Definition μ_saxpy_gen : MS.mem :=
  mem_of_pairs [(1000, M.VF32 42%Z); (2000, M.VF32 0%Z)].

Definition cfg_saxpy_gen : MS.cfg :=
  MS.mk_cfg SG.prog env_saxpy_gen μ_saxpy_gen.

(* Fuel 4 = guard step + three body instructions, yielding one loop iteration. *)
Definition trace_saxpy_gen : list M.event_mir := fst (MR.run 4 cfg_saxpy_gen).

Example saxpy_gen_events_ok :
  trace_saxpy_gen =
    [ M.EvLoad M.TyF32 1000 (M.VF32 42%Z)
    ; M.EvLoad M.TyF32 2000 (M.VF32 0%Z)
    ; M.EvStore M.TyF32 2000 (M.VF32 42%Z)
    ].
Proof. reflexivity. Qed.

Example saxpy_gen_translate_ok :
  TR.translate_trace trace_saxpy_gen =
    [ P.EvLoad  P.space_global P.sem_relaxed None P.MemF32 1000 42
    ; P.EvLoad  P.space_global P.sem_relaxed None P.MemF32 2000 0
    ; P.EvStore P.space_global P.sem_relaxed None P.MemF32 2000 42 ].
Proof. reflexivity. Qed.

Definition env_atomic_gen : MS.env :=
  env_of_pairs [ ("_3", M.VU64 3000%Z)
               ; ("_2", M.VU64 4000%Z)
               ].

Definition μ_atomic_gen : MS.mem :=
  mem_of_pairs [(3000, M.VU32 0%Z); (4000, M.VU32 0%Z)].

Definition cfg_atomic_gen : MS.cfg :=
  MS.mk_cfg AF.prog env_atomic_gen μ_atomic_gen.

Definition trace_atomic_gen : list M.event_mir := fst (MR.run 10 cfg_atomic_gen).

Example atomic_gen_events_ok :
  trace_atomic_gen =
    [ M.EvAtomicLoadAcquire M.TyU32 3000 (M.VU32 0%Z)
    ; M.EvStore M.TyU32 4000 (M.VU32 0%Z)
    ; M.EvAtomicStoreRelease M.TyU32 3000 (M.VU32 1%Z)
    ].
Proof. reflexivity. Qed.

Example atomic_gen_translate_ok :
  TR.translate_trace trace_atomic_gen =
    [ P.EvLoad  P.space_global P.sem_acquire (Some P.scope_sys) P.MemU32 3000 0
    ; P.EvStore P.space_global P.sem_relaxed None P.MemU32 4000 0
    ; P.EvStore P.space_global P.sem_release (Some P.scope_sys) P.MemU32 3000 1 ].
Proof. reflexivity. Qed.

(* === Step 5: reads-from maps and coherence relations === *)

(* === Saxpy_gen trace === *)

Definition rf_saxpy_gen : RF.rf_map :=
  RF.rf_of_trace (TR.translate_trace trace_saxpy_gen).

Example saxpy_gen_rf_0_none :
  rf_saxpy_gen 0%nat = None.
Proof. reflexivity. Qed.

Example saxpy_gen_rf_1_none :
  rf_saxpy_gen 1%nat = None.
Proof. reflexivity. Qed.

Example saxpy_gen_rf_2_none :
  rf_saxpy_gen 2%nat = None.
Proof. reflexivity. Qed.

Definition co_saxpy_gen : RF.co_rel :=
  RF.co_of_trace (TR.translate_trace trace_saxpy_gen).

Example saxpy_gen_co_irrefl :
  ~ co_saxpy_gen 2%nat 2%nat.
Proof. vm_compute. intros contra. inversion contra. Qed.

(* === Atomic_flag_gen trace === *)

Definition rf_atomic_gen : RF.rf_map :=
  RF.rf_of_trace (TR.translate_trace trace_atomic_gen).

Example atomic_gen_rf_load_none :
  rf_atomic_gen 0%nat = None.
Proof. reflexivity. Qed.

Example atomic_gen_rf_store_none :
  rf_atomic_gen 1%nat = None.
Proof. reflexivity. Qed.

Definition co_atomic_gen : RF.co_rel :=
  RF.co_of_trace (TR.translate_trace trace_atomic_gen).

Example atomic_gen_co_disjoint :
  ~ co_atomic_gen 2%nat 1%nat.
Proof. vm_compute. intros contra. inversion contra. Qed.

(* === multi-reads-from trace === *)

Definition prog_multi_rf : list M.stmt :=
  [ M.SStore (M.EVal (M.VU64 3000)) (M.EVal (M.VU32 1)) M.TyU32
  ; M.SLoad "x1" (M.EVal (M.VU64 3000)) M.TyU32
  ; M.SStore (M.EVal (M.VU64 3000)) (M.EVal (M.VU32 2)) M.TyU32
  ; M.SLoad "x2" (M.EVal (M.VU64 3000)) M.TyU32
  ].

Definition μ_multi_rf : MS.mem := mem_of_pairs [(3000, M.VU32 0%Z)].
Definition cfg_multi_rf : MS.cfg := MS.mk_cfg prog_multi_rf empty_env μ_multi_rf.
Definition trace_multi_rf : list M.event_mir := fst (MR.run 10 cfg_multi_rf).

Example multi_rf_events_ok :
  trace_multi_rf =
    [ M.EvStore M.TyU32 3000 (M.VU32 1%Z)
    ; M.EvLoad  M.TyU32 3000 (M.VU32 1%Z)
    ; M.EvStore M.TyU32 3000 (M.VU32 2%Z)
    ; M.EvLoad  M.TyU32 3000 (M.VU32 2%Z)
    ].
Proof. reflexivity. Qed.

Example multi_rf_translate_ok :
  TR.translate_trace trace_multi_rf =
    [ P.EvStore P.space_global P.sem_relaxed None P.MemU32 3000 1
    ; P.EvLoad  P.space_global P.sem_relaxed None P.MemU32 3000 1
    ; P.EvStore P.space_global P.sem_relaxed None P.MemU32 3000 2
    ; P.EvLoad  P.space_global P.sem_relaxed None P.MemU32 3000 2
    ].
Proof. reflexivity. Qed.

Definition rf_multi_rf : RF.rf_map :=
  RF.rf_of_trace (TR.translate_trace trace_multi_rf).

Example multi_rf_rf_0_none :
  rf_multi_rf 0%nat = None.
Proof. reflexivity. Qed.

Example multi_rf_rf_1_from0 :
  rf_multi_rf 1%nat = Some 0%nat.
Proof. reflexivity. Qed.

Example multi_rf_rf_2_none :
  rf_multi_rf 2%nat = None.
Proof. reflexivity. Qed.

Example multi_rf_rf_3_from2 :
  rf_multi_rf 3%nat = Some 2%nat.
Proof. reflexivity. Qed.

Definition co_multi_rf : RF.co_rel :=
  RF.co_of_trace (TR.translate_trace trace_multi_rf).

Example multi_rf_co_order :
  co_multi_rf 0%nat 2%nat.
Proof. vm_compute. lia. Qed.

Example multi_rf_co_no_reverse :
  ~ co_multi_rf 2%nat 0%nat.
Proof. vm_compute. intros contra. lia. Qed.

(* === two stores coherence test === *)

Definition prog_two_stores : list M.stmt :=
  [ M.SStore (M.EVal (M.VU64 7000)) (M.EVal (M.VI32 1%Z)) M.TyI32
  ; M.SStore (M.EVal (M.VU64 7000)) (M.EVal (M.VI32 2%Z)) M.TyI32
  ].

Definition μ_two_stores : MS.mem := mem_of_pairs [(7000, M.VI32 0%Z)].
Definition cfg_two_stores : MS.cfg := MS.mk_cfg prog_two_stores empty_env μ_two_stores.
Definition trace_two_stores : list M.event_mir := fst (MR.run 5 cfg_two_stores).

Definition co_two_stores : RF.co_rel :=
  RF.co_of_trace (TR.translate_trace trace_two_stores).

Example co_two_stores_order :
  co_two_stores 0%nat 1%nat.
Proof. vm_compute. lia. Qed.

Example co_two_stores_asym :
  ~ co_two_stores 1%nat 0%nat.
Proof. vm_compute. intros contra. lia. Qed.

(* === Additional regression: i32 loads use MemS32 === *)

Definition prog_i32 : list M.stmt :=
  [ M.SLoad "x" (M.EVal (M.VU64 5000)) M.TyI32
  ; M.SStore (M.EVal (M.VU64 6000)) (M.EVar "x") M.TyI32
  ].

Definition μ_i32 : MS.mem := mem_of_pairs [(5000, M.VI32 7%Z); (6000, M.VI32 0%Z)].
Definition cfg_i32 : MS.cfg := MS.mk_cfg prog_i32 empty_env μ_i32.
Definition tr_i32 : list M.event_mir := fst (MR.run 5 cfg_i32).

Example trans_i32_ok :
  TR.translate_trace tr_i32 =
    [ P.EvLoad  P.space_global P.sem_relaxed None P.MemS32 5000 7
    ; P.EvStore P.space_global P.sem_relaxed None P.MemS32 6000 7 ].
Proof. reflexivity. Qed.

(* === Negative assertions: intentional failures to guard invariants === *)

(* 1) Signed 32-bit payloads must map to MemS32, not MemU32. *)
Definition prog_i32_neg : list M.stmt :=
  [ M.SLoad "x" (M.EVal (M.VU64 5000)) M.TyI32 ].
Definition μ_i32_neg : MS.mem := mem_of_pairs [(5000, M.VI32 7%Z)].
Definition cfg_i32_neg : MS.cfg := MS.mk_cfg prog_i32_neg empty_env μ_i32_neg.
Definition tr_i32_neg : list M.event_mir := fst (MR.run 3 cfg_i32_neg).
(* 2) Acquire loads must carry SYS scope. *)
Definition tr_acq : list M.event_mir :=
  [M.EvAtomicLoadAcquire M.TyU32 0 (M.VU32 0%Z)].

Goal True.
  Fail unify (TR.translate_event M.EvBarrier) (P.EvBarrier P.scope_sys).
  Fail unify (TR.translate_trace tr_i32_neg)
            [ P.EvLoad P.space_global P.sem_relaxed None P.MemU32 5000 7 ].
  Fail unify (TR.translate_trace tr_acq)
            [ P.EvLoad P.space_global P.sem_acquire (Some P.scope_cta) P.MemU32 0 0 ].
  exact I.
Qed.
