From Coq Require Import ZArith List String Bool Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax.

Module MIRSemantics.

Module M := MIR.

(** * Environments and memory models for the MVP MIR subset *)

Record env := {
  env_get : M.var -> option M.val
}.

Definition empty_env : env := {| env_get := fun _ => None |}.

Definition env_set (ρ : env) (x : M.var) (v : M.val) : env :=
  {| env_get := fun y => if String.eqb x y then Some v else env_get ρ y |}.

Record mem := {
  mem_get : M.addr -> option M.val
}.

Definition empty_mem : mem := {| mem_get := fun _ => None |}.

Definition mem_read (μ : mem) (a : M.addr) : option M.val := mem_get μ a.

Definition mem_write (μ : mem) (a : M.addr) (v : M.val) : mem :=
  {| mem_get := fun k => if Z.eqb k a then Some v else mem_get μ k |}.

Record cfg := {
  cfg_code : list M.stmt;
  cfg_env  : env;
  cfg_mem  : mem
}.

Definition mk_cfg (code : list M.stmt) (ρ : env) (μ : mem) : cfg :=
  {| cfg_code := code; cfg_env := ρ; cfg_mem := μ |}.

(** * Expression evaluation helpers *)

Definition offset_of_val (v : M.val) : option Z :=
  match v with
  | M.VI32 z => Some z
  | M.VU32 z => Some z
  | _ => None
  end.

Definition add_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (x + y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (x + y))
  | M.VF32 x, M.VF32 y => Some (M.VF32 (x + y))
  | _, _ => None
  end.

Definition mul_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (x * y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (x * y))
  | M.VF32 x, M.VF32 y => Some (M.VF32 (x * y))
  | _, _ => None
  end.

Definition lt_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VBool (Z.ltb x y))
  | M.VU32 x, M.VU32 y => Some (M.VBool (Z.ltb x y))
  | _, _ => None
  end.

Definition shr_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VU32 x, M.VU32 y => Some (M.VU32 (Z.shiftr x y))
  | _, _ => None
  end.

Fixpoint eval_expr (tid : nat) (ρ : env) (e : M.expr) : option M.val :=
  match e with
  | M.EVal v => Some v
  | M.EVar x => env_get ρ x
  | M.ETid => Some (M.VU32 (Z.of_nat tid))
  | M.EAdd e1 e2 =>
      match eval_expr tid ρ e1, eval_expr tid ρ e2 with
      | Some v1, Some v2 => add_vals v1 v2
      | _, _ => None
      end
  | M.EMul e1 e2 =>
      match eval_expr tid ρ e1, eval_expr tid ρ e2 with
      | Some v1, Some v2 => mul_vals v1 v2
      | _, _ => None
      end
  | M.EPtrAdd base ofs =>
      match eval_expr tid ρ base, eval_expr tid ρ ofs with
      | Some (M.VU64 a), Some off =>
          match offset_of_val off with
          | Some δ => Some (M.VU64 (a + δ))
          | None => None
          end
      | _, _ => None
      end
  | M.ELt e1 e2 =>
      match eval_expr tid ρ e1, eval_expr tid ρ e2 with
      | Some v1, Some v2 => lt_vals v1 v2
      | _, _ => None
      end
  | M.EShr e1 e2 =>
      match eval_expr tid ρ e1, eval_expr tid ρ e2 with
      | Some v1, Some v2 => shr_vals v1 v2
      | _, _ => None
      end
  end.

Definition eval_addr (tid : nat) (ρ : env) (e : M.expr) : option M.addr :=
  match eval_expr tid ρ e with
  | Some (M.VU64 a) => Some a
  | _ => None
  end.

Definition eval_bool (tid : nat) (ρ : env) (e : M.expr) : option bool :=
  match eval_expr tid ρ e with
  | Some (M.VBool b) => Some b
  | _ => None
  end.

(** Fully expand a statically bounded loop.  The fuel is computed once from
    [bound - i], so no back-edge survives in residual code.  This does not
    model dynamic or while-style loops. *)
Fixpoint unroll_for_fuel
    (counter : M.var) (i : Z) (fuel : nat) (body : list M.stmt)
    : list M.stmt :=
  match fuel with
  | O => []
  | S fuel' =>
      M.SAssign counter (M.EVal (M.VU32 i)) ::
      body ++ unroll_for_fuel counter (i + 1) fuel' body
  end.

Definition unroll_for
    (counter : M.var) (i bound : Z) (body : list M.stmt) : list M.stmt :=
  unroll_for_fuel counter i (Z.to_nat (bound - i)) body.

(** * Small-step semantics emitting MIR events *)

Inductive step : nat -> cfg -> option M.event_mir -> cfg -> Prop :=
| StepAssign : forall tid stk ρ μ x rhs v,
    eval_expr tid ρ rhs = Some v ->
    step tid (mk_cfg (M.SAssign x rhs :: stk) ρ μ) None
         (mk_cfg stk (env_set ρ x v) μ)
| StepLoad : forall tid stk ρ μ x ptr ty addr v,
    eval_addr tid ρ ptr = Some addr ->
    mem_read μ addr = Some v ->
    step tid (mk_cfg (M.SLoad x ptr ty :: stk) ρ μ)
         (Some (M.EvLoad ty addr v))
         (mk_cfg stk (env_set ρ x v) μ)
| StepStore : forall tid stk ρ μ ptr rhs ty addr v,
    eval_addr tid ρ ptr = Some addr ->
    eval_expr tid ρ rhs = Some v ->
    step tid (mk_cfg (M.SStore ptr rhs ty :: stk) ρ μ)
         (Some (M.EvStore ty addr v))
         (mk_cfg stk ρ (mem_write μ addr v))
| StepAtomicLoadAcquire : forall tid stk ρ μ x ptr ty addr v,
    eval_addr tid ρ ptr = Some addr ->
    mem_read μ addr = Some v ->
    step tid (mk_cfg (M.SAtomicLoadAcquire x ptr ty :: stk) ρ μ)
         (Some (M.EvAtomicLoadAcquire ty addr v))
         (mk_cfg stk (env_set ρ x v) μ)
| StepAtomicStoreRelease : forall tid stk ρ μ ptr rhs ty addr v,
    eval_addr tid ρ ptr = Some addr ->
    eval_expr tid ρ rhs = Some v ->
    step tid (mk_cfg (M.SAtomicStoreRelease ptr rhs ty :: stk) ρ μ)
         (Some (M.EvAtomicStoreRelease ty addr v))
         (mk_cfg stk ρ (mem_write μ addr v))
| StepBarrier : forall tid stk ρ μ,
    step tid (mk_cfg (M.SBarrier :: stk) ρ μ)
         (Some M.EvBarrier)
         (mk_cfg stk ρ μ)
| StepIfTrue : forall tid stk ρ μ cond t_branch f_branch,
    eval_bool tid ρ cond = Some true ->
    step tid (mk_cfg (M.SIf cond t_branch f_branch :: stk) ρ μ)
         None
         (mk_cfg (t_branch ++ stk) ρ μ)
| StepIfFalse : forall tid stk ρ μ cond t_branch f_branch,
    eval_bool tid ρ cond = Some false ->
    step tid (mk_cfg (M.SIf cond t_branch f_branch :: stk) ρ μ)
         None
         (mk_cfg (f_branch ++ stk) ρ μ)
| StepSeq : forall tid stk ρ μ body,
    step tid (mk_cfg (M.SSeq body :: stk) ρ μ)
         None
         (mk_cfg (body ++ stk) ρ μ)
| StepForZero : forall tid stk ρ μ counter bound body,
    bound <= 0 ->
    step tid (mk_cfg (M.SFor counter bound body :: stk) ρ μ)
         None
         (mk_cfg stk ρ μ)
| StepForUnfold : forall tid stk ρ μ counter bound body,
    0 < bound ->
    step tid (mk_cfg (M.SFor counter bound body :: stk) ρ μ)
         None
         (mk_cfg (unroll_for counter 0 bound body ++ stk) ρ μ).

(** Shared loads, stores, and barriers deliberately have no [step]
    constructor.  They require machine-owned shared memory and are handled by
    [MIRConcurrent]; the per-thread relation is partial at those heads. *)

Lemma unroll_for_zero : forall counter body,
  unroll_for counter 0 0 body = [].
Proof. intros. reflexivity. Qed.

Lemma unroll_for_fuel_length : forall counter i fuel body,
  List.length (unroll_for_fuel counter i fuel body) =
  (fuel * (1 + List.length body))%nat.
Proof.
  intros counter i fuel. revert i. induction fuel as [|fuel IH]; intros i body.
  - reflexivity.
  - cbn [unroll_for_fuel].
    change (S (List.length (body ++
      unroll_for_fuel counter (i + 1) fuel body)) =
      (S fuel * (1 + List.length body))%nat).
    rewrite List.app_length, IH. lia.
Qed.

Lemma unroll_for_three_heads : forall counter body,
  List.length (unroll_for counter 0 3 body) =
  (3 * (1 + List.length body))%nat.
Proof.
  intros. unfold unroll_for.
  change (List.length (unroll_for_fuel counter 0 3 body) =
    (3 * (1 + List.length body))%nat).
  apply unroll_for_fuel_length.
Qed.

(** * Simple environment lemmas for later proofs *)

Lemma env_get_set_same : forall ρ x v,
  env_get (env_set ρ x v) x = Some v.
Proof.
  intros ρ x v. unfold env_get, env_set. now rewrite String.eqb_refl.
Qed.

Lemma env_get_set_other : forall ρ x y v,
  x <> y -> env_get (env_set ρ x v) y = env_get ρ y.
Proof.
  intros ρ x y v Hneq. unfold env_get, env_set.
  destruct (String.eqb x y) eqn:Hxy.
  - apply String.eqb_eq in Hxy; subst; contradiction.
  - reflexivity.
Qed.

End MIRSemantics.
