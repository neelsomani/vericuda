From Coq Require Import ZArith List String Bool.

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
  | M.VU64 x, M.VU64 y => Some (M.VU64 (x + y))
  | M.VF32 x, M.VF32 y => Some (M.VF32 (x + y))
  | _, _ => None
  end.

Definition sub_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (x - y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (x - y))
  | M.VU64 x, M.VU64 y => Some (M.VU64 (x - y))
  | M.VF32 x, M.VF32 y => Some (M.VF32 (x - y))
  | _, _ => None
  end.

Definition mul_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (x * y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (x * y))
  | M.VU64 x, M.VU64 y => Some (M.VU64 (x * y))
  | M.VF32 x, M.VF32 y => Some (M.VF32 (x * y))
  | _, _ => None
  end.

Definition div_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => if Z.eqb y 0 then None else Some (M.VI32 (Z.quot x y))
  | M.VU32 x, M.VU32 y => if Z.eqb y 0 then None else Some (M.VU32 (Z.quot x y))
  | M.VU64 x, M.VU64 y => if Z.eqb y 0 then None else Some (M.VU64 (Z.quot x y))
  | M.VF32 x, M.VF32 y => if Z.eqb y 0 then None else Some (M.VF32 (Z.quot x y))
  | _, _ => None
  end.

Definition rem_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => if Z.eqb y 0 then None else Some (M.VI32 (Z.rem x y))
  | M.VU32 x, M.VU32 y => if Z.eqb y 0 then None else Some (M.VU32 (Z.rem x y))
  | M.VU64 x, M.VU64 y => if Z.eqb y 0 then None else Some (M.VU64 (Z.rem x y))
  | _, _ => None
  end.

Definition xor_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (Z.lxor x y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (Z.lxor x y))
  | M.VU64 x, M.VU64 y => Some (M.VU64 (Z.lxor x y))
  | _, _ => None
  end.

Definition shl_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (Z.shiftl x y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (Z.shiftl x y))
  | M.VU64 x, M.VU64 y => Some (M.VU64 (Z.shiftl x y))
  | _, _ => None
  end.

Definition shr_vals (v1 v2 : M.val) : option M.val :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (M.VI32 (Z.shiftr x y))
  | M.VU32 x, M.VU32 y => Some (M.VU32 (Z.shiftr x y))
  | M.VU64 x, M.VU64 y => Some (M.VU64 (Z.shiftr x y))
  | _, _ => None
  end.

Definition int_of_val (v : M.val) : option Z :=
  match v with
  | M.VI32 z => Some z
  | M.VU32 z => Some z
  | M.VU64 z => Some z
  | _ => None
  end.

Definition bool_of_val (v : M.val) : option bool :=
  match v with
  | M.VBool b => Some b
  | M.VI32 z => Some (negb (Z.eqb z 0))
  | M.VU32 z => Some (negb (Z.eqb z 0))
  | M.VU64 z => Some (negb (Z.eqb z 0))
  | _ => None
  end.

Definition eq_vals (v1 v2 : M.val) : option bool :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (Z.eqb x y)
  | M.VU32 x, M.VU32 y => Some (Z.eqb x y)
  | M.VU64 x, M.VU64 y => Some (Z.eqb x y)
  | M.VF32 x, M.VF32 y => Some (Z.eqb x y)
  | M.VBool b1, M.VBool b2 => Some (Bool.eqb b1 b2)
  | _, _ => None
  end.

Definition lt_vals (v1 v2 : M.val) : option bool :=
  match v1, v2 with
  | M.VI32 x, M.VI32 y => Some (Z.ltb x y)
  | M.VU32 x, M.VU32 y => Some (Z.ltb x y)
  | M.VU64 x, M.VU64 y => Some (Z.ltb x y)
  | _, _ => None
  end.

Fixpoint eval_expr (ρ : env) (e : M.expr) : option M.val :=
  match e with
  | M.EVal v => Some v
  | M.EVar x => env_get ρ x
  | M.EAdd e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => add_vals v1 v2
    | _, _ => None
    end
  | M.ESub e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => sub_vals v1 v2
    | _, _ => None
    end
  | M.EMul e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => mul_vals v1 v2
    | _, _ => None
    end
  | M.EDiv e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => div_vals v1 v2
    | _, _ => None
    end
  | M.ERem e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => rem_vals v1 v2
    | _, _ => None
    end
  | M.ELt e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 =>
      match lt_vals v1 v2 with
      | Some b => Some (M.VBool b)
      | None => None
      end
    | _, _ => None
    end
  | M.EEq e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 =>
      match eq_vals v1 v2 with
      | Some b => Some (M.VBool b)
      | None => None
      end
    | _, _ => None
    end
  | M.EAnd e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 =>
      match bool_of_val v1, bool_of_val v2 with
      | Some b1, Some b2 => Some (M.VBool (andb b1 b2))
      | _, _ => None
      end
    | _, _ => None
    end
  | M.EXor e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => xor_vals v1 v2
    | _, _ => None
    end
  | M.EShl e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => shl_vals v1 v2
    | _, _ => None
    end
  | M.EShr e1 e2 =>
    match eval_expr ρ e1, eval_expr ρ e2 with
    | Some v1, Some v2 => shr_vals v1 v2
    | _, _ => None
    end
  | M.ENot e1 =>
    match eval_expr ρ e1 with
    | Some v =>
      match bool_of_val v with
      | Some b => Some (M.VBool (negb b))
      | None => None
      end
    | None => None
    end
  | M.EPtrAdd base ofs =>
      match eval_expr ρ base, eval_expr ρ ofs with
      | Some (M.VU64 a), Some off =>
          match offset_of_val off with
          | Some δ => Some (M.VU64 (a + δ))
          | None => None
          end
      | _, _ => None
      end
  end.

Definition eval_addr (ρ : env) (e : M.expr) : option M.addr :=
  match eval_expr ρ e with
  | Some (M.VU64 a) => Some a
  | _ => None
  end.

Definition eval_bool (ρ : env) (e : M.expr) : option bool :=
  match eval_expr ρ e with
  | Some (M.VBool b) => Some b
  | _ => None
  end.

(** * Small-step semantics emitting MIR events *)

Inductive step : cfg -> option M.event_mir -> cfg -> Prop :=
| StepAssign : forall stk ρ μ x rhs v,
  eval_expr ρ rhs = Some v ->
  step (mk_cfg (M.SAssign x rhs :: stk) ρ μ)
     (Some (M.EvAssign x v))
     (mk_cfg stk (env_set ρ x v) μ)
| StepLoad : forall stk ρ μ x ptr ty addr v,
    eval_addr ρ ptr = Some addr ->
    mem_read μ addr = Some v ->
    step (mk_cfg (M.SLoad x ptr ty :: stk) ρ μ)
         (Some (M.EvLoad ty addr v))
         (mk_cfg stk (env_set ρ x v) μ)
| StepStore : forall stk ρ μ ptr rhs ty addr v,
    eval_addr ρ ptr = Some addr ->
    eval_expr ρ rhs = Some v ->
    step (mk_cfg (M.SStore ptr rhs ty :: stk) ρ μ)
         (Some (M.EvStore ty addr v))
         (mk_cfg stk ρ (mem_write μ addr v))
| StepAtomicLoadAcquire : forall stk ρ μ x ptr ty addr v,
    eval_addr ρ ptr = Some addr ->
    mem_read μ addr = Some v ->
    step (mk_cfg (M.SAtomicLoadAcquire x ptr ty :: stk) ρ μ)
         (Some (M.EvAtomicLoadAcquire ty addr v))
         (mk_cfg stk (env_set ρ x v) μ)
| StepAtomicStoreRelease : forall stk ρ μ ptr rhs ty addr v,
    eval_addr ρ ptr = Some addr ->
    eval_expr ρ rhs = Some v ->
    step (mk_cfg (M.SAtomicStoreRelease ptr rhs ty :: stk) ρ μ)
         (Some (M.EvAtomicStoreRelease ty addr v))
         (mk_cfg stk ρ (mem_write μ addr v))
| StepBarrier : forall stk ρ μ,
    step (mk_cfg (M.SBarrier :: stk) ρ μ)
         (Some M.EvBarrier)
         (mk_cfg stk ρ μ)
| StepIfTrue : forall stk ρ μ cond t_branch f_branch,
  eval_bool ρ cond = Some true ->
  step (mk_cfg (M.SIf cond t_branch f_branch :: stk) ρ μ)
     (Some (M.EvCond cond true))
     (mk_cfg (t_branch ++ stk) ρ μ)
| StepIfFalse : forall stk ρ μ cond t_branch f_branch,
  eval_bool ρ cond = Some false ->
  step (mk_cfg (M.SIf cond t_branch f_branch :: stk) ρ μ)
     (Some (M.EvCond cond false))
     (mk_cfg (f_branch ++ stk) ρ μ)
| StepWhileTrue : forall stk ρ μ cond body,
  eval_bool ρ cond = Some true ->
  step (mk_cfg (M.SWhile cond body :: stk) ρ μ)
     (Some (M.EvCond cond true))
     (mk_cfg (body ++ (M.SWhile cond body :: stk)) ρ μ)
| StepWhileFalse : forall stk ρ μ cond body,
  eval_bool ρ cond = Some false ->
  step (mk_cfg (M.SWhile cond body :: stk) ρ μ)
     (Some (M.EvCond cond false))
     (mk_cfg stk ρ μ)
| StepLoop : forall stk ρ μ body,
    step (mk_cfg (M.SLoop body :: stk) ρ μ)
      None
      (mk_cfg (body ++ (M.SLoop body :: stk)) ρ μ)
| StepSeq : forall stk ρ μ body,
    step (mk_cfg (M.SSeq body :: stk) ρ μ)
         None
         (mk_cfg (body ++ stk) ρ μ).

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
