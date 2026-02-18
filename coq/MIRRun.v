From Coq Require Import ZArith List String Bool.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax.
Require Import MIRSemantics.

Module MIRRun.

Module M := MIR.
Module MS := MIRSemantics.

Definition step_fun (c : MS.cfg) : option (option M.event_mir * MS.cfg) :=
  match MS.cfg_code c with
  | [] => None
  | instr :: rest =>
      let ρ := MS.cfg_env c in
      let μ := MS.cfg_mem c in
      match instr with
      | M.SAssign x rhs =>
          match MS.eval_expr ρ rhs with
          | Some v =>
              let cfg' := {| MS.cfg_code := rest;
                              MS.cfg_env := MS.env_set ρ x v;
                              MS.cfg_mem := μ |} in
              Some (None, cfg')
          | None => None
          end
      | M.SLoad x ptr ty =>
          match MS.eval_addr ρ ptr with
          | Some addr =>
              match MS.mem_read μ addr with
              | Some v =>
                  let cfg' := {| MS.cfg_code := rest;
                                  MS.cfg_env := MS.env_set ρ x v;
                                  MS.cfg_mem := μ |} in
                  Some (Some (M.EvLoad ty addr v), cfg')
              | None => None
              end
          | None => None
          end
      | M.SStore ptr rhs ty =>
          match MS.eval_addr ρ ptr, MS.eval_expr ρ rhs with
          | Some addr, Some v =>
              let cfg' := {| MS.cfg_code := rest;
                              MS.cfg_env := ρ;
                              MS.cfg_mem := MS.mem_write μ addr v |} in
              Some (Some (M.EvStore ty addr v), cfg')
          | _, _ => None
          end
      | M.SAtomicLoadAcquire x ptr ty =>
          match MS.eval_addr ρ ptr with
          | Some addr =>
              match MS.mem_read μ addr with
              | Some v =>
                  let cfg' := {| MS.cfg_code := rest;
                                  MS.cfg_env := MS.env_set ρ x v;
                                  MS.cfg_mem := μ |} in
                  Some (Some (M.EvAtomicLoadAcquire ty addr v), cfg')
              | None => None
              end
          | None => None
          end
      | M.SAtomicStoreRelease ptr rhs ty =>
          match MS.eval_addr ρ ptr, MS.eval_expr ρ rhs with
          | Some addr, Some v =>
              let cfg' := {| MS.cfg_code := rest;
                              MS.cfg_env := ρ;
                              MS.cfg_mem := MS.mem_write μ addr v |} in
              Some (Some (M.EvAtomicStoreRelease ty addr v), cfg')
          | _, _ => None
          end
      | M.SBarrier =>
          let cfg' := {| MS.cfg_code := rest;
                          MS.cfg_env := ρ;
                          MS.cfg_mem := μ |} in
          Some (Some M.EvBarrier, cfg')
      | M.SIf cond t_branch f_branch =>
          match MS.eval_bool ρ cond with
          | Some true =>
              let cfg' := {| MS.cfg_code := t_branch ++ rest;
                              MS.cfg_env := ρ;
                              MS.cfg_mem := μ |} in
              Some (None, cfg')
          | Some false =>
              let cfg' := {| MS.cfg_code := f_branch ++ rest;
                              MS.cfg_env := ρ;
                              MS.cfg_mem := μ |} in
              Some (None, cfg')
          | None => None
          end
      | M.SLoop body =>
          let cfg' := {| MS.cfg_code := body ++ (M.SLoop body :: rest);
                          MS.cfg_env := ρ;
                          MS.cfg_mem := μ |} in
          Some (None, cfg')
      | M.SSeq body =>
          let cfg' := {| MS.cfg_code := body ++ rest;
                          MS.cfg_env := ρ;
                          MS.cfg_mem := μ |} in
          Some (None, cfg')
      end
  end.

Fixpoint run (fuel : nat) (c : MS.cfg) : list M.event_mir * MS.cfg :=
  match fuel with
  | O => ([], c)
  | S n =>
      match step_fun c with
      | None => ([], c)
      | Some (oev, c') =>
          let '(evs, c'') := run n c' in
          match oev with
          | None => (evs, c'')
          | Some ev => (ev :: evs, c'')
          end
      end
  end.

End MIRRun.
