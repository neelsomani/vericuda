From Coq Require Import ZArith List String Bool Lia.

Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

Require Import MIRSyntax.
Require Import MIRSemantics.

Module MIRRun.

Module M := MIR.
Module MS := MIRSemantics.

Definition step_fun (tid : nat) (c : MS.cfg)
    : option (option M.event_mir * MS.cfg) :=
  match MS.cfg_code c with
  | [] => None
  | instr :: rest =>
      let ρ := MS.cfg_env c in
      let μ := MS.cfg_mem c in
      match instr with
      | M.SAssign x rhs =>
          match MS.eval_expr tid ρ rhs with
          | Some v =>
              let cfg' := {| MS.cfg_code := rest;
                              MS.cfg_env := MS.env_set ρ x v;
                              MS.cfg_mem := μ |} in
              Some (None, cfg')
          | None => None
          end
      | M.SLoad x ptr ty =>
          match MS.eval_addr tid ρ ptr with
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
          match MS.eval_addr tid ρ ptr, MS.eval_expr tid ρ rhs with
          | Some addr, Some v =>
              let cfg' := {| MS.cfg_code := rest;
                              MS.cfg_env := ρ;
                              MS.cfg_mem := MS.mem_write μ addr v |} in
              Some (Some (M.EvStore ty addr v), cfg')
          | _, _ => None
          end
      | M.SAtomicLoadAcquire x ptr ty =>
          match MS.eval_addr tid ρ ptr with
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
          match MS.eval_addr tid ρ ptr, MS.eval_expr tid ρ rhs with
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
      | M.SLoadShared _ _ _ => None
      | M.SStoreShared _ _ _ => None
      | M.SBarrierShared => None
      | M.SIf cond t_branch f_branch =>
          match MS.eval_bool tid ρ cond with
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
      | M.SSeq body =>
          let cfg' := {| MS.cfg_code := body ++ rest;
                          MS.cfg_env := ρ;
                          MS.cfg_mem := μ |} in
          Some (None, cfg')
      | M.SFor counter bound body =>
          if Z.leb bound 0 then
            let cfg' := {| MS.cfg_code := rest;
                            MS.cfg_env := ρ;
                            MS.cfg_mem := μ |} in
            Some (None, cfg')
          else
            let cfg' := {| MS.cfg_code :=
                              MS.unroll_for counter 0 bound body ++ rest;
                            MS.cfg_env := ρ;
                            MS.cfg_mem := μ |} in
            Some (None, cfg')
      end
  end.

(** The executable and relational presentations describe exactly the same
    one-thread step.  Both are deliberately partial when a shared-memory
    statement is at the head: those statements only step in the machine-level
    semantics.  Thus computations performed by [run] are evidence about
    [MIRSemantics.step], not an independent or shared-memory model. *)
Lemma step_fun_sound : forall tid c oev c',
  step_fun tid c = Some (oev, c') -> MS.step tid c oev c'.
Proof.
  intros tid [code rho memory] oev c' Hrun.
  destruct code as [|instruction rest]; cbn in Hrun; try discriminate.
  destruct instruction as
    [x rhs | x ptr ty | ptr rhs ty | x ptr ty | ptr rhs ty
    | | x ptr ty | ptr rhs ty | | cond then_branch else_branch | body
    | counter bound body]; cbn in Hrun.
  - destruct (MS.eval_expr tid rho rhs) as [value|] eqn:Heval; try discriminate.
    inversion Hrun; subst. now apply MS.StepAssign.
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr; try discriminate.
    destruct (MS.mem_read memory addr) as [value|] eqn:Hread; try discriminate.
    inversion Hrun; subst. now eapply MS.StepLoad.
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr; try discriminate.
    destruct (MS.eval_expr tid rho rhs) as [value|] eqn:Heval; try discriminate.
    inversion Hrun; subst. now eapply MS.StepStore.
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr; try discriminate.
    destruct (MS.mem_read memory addr) as [value|] eqn:Hread; try discriminate.
    inversion Hrun; subst. now eapply MS.StepAtomicLoadAcquire.
  - destruct (MS.eval_addr tid rho ptr) as [addr|] eqn:Haddr; try discriminate.
    destruct (MS.eval_expr tid rho rhs) as [value|] eqn:Heval; try discriminate.
    inversion Hrun; subst. now eapply MS.StepAtomicStoreRelease.
  - inversion Hrun; subst. apply MS.StepBarrier.
  - discriminate.
  - discriminate.
  - discriminate.
  - destruct (MS.eval_bool tid rho cond) as [branch|] eqn:Hcond; try discriminate.
    destruct branch.
    + inversion Hrun; subst. now apply MS.StepIfTrue.
    + inversion Hrun; subst. now apply MS.StepIfFalse.
  - inversion Hrun; subst. apply MS.StepSeq.
  - destruct (Z.leb bound 0) eqn:Hbound.
    + inversion Hrun; subst. apply MS.StepForZero. now apply Z.leb_le.
    + inversion Hrun; subst. apply MS.StepForUnfold. now apply Z.leb_gt.
Qed.

Lemma step_fun_complete : forall tid c oev c',
  MS.step tid c oev c' -> step_fun tid c = Some (oev, c').
Proof.
  intros tid c oev c' Hstep.
  inversion Hstep; subst; cbn.
  - now rewrite H.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - now rewrite H, H0.
  - reflexivity.
  - now rewrite H.
  - now rewrite H.
  - reflexivity.
  - destruct (Z.leb bound 0) eqn:Hleb; [reflexivity|].
    apply Z.leb_gt in Hleb. lia.
  - destruct (Z.leb bound 0) eqn:Hleb; [|reflexivity].
    apply Z.leb_le in Hleb. lia.
Qed.

Fixpoint run (tid fuel : nat) (c : MS.cfg) : list M.event_mir * MS.cfg :=
  match fuel with
  | O => ([], c)
  | S n =>
      match step_fun tid c with
      | None => ([], c)
      | Some (oev, c') =>
          let '(evs, c'') := run tid n c' in
          match oev with
          | None => (evs, c'')
          | Some ev => (ev :: evs, c'')
          end
      end
  end.

End MIRRun.
