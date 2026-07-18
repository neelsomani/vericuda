From Coq Require Import List.

Import ListNotations.

Require Import MIRSyntax MIRSemantics.

Module MIRConcurrent.

Module M := MIR.
Module MS := MIRSemantics.

(** A thread owns code and an environment.  Memory is deliberately absent: it
    is shared by all threads in the enclosing machine. *)
Record thread := {
  th_id   : nat;
  th_code : list M.stmt;
  th_env  : MS.env
}.

Definition mk_thread (tid : nat) (code : list M.stmt) (rho : MS.env) : thread :=
  {| th_id := tid; th_code := code; th_env := rho |}.

(** A machine owns disjoint global and one-CTA shared address spaces.  Equal
    numeric addresses in the two memories do not alias; this record does not
    model multiple CTAs or shared-memory lifetime across launches. *)
Record machine := {
  mach_threads : list thread;
  mach_mem     : MS.mem;
  mach_shared  : MS.mem;
  mach_trace   : list (nat * M.event_mir)
}.

Definition mk_machine
    (threads : list thread) (memory shared : MS.mem)
    (trace : list (nat * M.event_mir)) : machine :=
  {| mach_threads := threads; mach_mem := memory;
     mach_shared := shared; mach_trace := trace |}.

Definition append_event
    (tid : nat) (oev : option M.event_mir)
    (trace : list (nat * M.event_mir)) : list (nat * M.event_mir) :=
  match oev with
  | None => trace
  | Some ev => trace ++ [(tid, ev)]
  end.

(** Lift one existing per-thread [MS.step] into a nondeterministic machine
    step.  Splitting the thread list as [before ++ current :: after] chooses an
    arbitrary runnable thread.  The selected step reads and updates the shared
    machine memory, while all other thread states are preserved. *)
Inductive machine_step : machine -> machine -> Prop :=
| MachineStep : forall before current after memory shared trace oev next,
    MS.step (th_id current)
      (MS.mk_cfg (th_code current) (th_env current) memory)
      oev next ->
    machine_step
      (mk_machine (before ++ current :: after) memory shared trace)
      (mk_machine
        (before ++
          mk_thread (th_id current) (MS.cfg_code next) (MS.cfg_env next) ::
          after)
        (MS.cfg_mem next)
        shared
        (append_event (th_id current) oev trace))
| MachineLoadShared :
    forall before current after memory shared trace
           rest dst ptr ty addr value,
      th_code current = M.SLoadShared dst ptr ty :: rest ->
      MS.eval_addr (th_id current) (th_env current) ptr = Some addr ->
      MS.mem_read shared addr = Some value ->
      machine_step
        (mk_machine (before ++ current :: after) memory shared trace)
        (mk_machine
          (before ++
            mk_thread (th_id current) rest
              (MS.env_set (th_env current) dst value) :: after)
          memory shared
          (trace ++ [(th_id current, M.EvLoadShared ty addr value)]))
| MachineStoreShared :
    forall before current after memory shared trace
           rest ptr rhs ty addr value,
      th_code current = M.SStoreShared ptr rhs ty :: rest ->
      MS.eval_addr (th_id current) (th_env current) ptr = Some addr ->
      MS.eval_expr (th_id current) (th_env current) rhs = Some value ->
      machine_step
        (mk_machine (before ++ current :: after) memory shared trace)
        (mk_machine
          (before ++ mk_thread (th_id current) rest (th_env current) :: after)
          memory (MS.mem_write shared addr value)
          (trace ++ [(th_id current, M.EvStoreShared ty addr value)]))
| MachineBarrierShared :
    forall before current after memory shared trace rest,
      th_code current = M.SBarrierShared :: rest ->
      machine_step
        (mk_machine (before ++ current :: after) memory shared trace)
        (mk_machine
          (before ++ mk_thread (th_id current) rest (th_env current) :: after)
          memory shared
          (trace ++ [(th_id current, M.EvBarrierShared)]))
.

(** Reflexive-transitive execution of the concurrent machine. *)
Inductive machine_steps : machine -> machine -> Prop :=
| MachineDone : forall m,
    machine_steps m m
| MachineMore : forall m m' m'',
    machine_step m m' ->
    machine_steps m' m'' ->
    machine_steps m m''.

End MIRConcurrent.
