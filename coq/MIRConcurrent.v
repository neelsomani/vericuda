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

Record machine := {
  mach_threads : list thread;
  mach_mem     : MS.mem;
  mach_trace   : list (nat * M.event_mir)
}.

Definition mk_machine
    (threads : list thread) (memory : MS.mem)
    (trace : list (nat * M.event_mir)) : machine :=
  {| mach_threads := threads; mach_mem := memory; mach_trace := trace |}.

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
| MachineStep : forall before current after memory trace oev next,
    MS.step
      (MS.mk_cfg (th_code current) (th_env current) memory)
      oev next ->
    machine_step
      (mk_machine (before ++ current :: after) memory trace)
      (mk_machine
        (before ++
          mk_thread (th_id current) (MS.cfg_code next) (MS.cfg_env next) ::
          after)
        (MS.cfg_mem next)
        (append_event (th_id current) oev trace)).

(** Reflexive-transitive execution of the concurrent machine. *)
Inductive machine_steps : machine -> machine -> Prop :=
| MachineDone : forall m,
    machine_steps m m
| MachineMore : forall m m' m'',
    machine_step m m' ->
    machine_steps m' m'' ->
    machine_steps m m''.

End MIRConcurrent.
