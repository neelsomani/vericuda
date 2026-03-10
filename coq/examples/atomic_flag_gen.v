From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Atomic_flag_gen.

Definition prog : list M.stmt :=
  [ M.SAtomicLoadAcquire "_4" (M.EVar "_3") M.TyU32;
    M.SStore (M.EVar "_2") (M.EVar "_4") M.TyU32;
    M.SAtomicStoreRelease (M.EVar "_3") (M.EVal (M.VU32 1)) M.TyU32 ].

End Atomic_flag_gen.
