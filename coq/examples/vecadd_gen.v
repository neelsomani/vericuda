From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Vecadd_gen.

Definition prog : list M.stmt :=
  [ M.SLoad "_9" (M.EVar "_1") M.TyF32;
    M.SLoad "_12" (M.EVar "_2") M.TyF32;
    M.SStore (M.EVar "_7") (M.EAdd (M.EVar "_9") (M.EVar "_12")) M.TyU32 ].

End Vecadd_gen.
