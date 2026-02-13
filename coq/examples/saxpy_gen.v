From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Saxpy_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_6") [] [];
    M.SLoad "_10" (M.EPtrAdd (M.EVar "_2") (M.EVar "_8")) M.TyF32;
    M.SLoad "_12" (M.EPtrAdd (M.EVar "_3") (M.EVar "_8")) M.TyF32;
    M.SStore (M.EPtrAdd (M.EVar "_3") (M.EVar "_8")) (M.EAdd (M.EVar "_14") (M.EVar "_12")) M.TyF32 ].

End Saxpy_gen.
