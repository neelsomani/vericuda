From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Vecadd_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_9") [ M.SLoad "_13" (M.EVar "_1") M.TyF32;
      M.SLoad "_16" (M.EVar "_2") M.TyF32;
      M.SStore (M.EVar "_11") (M.EAdd (M.EVar "_13") (M.EVar "_16")) M.TyU32 ] [] ].

End Vecadd_gen.
