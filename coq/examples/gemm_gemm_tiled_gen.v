From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Gemm_gemm_tiled_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_40") [] [];
    M.SIf (M.EVar "_126") [ M.SIf (M.EVar "_127") [ M.SLoad "_136" (M.EVar "_128") M.TyF32;
      M.SStore (M.EVar "_128") (M.EAdd (M.EVar "_133") (M.EVar "_135")) M.TyF32 ] [] ] [] ].

End Gemm_gemm_tiled_gen.
