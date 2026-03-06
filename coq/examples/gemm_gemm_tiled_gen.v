From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Gemm_gemm_tiled_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_17" (M.EVar "_18");
    M.SAssign "_19" (M.EVar "_20");
    M.SAssign "_23" (M.EVar "_24");
    M.SAssign "_29" (M.EVar "_30");
    M.SAssign "_33" (M.EVal (M.VF32 0));
    M.SAssign "_37" (M.EVar "_34");
    M.SLoop [];
    M.SIf (M.EVar "_126") [ M.SIf (M.EVar "_127") [ M.SAssign "_134" (M.EVar "_33");
      M.SAssign "_133" (M.EMul (M.EVar "_7") (M.EVar "_134"));
      M.SAssign "_143" (M.EVar "_128");
      M.SAssign "_144" (M.EVar "_143");
      M.SAssign "_175" (M.EVar "_128");
      M.SAssign "_176" (M.EVar "_175");
      M.SLoad "_136" (M.EVar "_128") M.TyF32;
      M.SAssign "_135" (M.EMul (M.EVar "_8") (M.EVar "_136"));
      M.SAssign "_137" (M.EVar "_128");
      M.SAssign "_138" (M.EVar "_137");
      M.SAssign "_182" (M.EVar "_128");
      M.SAssign "_183" (M.EVar "_182");
      M.SStore (M.EVar "_128") (M.EAdd (M.EVar "_133") (M.EVar "_135")) M.TyF32 ] [] ] [] ].

End Gemm_gemm_tiled_gen.
