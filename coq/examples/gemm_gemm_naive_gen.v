From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Gemm_gemm_naive_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_33") [ M.SIf (M.EVar "_34") [ M.SLoop [ M.SLoad "_44" (M.EVar "_1") M.TyF32;
      M.SLoad "_51" (M.EVar "_2") M.TyF32 ];
      M.SLoad "_67" (M.EVar "_58") M.TyF32;
      M.SStore (M.EVar "_58") (M.EAdd (M.EVar "_64") (M.EVar "_66")) M.TyU32 ] [] ] [] ].

End Gemm_gemm_naive_gen.
