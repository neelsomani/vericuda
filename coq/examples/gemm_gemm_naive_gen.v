From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Gemm_gemm_naive_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_17" (M.EVar "_18");
    M.SAssign "_25" (M.EVar "_26");
    M.SIf (M.EVar "_33") [ M.SIf (M.EVar "_34") [ M.SAssign "_35" (M.EVal (M.VF32 0));
      M.SAssign "_38" (M.EVar "_36");
      M.SLoop [ M.SLoad "_44" (M.EVar "_1") M.TyF32;
      M.SLoad "_51" (M.EVar "_2") M.TyF32;
      M.SAssign "_43" (M.EMul (M.EVar "_44") (M.EVar "_51"));
      M.SAssign "_35" (M.EAdd (M.EVar "_35") (M.EVar "_43")) ];
      M.SAssign "_68" (M.EVar "_59");
      M.SAssign "_69" (M.EVar "_68");
      M.SAssign "_65" (M.EVar "_35");
      M.SAssign "_64" (M.EMul (M.EVar "_7") (M.EVar "_65"));
      M.SLoad "_67" (M.EVar "_58") M.TyF32;
      M.SAssign "_66" (M.EMul (M.EVar "_8") (M.EVar "_67"));
      M.SStore (M.EVar "_58") (M.EAdd (M.EVar "_64") (M.EVar "_66")) M.TyU32 ] [] ] [] ].

End Gemm_gemm_naive_gen.
