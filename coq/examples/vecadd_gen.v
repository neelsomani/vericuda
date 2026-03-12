From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Vecadd_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_7" (M.EVar "_8");
    M.SAssign "_9" (M.ELt (M.EVar "_7") (M.EVar "_10"));
    M.SIf (M.EVar "_9") [ M.SAssign "_12" (M.EPtrAdd (M.EVar "_3") (M.EVar "_7"));
      M.SAssign "_19" (M.EVar "_12");
      M.SAssign "_20" (M.EVar "_19");
      M.SAssign "_21" (M.EEq (M.EVar "_20") (M.EVal (M.VU64 0)));
      M.SAssign "_22" (M.EAnd (M.EVar "_21") (M.EVal (M.VBool true)));
      M.SAssign "_23" (M.ENot (M.EVar "_22"));
      M.SAssign "_11" (M.EVar "_12");
      M.SAssign "_15" (M.ELt (M.EVar "_7") (M.EVar "_14"));
      M.SLoad "_13" (M.EVar "_1") M.TyF32;
      M.SAssign "_18" (M.ELt (M.EVar "_7") (M.EVar "_17"));
      M.SLoad "_16" (M.EVar "_2") M.TyF32;
      M.SStore (M.EVar "_12") (M.EAdd (M.EVar "_13") (M.EVar "_16")) M.TyF32 ] [] ].

End Vecadd_gen.
