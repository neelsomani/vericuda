From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Saxpy_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_5" (M.EVal (M.VI32 0));
    M.SAssign "_7" (M.EVar "_5");
    M.SAssign "_6" (M.ELt (M.EVar "_7") (M.EVar "_4"));
    M.SWhile (M.EVar "_6") [ M.SAssign "_9" (M.EVar "_5");
      M.SAssign "_8" (M.EVar "_9");
      M.SAssign "_11" (M.EPtrAdd (M.EVar "_2") (M.EVar "_8"));
      M.SLoad "_10" (M.EPtrAdd (M.EVar "_2") (M.EVar "_8")) M.TyF32;
      M.SAssign "_13" (M.EPtrAdd (M.EVar "_3") (M.EVar "_8"));
      M.SLoad "_12" (M.EPtrAdd (M.EVar "_3") (M.EVar "_8")) M.TyF32;
      M.SAssign "_14" (M.EMul (M.EVar "_1") (M.EVar "_10"));
      M.SAssign "_15" (M.EPtrAdd (M.EVar "_3") (M.EVar "_8"));
      M.SStore (M.EPtrAdd (M.EVar "_3") (M.EVar "_8")) (M.EAdd (M.EVar "_14") (M.EVar "_12")) M.TyF32;
      M.SAssign "_16" (M.EAdd (M.EVar "_5") (M.EVal (M.VI32 1)));
      M.SAssign "_5" (M.EVar "_16") ] ].

End Saxpy_gen.
