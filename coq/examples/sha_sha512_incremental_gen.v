From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Sha_sha512_incremental_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_5" (M.EVar "_6");
    M.SIf (M.EVar "_5") [] [];
    M.SAssign "_11" (M.EVar "_7");
    M.SAssign "_17" (M.EVar "_2");
    M.SAssign "_18" (M.EVar "_17");
    M.SAssign "_19" (M.EEq (M.EVar "_18") (M.EVal (M.VU64 0)));
    M.SAssign "_20" (M.EAnd (M.EVar "_19") (M.EVal (M.VBool true)));
    M.SAssign "_21" (M.ENot (M.EVar "_20"));
    M.SAssign "_14" (M.EVar "_12") ].

End Sha_sha512_incremental_gen.
