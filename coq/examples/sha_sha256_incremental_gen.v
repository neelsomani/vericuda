From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Sha_sha256_incremental_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_7" (M.EVar "_8");
    M.SIf (M.EVar "_7") [] [];
    M.SAssign "_15" (M.EVar "_9");
    M.SAssign "_21" (M.EVar "_3");
    M.SAssign "_22" (M.EVar "_21");
    M.SAssign "_23" (M.EEq (M.EVar "_22") (M.EVal (M.VU64 0)));
    M.SAssign "_24" (M.EAnd (M.EVar "_23") (M.EVal (M.VBool true)));
    M.SAssign "_25" (M.ENot (M.EVar "_24"));
    M.SAssign "_18" (M.EVar "_16") ].

End Sha_sha256_incremental_gen.
