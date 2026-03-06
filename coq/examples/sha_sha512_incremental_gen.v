From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Sha_sha512_incremental_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_5" (M.EVar "_6");
    M.SIf (M.EVar "_5") [] [];
    M.SAssign "_11" (M.EVar "_7");
    M.SAssign "_17" (M.EVar "_2");
    M.SAssign "_18" (M.EVar "_17");
    M.SAssign "_14" (M.EVar "_12") ].

End Sha_sha512_incremental_gen.
