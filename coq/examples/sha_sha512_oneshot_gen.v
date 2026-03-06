From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Sha_sha512_oneshot_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_5" (M.EVar "_6");
    M.SIf (M.EVar "_5") [] [];
    M.SAssign "_13" (M.EVar "_2");
    M.SAssign "_14" (M.EVar "_13");
    M.SAssign "_10" (M.EVar "_8") ].

End Sha_sha512_oneshot_gen.
