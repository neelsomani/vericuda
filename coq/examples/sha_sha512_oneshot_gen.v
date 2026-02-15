From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Sha_sha512_oneshot_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_5") [] [] ].

End Sha_sha512_oneshot_gen.
