From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Sha_sha256_incremental_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_7") [] [] ].

End Sha_sha256_incremental_gen.
