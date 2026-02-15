From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module I128_gen.

Definition prog : list M.stmt :=
  [ M.SIf (M.EVar "_31") [] [];
    M.SIf (M.EVar "_33") [] [];
    M.SLoad "_35" (M.EVar "_1") M.TyU32;
    M.SLoad "_38" (M.EVar "_2") M.TyU32;
    M.SStore (M.EVar "_46") (M.EVar "_45") M.TyU32;
    M.SStore (M.EVar "_48") (M.EVar "_47") M.TyU32;
    M.SStore (M.EVar "_50") (M.EVar "_49") M.TyU32;
    M.SStore (M.EVar "_51") (M.EVar "BitAnd(copy _35, copy _38)") M.TyU32;
    M.SStore (M.EVar "_52") (M.EVar "BitXor(copy _35, copy _38)") M.TyU32;
    M.SStore (M.EVar "_54") (M.EVar "_53") M.TyU32;
    M.SStore (M.EVar "_56") (M.EVar "_55") M.TyU32;
    M.SStore (M.EVar "_58") (M.EVar "_57") M.TyU32;
    M.SStore (M.EVar "_60") (M.EVar "Div(copy _35, copy _38)") M.TyU32;
    M.SStore (M.EVar "_66") (M.EVar "_61") M.TyU32;
    M.SStore (M.EVar "_68") (M.EVar "Rem(copy _35, copy _38)") M.TyU32;
    M.SStore (M.EVar "_74") (M.EVar "_69") M.TyU32 ].

End I128_gen.
