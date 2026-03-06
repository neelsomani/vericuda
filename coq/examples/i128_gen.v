From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module I128_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_29" (M.EVar "_30");
    M.SIf (M.EVar "_31") [] [];
    M.SIf (M.EVar "_33") [] [];
    M.SLoad "_35" (M.EVar "_1") M.TyU32;
    M.SLoad "_38" (M.EVar "_2") M.TyU32;
    M.SAssign "_41" (M.EVar "_42");
    M.SAssign "_43" (M.EVar "_35");
    M.SAssign "_44" (M.EVar "_38");
    M.SAssign "_141" (M.EVar "_46");
    M.SAssign "_142" (M.EVar "_141");
    M.SAssign "_147" (M.EVar "_46");
    M.SAssign "_148" (M.EVar "_147");
    M.SStore (M.EVar "_46") (M.EVar "_45") M.TyU32;
    M.SAssign "_135" (M.EVar "_48");
    M.SAssign "_136" (M.EVar "_135");
    M.SAssign "_154" (M.EVar "_48");
    M.SAssign "_155" (M.EVar "_154");
    M.SStore (M.EVar "_48") (M.EVar "_47") M.TyU32;
    M.SAssign "_129" (M.EVar "_50");
    M.SAssign "_130" (M.EVar "_129");
    M.SAssign "_161" (M.EVar "_50");
    M.SAssign "_162" (M.EVar "_161");
    M.SStore (M.EVar "_50") (M.EVar "_49") M.TyU32;
    M.SAssign "_123" (M.EVar "_51");
    M.SAssign "_124" (M.EVar "_123");
    M.SAssign "_168" (M.EVar "_51");
    M.SAssign "_169" (M.EVar "_168");
    M.SStore (M.EVar "_51") (M.EVar "BitAnd(copy _35, copy _38)") M.TyU32;
    M.SAssign "_117" (M.EVar "_52");
    M.SAssign "_118" (M.EVar "_117");
    M.SAssign "_175" (M.EVar "_52");
    M.SAssign "_176" (M.EVar "_175");
    M.SStore (M.EVar "_52") (M.EVar "BitXor(copy _35, copy _38)") M.TyU32;
    M.SAssign "_111" (M.EVar "_54");
    M.SAssign "_112" (M.EVar "_111");
    M.SAssign "_182" (M.EVar "_54");
    M.SAssign "_183" (M.EVar "_182");
    M.SStore (M.EVar "_54") (M.EVar "_53") M.TyU32;
    M.SAssign "_105" (M.EVar "_56");
    M.SAssign "_106" (M.EVar "_105");
    M.SAssign "_189" (M.EVar "_56");
    M.SAssign "_190" (M.EVar "_189");
    M.SStore (M.EVar "_56") (M.EVar "_55") M.TyU32;
    M.SAssign "_99" (M.EVar "_58");
    M.SAssign "_100" (M.EVar "_99");
    M.SAssign "_196" (M.EVar "_58");
    M.SAssign "_197" (M.EVar "_196");
    M.SStore (M.EVar "_58") (M.EVar "_57") M.TyU32;
    M.SAssign "_93" (M.EVar "_60");
    M.SAssign "_94" (M.EVar "_93");
    M.SAssign "_203" (M.EVar "_60");
    M.SAssign "_204" (M.EVar "_203");
    M.SStore (M.EVar "_60") (M.EVar "Div(copy _35, copy _38)") M.TyU32;
    M.SAssign "_87" (M.EVar "_66");
    M.SAssign "_88" (M.EVar "_87");
    M.SAssign "_210" (M.EVar "_66");
    M.SAssign "_211" (M.EVar "_210");
    M.SStore (M.EVar "_66") (M.EVar "_61") M.TyU32;
    M.SAssign "_81" (M.EVar "_68");
    M.SAssign "_82" (M.EVar "_81");
    M.SAssign "_217" (M.EVar "_68");
    M.SAssign "_218" (M.EVar "_217");
    M.SStore (M.EVar "_68") (M.EVar "Rem(copy _35, copy _38)") M.TyU32;
    M.SAssign "_75" (M.EVar "_74");
    M.SAssign "_76" (M.EVar "_75");
    M.SAssign "_224" (M.EVar "_74");
    M.SAssign "_225" (M.EVar "_224");
    M.SStore (M.EVar "_74") (M.EVar "_69") M.TyU32 ].

End I128_gen.
