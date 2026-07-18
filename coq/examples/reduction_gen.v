From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.

Module Reduction_gen.

Definition prog : list M.stmt :=
  [ M.SStoreShared (M.EPtrAdd (M.EVar "_1") (M.EVar "_6")) (M.EVar "_3") M.TyF32;
    M.SBarrierShared;
    M.SFor "_loop_counter" 3 [ M.SLoadShared "_18" (M.EPtrAdd (M.EVar "_1") (M.EVar "_20")) M.TyF32;
        M.SLoadShared "_21" (M.EPtrAdd (M.EVar "_1") (M.EVar "_23")) M.TyF32;
        M.SStoreShared (M.EPtrAdd (M.EVar "_1") (M.EVar "_27")) (M.EAdd (M.EVar "_18") (M.EVar "_21")) M.TyF32;
        M.SBarrierShared ] ].

End Reduction_gen.
