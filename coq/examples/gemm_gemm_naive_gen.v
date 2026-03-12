From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Gemm_gemm_naive_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_22" (M.EMul (M.EVar "_20") (M.EVar "_21"));
    M.SAssign "_19" (M.EVar "_22");
    M.SAssign "_24" (M.EAdd (M.EVar "_19") (M.EVar "_23"));
    M.SAssign "_18" (M.EVar "_24");
    M.SAssign "_17" (M.EVar "_18");
    M.SAssign "_30" (M.EMul (M.EVar "_28") (M.EVar "_29"));
    M.SAssign "_27" (M.EVar "_30");
    M.SAssign "_32" (M.EAdd (M.EVar "_27") (M.EVar "_31"));
    M.SAssign "_26" (M.EVar "_32");
    M.SAssign "_25" (M.EVar "_26");
    M.SAssign "_33" (M.ELt (M.EVar "_17") (M.EVar "_4"));
    M.SIf (M.EVar "_33") [ M.SAssign "_34" (M.ELt (M.EVar "_25") (M.EVar "_5"));
      M.SIf (M.EVar "_34") [ M.SAssign "_35" (M.EVal (M.VF32 0));
      M.SAssign "_36" (M.EVar "_37");
      M.SAssign "_38" (M.EVar "_36");
      M.SAssign "_40" (M.EVar "_38");
      M.SAssign "_39" (M.EVar "_40");
      M.SAssign "_41" (M.EVar "_39");
      M.SWhile (M.EVar "_41") [ M.SAssign "_42" (M.EVar "_39");
      M.SAssign "_47" (M.EMul (M.EVar "_17") (M.EVar "_6"));
      M.SAssign "_46" (M.EVar "_47");
      M.SAssign "_48" (M.EAdd (M.EVar "_46") (M.EVar "_42"));
      M.SAssign "_45" (M.EVar "_48");
      M.SAssign "_50" (M.ELt (M.EVar "_45") (M.EVar "_49"));
      M.SLoad "_44" (M.EVar "_1") M.TyF32;
      M.SAssign "_54" (M.EMul (M.EVar "_42") (M.EVar "_5"));
      M.SAssign "_53" (M.EVar "_54");
      M.SAssign "_55" (M.EAdd (M.EVar "_53") (M.EVar "_25"));
      M.SAssign "_52" (M.EVar "_55");
      M.SAssign "_57" (M.ELt (M.EVar "_52") (M.EVar "_56"));
      M.SLoad "_51" (M.EVar "_2") M.TyF32;
      M.SAssign "_43" (M.EMul (M.EVar "_44") (M.EVar "_51"));
      M.SAssign "_35" (M.EAdd (M.EVar "_35") (M.EVar "_43"));
      M.SAssign "_40" (M.EVar "_38");
      M.SAssign "_39" (M.EVar "_40") ];
      M.SAssign "_62" (M.EMul (M.EVar "_17") (M.EVar "_5"));
      M.SAssign "_61" (M.EVar "_62");
      M.SAssign "_63" (M.EAdd (M.EVar "_61") (M.EVar "_25"));
      M.SAssign "_60" (M.EVar "_63");
      M.SAssign "_59" (M.EPtrAdd (M.EVar "_3") (M.EVar "_60"));
      M.SAssign "_68" (M.EVar "_59");
      M.SAssign "_69" (M.EVar "_68");
      M.SAssign "_70" (M.EEq (M.EVar "_69") (M.EVal (M.VU64 0)));
      M.SAssign "_71" (M.EAnd (M.EVar "_70") (M.EVal (M.VBool true)));
      M.SAssign "_72" (M.ENot (M.EVar "_71"));
      M.SAssign "_58" (M.EVar "_59");
      M.SAssign "_65" (M.EVar "_35");
      M.SAssign "_64" (M.EMul (M.EVar "_7") (M.EVar "_65"));
      M.SLoad "_67" (M.EVar "_59") M.TyF32;
      M.SAssign "_66" (M.EMul (M.EVar "_8") (M.EVar "_67"));
      M.SStore (M.EVar "_59") (M.EAdd (M.EVar "_64") (M.EVar "_66")) M.TyF32 ] [] ] [] ].

End Gemm_gemm_naive_gen.
