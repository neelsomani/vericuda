From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Gemm_gemm_tiled_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_9" (M.EVal (M.VBool true));
    M.SAssign "_10" (M.EVal (M.VBool true));
    M.SAssign "_11" (M.EVal (M.VBool true));
    M.SAssign "_12" (M.EVal (M.VBool true));
    M.SAssign "_13" (M.EVal (M.VBool true));
    M.SAssign "_14" (M.EVal (M.VBool true));
    M.SAssign "_15" (M.EVal (M.VBool true));
    M.SAssign "_16" (M.EVal (M.VBool true));
    M.SAssign "_18" (M.EVar "CUDA_thread_idx_x");
    M.SAssign "_17" (M.EVar "_18");
    M.SAssign "_20" (M.EVar "CUDA_thread_idx_y");
    M.SAssign "_19" (M.EVar "_20");
    M.SAssign "_24" (M.EVar "CUDA_block_idx_x");
    M.SAssign "_23" (M.EVar "_24");
    M.SAssign "_25" (M.EMul (M.EVar "_23") (M.EVal (MC.const_TILE_SIZE)));
    M.SAssign "_22" (M.EVar "_25");
    M.SAssign "_26" (M.EAdd (M.EVar "_22") (M.EVar "_19"));
    M.SAssign "_21" (M.EVar "_26");
    M.SAssign "_30" (M.EVar "CUDA_block_idx_y");
    M.SAssign "_29" (M.EVar "_30");
    M.SAssign "_31" (M.EMul (M.EVar "_29") (M.EVal (MC.const_TILE_SIZE)));
    M.SAssign "_28" (M.EVar "_31");
    M.SAssign "_32" (M.EAdd (M.EVar "_28") (M.EVar "_17"));
    M.SAssign "_27" (M.EVar "_32");
    M.SAssign "_33" (M.EVal (M.VF32 0));
    M.SAssign "_34" (M.EVar "_35");
    M.SAssign "_37" (M.EVar "_34");
    M.SAssign "_39" (M.EVar "_37");
    M.SAssign "_38" (M.EVar "_39");
    M.SAssign "_40" (M.EVar "_38");
    M.SWhile (M.EVar "_40") [ M.SAssign "_41" (M.EVar "_38");
      M.SAssign "_42" (M.ELt (M.EVar "_21") (M.EVar "_4")) ];
    M.SAssign "_126" (M.ELt (M.EVar "_21") (M.EVar "_4"));
    M.SIf (M.EVar "_126") [ M.SAssign "_127" (M.ELt (M.EVar "_27") (M.EVar "_5"));
      M.SIf (M.EVar "_127") [ M.SAssign "_131" (M.EMul (M.EVar "_21") (M.EVar "_5"));
      M.SAssign "_130" (M.EVar "_131");
      M.SAssign "_132" (M.EAdd (M.EVar "_130") (M.EVar "_27"));
      M.SAssign "_129" (M.EVar "_132");
      M.SAssign "_128" (M.EPtrAdd (M.EVar "_3") (M.EVar "_129"));
      M.SAssign "_134" (M.EVar "_33");
      M.SAssign "_133" (M.EMul (M.EVar "_7") (M.EVar "_134"));
      M.SAssign "_143" (M.EVar "_128");
      M.SAssign "_144" (M.EVar "_143");
      M.SAssign "_146" (M.ESub (M.EVar "_145") (M.EVal (M.VU64 1)));
      M.SAssign "_147" (M.EAnd (M.EVar "_144") (M.EVar "_146"));
      M.SAssign "_148" (M.EEq (M.EVar "_147") (M.EVal (M.VU64 0)));
      M.SAssign "_175" (M.EVar "_128");
      M.SAssign "_176" (M.EVar "_175");
      M.SAssign "_178" (M.ENot (M.EEq (M.EVar "_177") (M.EVal (M.VU64 0))));
      M.SAssign "_179" (M.EEq (M.EVar "_176") (M.EVal (M.VU64 0)));
      M.SAssign "_180" (M.EAnd (M.EVar "_179") (M.EVar "_178"));
      M.SAssign "_181" (M.ENot (M.EVar "_180"));
      M.SLoad "_136" (M.EPtrAdd (M.EVar "_3") (M.EVar "_129")) M.TyF32;
      M.SAssign "_135" (M.EMul (M.EVar "_8") (M.EVar "_136"));
      M.SAssign "_137" (M.EVar "_128");
      M.SAssign "_138" (M.EVar "_137");
      M.SAssign "_140" (M.ESub (M.EVar "_139") (M.EVal (M.VU64 1)));
      M.SAssign "_141" (M.EAnd (M.EVar "_138") (M.EVar "_140"));
      M.SAssign "_142" (M.EEq (M.EVar "_141") (M.EVal (M.VU64 0)));
      M.SAssign "_182" (M.EVar "_128");
      M.SAssign "_183" (M.EVar "_182");
      M.SAssign "_185" (M.ENot (M.EEq (M.EVar "_184") (M.EVal (M.VU64 0))));
      M.SAssign "_186" (M.EEq (M.EVar "_183") (M.EVal (M.VU64 0)));
      M.SAssign "_187" (M.EAnd (M.EVar "_186") (M.EVar "_185"));
      M.SAssign "_188" (M.ENot (M.EVar "_187"));
      M.SStore (M.EPtrAdd (M.EVar "_3") (M.EVar "_129")) (M.EAdd (M.EVar "_133") (M.EVar "_135")) M.TyF32 ] [] ] [] ].

End Gemm_gemm_tiled_gen.
