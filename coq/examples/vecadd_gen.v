From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Vecadd_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_4" (M.EVar "assert_kernel_parameter_is_copy::<*mut f32>()");
    M.SAssign "_5" (M.EVar "assert_kernel_parameter_is_copy::<&[f32]>()");
    M.SAssign "_6" (M.EVar "assert_kernel_parameter_is_copy::<&[f32]>()");
    M.SAssign "_8" (M.EVar "index_1d()");
    M.SAssign "_7" (M.EVar "_8");
    M.SAssign "_10" (M.EVar "PtrMetadata(copy _1)");
    M.SAssign "_9" (M.ELt (M.EVar "_7") (M.EVar "_10"));
    M.SIf (M.EVar "_9") [ M.SAssign "_12" (M.EVar "std::ptr::mut_ptr::<impl *mut f32>::add(copy _3, copy _7)");
      M.SAssign "_19" (M.EVar "_12");
      M.SAssign "_20" (M.EVar "_19");
      M.SAssign "_21" (M.EEq (M.EVar "_20") (M.EVal (M.VU64 0)));
      M.SAssign "_22" (M.EAnd (M.EVar "_21") (M.EVal (M.VBool true)));
      M.SAssign "_23" (M.ENot (M.EVar "_22"));
      M.SAssign "_11" (M.EVar "&mut (*_12)");
      M.SAssign "_14" (M.EVar "PtrMetadata(copy _1)");
      M.SAssign "_15" (M.ELt (M.EVar "_7") (M.EVar "_14"));
      M.SLoad "_13" (M.EVar "_1") M.TyF32;
      M.SAssign "_17" (M.EVar "PtrMetadata(copy _2)");
      M.SAssign "_18" (M.ELt (M.EVar "_7") (M.EVar "_17"));
      M.SLoad "_16" (M.EVar "_2") M.TyF32;
      M.SStore (M.EVar "_11") (M.EAdd (M.EVar "_13") (M.EVar "_16")) M.TyU32 ] [] ].

End Vecadd_gen.
