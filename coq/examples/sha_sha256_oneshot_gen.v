From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Sha_sha256_oneshot_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_3" (M.EVar "sha256_oneshot::assert_kernel_parameter_is_copy::<*mut [u8; 32]>()");
    M.SAssign "_4" (M.EVar "sha256_oneshot::assert_kernel_parameter_is_copy::<&[u8]>()");
    M.SAssign "_6" (M.EVar "index_1d()");
    M.SAssign "_5" (M.EVar "_6");
    M.SIf (M.EVar "_5") [] [];
    M.SAssign "_7" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha256VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, OidSha256>> as Digest>::digest::<&[u8]>(copy _1)");
    M.SAssign "_13" (M.EVar "_2");
    M.SAssign "_14" (M.EVar "_13");
    M.SAssign "_15" (M.EEq (M.EVar "_14") (M.EVal (M.VU64 0)));
    M.SAssign "_16" (M.EAnd (M.EVar "_15") (M.EVal (M.VBool true)));
    M.SAssign "_17" (M.ENot (M.EVar "_16"));
    M.SAssign "_8" (M.EVar "&mut (*_2)");
    M.SAssign "_10" (M.EVar "_8");
    M.SAssign "_12" (M.EVar "_7");
    M.SAssign "_11" (M.EVar "GenericArray::<u8, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>>::as_slice(move _12)");
    M.SAssign "_9" (M.EVar "core::slice::<impl [u8]>::copy_from_slice(move _10, copy _11)") ].

End Sha_sha256_oneshot_gen.
