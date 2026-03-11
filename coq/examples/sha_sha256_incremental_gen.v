From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Sha_sha256_incremental_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_4" (M.EVar "sha256_incremental::assert_kernel_parameter_is_copy::<*mut [u8; 32]>()");
    M.SAssign "_5" (M.EVar "sha256_incremental::assert_kernel_parameter_is_copy::<&[u8]>()");
    M.SAssign "_6" (M.EVar "sha256_incremental::assert_kernel_parameter_is_copy::<&[u8]>()");
    M.SAssign "_8" (M.EVar "index_1d()");
    M.SAssign "_7" (M.EVar "_8");
    M.SIf (M.EVar "_7") [] [];
    M.SAssign "_9" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha256VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, OidSha256>> as Digest>::new()");
    M.SAssign "_11" (M.EVar "_9");
    M.SAssign "_10" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha256VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, OidSha256>> as Digest>::update::<&[u8]>(move _11, copy _1)");
    M.SAssign "_13" (M.EVar "_9");
    M.SAssign "_12" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha256VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, OidSha256>> as Digest>::update::<&[u8]>(move _13, copy _2)");
    M.SAssign "_15" (M.EVar "_9");
    M.SAssign "_14" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha256VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, OidSha256>> as Digest>::finalize(move _15)");
    M.SAssign "_21" (M.EVar "_3");
    M.SAssign "_22" (M.EVar "_21");
    M.SAssign "_23" (M.EEq (M.EVar "_22") (M.EVal (M.VU64 0)));
    M.SAssign "_24" (M.EAnd (M.EVar "_23") (M.EVal (M.VBool true)));
    M.SAssign "_25" (M.ENot (M.EVar "_24"));
    M.SAssign "_16" (M.EVar "&mut (*_3)");
    M.SAssign "_18" (M.EVar "_16");
    M.SAssign "_20" (M.EVar "_14");
    M.SAssign "_19" (M.EVar "GenericArray::<u8, UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>>::as_slice(move _20)");
    M.SAssign "_17" (M.EVar "core::slice::<impl [u8]>::copy_from_slice(move _18, copy _19)") ].

End Sha_sha256_incremental_gen.
