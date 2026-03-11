From Coq Require Import ZArith List String.
Import ListNotations.
Require Import MIRSyntax MIRSemantics.

Module M := MIR.
Module MS := MIRSemantics.
Module MC := MIRConstants.

Module Sha_sha512_incremental_gen.

Definition prog : list M.stmt :=
  [ M.SAssign "_3" (M.EVar "sha512_incremental::assert_kernel_parameter_is_copy::<*mut [u8; 64]>()");
    M.SAssign "_4" (M.EVar "sha512_incremental::assert_kernel_parameter_is_copy::<&[u8]>()");
    M.SAssign "_6" (M.EVar "index_1d()");
    M.SAssign "_5" (M.EVar "_6");
    M.SIf (M.EVar "_5") [] [];
    M.SAssign "_7" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha512VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, OidSha512>> as Digest>::new()");
    M.SAssign "_9" (M.EVar "_7");
    M.SAssign "_8" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha512VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, OidSha512>> as Digest>::update::<&[u8]>(move _9, copy _1)");
    M.SAssign "_11" (M.EVar "_7");
    M.SAssign "_10" (M.EVar "<CoreWrapper<CtVariableCoreWrapper<Sha512VarCore, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>, OidSha512>> as Digest>::finalize(move _11)");
    M.SAssign "_17" (M.EVar "_2");
    M.SAssign "_18" (M.EVar "_17");
    M.SAssign "_19" (M.EEq (M.EVar "_18") (M.EVal (M.VU64 0)));
    M.SAssign "_20" (M.EAnd (M.EVar "_19") (M.EVal (M.VBool true)));
    M.SAssign "_21" (M.ENot (M.EVar "_20"));
    M.SAssign "_12" (M.EVar "&mut (*_2)");
    M.SAssign "_14" (M.EVar "_12");
    M.SAssign "_16" (M.EVar "_10");
    M.SAssign "_15" (M.EVar "GenericArray::<u8, UInt<UInt<UInt<UInt<UInt<UInt<UInt<UTerm, B1>, B0>, B0>, B0>, B0>, B0>, B0>>::as_slice(move _16)");
    M.SAssign "_13" (M.EVar "core::slice::<impl [u8]>::copy_from_slice(move _14, copy _15)") ].

End Sha_sha512_incremental_gen.
