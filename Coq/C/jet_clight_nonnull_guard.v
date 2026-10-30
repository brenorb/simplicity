(** Pointer-check statement shared by original C jet helper wrappers. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition nonnull_return_zero id ty:=Sloop
 (Sifthenelse (Eunop Onotbool (Ebinop One (Etempvar id (tptr ty))
  (Ecast (Econst_int Int.zero tint) (tptr tvoid)) tint) tint)
  (Sreturn (Some (Econst_int Int.zero tint))) Sskip) Sbreak.
Theorem exec_nonnull_return_zero ge e le m id ty b ofs:
 le!id=Some (Vptr b ofs) ->Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs)=true ->
 Clight2.exec_stmt ge e le m (nonnull_return_zero id ty) E0 le m Out_normal.
Proof.
 intros Pointer Valid;unfold nonnull_return_zero.
 change E0 with (E0**E0);eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break).
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Eunop with (v1:=Vint Int.one);[|reflexivity].
   eapply eval_Ebinop with (v1:=Vptr b ofs) (v2:=Vlong Int64.zero).
   + apply eval_Etempvar;exact Pointer.
   + eapply eval_Ecast;[constructor|reflexivity].
   + change (option_map Val.of_bool
    (if Mem.weak_valid_pointer m b (Ptrofs.unsigned ofs) then Some true else None)=Some (Vint Int.one)).
     rewrite Valid;reflexivity.
 - constructor.
 - constructor.
 - constructor.
Qed.
