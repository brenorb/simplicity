(** Reuse the existing three-allocation normalization setup. The parity
    caller names its affine local b instead of r; all allocations are real. *)
From Coq Require Import ZArith List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_gej_public_entry
 C.jet_secp_gej_norm_branch C.jet_secp_gej_norm_infinity.
Import ListNotations.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_odd_env bl bp br := PTree.set _b(br,Tstruct __6121 noattr)(gej_public_env bl bp).
Definition gej_odd_temps envv bd base bs sbase := PTree.set _env envv
 (PTree.set _src(Vptr bs(Ptrofs.repr sbase))(PTree.set _dst(Vptr bd(Ptrofs.repr base))
  (create_undef_temps(fn_temps f_simplicity_gej_y_is_odd)))).
Lemma gej_odd_temps_match envv bd base bs sbase :
 gej_odd_temps envv bd base bs sbase=gej_norm_temps envv bd base bs sbase.
Proof. reflexivity. Qed.

Lemma gej_odd_entry_from_normalize envv m mc bl bp br bd base bs sbase :
 function_entry2 secp_ge f_simplicity_gej_normalize
  [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);envv]m
  (gej_norm_env bl bp br)(gej_norm_temps envv bd base bs sbase)mc ->
 function_entry2 secp_ge f_simplicity_gej_y_is_odd
  [Vptr bd(Ptrofs.repr base);Vptr bs(Ptrofs.repr sbase);envv]m
  (gej_odd_env bl bp br)(gej_odd_temps envv bd base bs sbase)mc.
Proof.
 intro Entry;inversion Entry;subst.
 repeat match goal with H:alloc_variables _ _ _ _ _ _ |- _=>inversion H;subst;clear H end.
 assert(Ok:fn_okb f_simplicity_gej_y_is_odd=true) by reflexivity.
 destruct(fn_okb_true _ Ok) as(N1 & N2 & Disjoint).
 constructor;[exact N1|exact N2|exact Disjoint| |reflexivity].
 eapply alloc_variables_cons;[eassumption|].
 eapply alloc_variables_cons;[eassumption|].
 eapply alloc_variables_cons;[eassumption|constructor].
Qed.

Lemma gej_odd_copy_from_normalize le mc md bl bp br :
 Clight2.exec_stmt secp_ge(gej_norm_env bl bp br)le mc
  (Sassign(Evar _src(Tstruct _frameItem noattr))(Etempvar _src(Tstruct _frameItem noattr)))E0 le md Out_normal ->
 Clight2.exec_stmt secp_ge(gej_odd_env bl bp br)le mc
  (Sassign(Evar _src(Tstruct _frameItem noattr))(Etempvar _src(Tstruct _frameItem noattr)))E0 le md Out_normal.
Proof.
 intro Copy.
 assert(Lookup:(gej_norm_env bl bp br)!_src=Some(bl,Tstruct _frameItem noattr)) by reflexivity.
 inversion Copy;subst.
 match goal with H:eval_lvalue _ _ _ _ (Evar _ _) _ _ _ |- _=>inversion H;subst end.
 - match goal with H:(gej_norm_env bl bp br)!_src=Some _ |- _=>rewrite Lookup in H;injection H as <- end.
   eapply exec_Sassign with(v2:=v2)(v:=v).
   + apply eval_Evar_local;reflexivity.
   + match goal with H:eval_expr _ _ _ _ (Etempvar _ _) _ |- _=>inversion H;subst end.
     * apply eval_Etempvar;assumption.
     * match goal with H:eval_lvalue _ _ _ _ (Etempvar _ _) _ _ _ |- _=>inversion H end.
   + eassumption.
   + eassumption.
 - match goal with H:(gej_norm_env bl bp br)!_src=None |- _=>rewrite Lookup in H;discriminate H end.
Qed.

Lemma gej_odd_blocks bl bp br : blocks_of_env secp_ge(gej_odd_env bl bp br)=
 [(bl,0,16);(bp,0,128);(br,0,88)].
Proof. reflexivity. Qed.
