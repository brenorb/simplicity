(** Allocation and permission effects of the original eight-store split.
    This applies to every completed call, independently of arithmetic values. *)
From Coq Require Import ZArith List.
From compcert Require Import AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Opaque secp_ge.
Set Default Timeout 10.

Theorem scalar_split128_permissions m mf args result :
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_split_128) args E0 mf result ->
 Mem.nextblock mf=Mem.nextblock m /\
 forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p.
Proof.
 intro Call;inversion Call;subst.
 match goal with Entry:function_entry2 _ _ _ _ _ _ _ |- _ => inversion Entry;subst;clear Entry end.
 match goal with Alloc:alloc_variables _ _ _ (fn_vars f_secp256k1_scalar_split_128) _ _ |- _ =>
  cbn [fn_vars f_secp256k1_scalar_split_128] in Alloc;inversion Alloc;subst;clear Alloc end.
 match goal with Body:exec_stmt function_entry2 secp_ge _ _ _
  (fn_body f_secp256k1_scalar_split_128) _ _ _ _ |- _ =>
  cbn [fn_body f_secp256k1_scalar_split_128] in Body end.
 repeat match goal with
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Ssequence _ _) _ _ _ _ |- _ => inversion H;subst;clear H;try contradiction
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Sset _ _) _ _ _ _ |- _ => inversion H;subst;clear H;try contradiction
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Sassign _ _) _ _ _ _ |- _ => inversion H;subst;clear H;try contradiction
 | H:eval_lvalue _ _ _ _ (Ederef _ _) _ _ _ |- _ => inversion H;subst;clear H
 | H:assign_loc _ _ _ _ _ Full _ _ |- _ => inversion H;subst;clear H;try discriminate
 end;try contradiction;try discriminate.
 all:match goal with Free:Mem.free_list _ (blocks_of_env _ empty_env)=_ |- _ =>
  cbn [blocks_of_env empty_env] in Free;inversion Free;subst;clear Free end.
 all:cbn [Mem.storev] in *.
 all:split.
 all:try solve [repeat match goal with Store:Mem.store _ _ _ _ _=Some ?mm |- context [Mem.nextblock ?mm] =>
  rewrite (Mem.nextblock_store _ _ _ _ _ _ Store) end;reflexivity].
 all:intros b pos k p;split;intro Perm.
 all:first [solve [repeat first [assumption |
  match goal with Store:Mem.store _ ?ma _ _ _=Some _ |- Mem.perm ?ma _ _ _ _ =>
   eapply Mem.perm_store_2;[exact Store|] end]] |
  solve [repeat first [assumption |
  match goal with Store:Mem.store _ _ _ _ _=Some ?mb |- Mem.perm ?mb _ _ _ _ =>
   eapply Mem.perm_store_1;[exact Store|] end]]].
Qed.
