(** The original normalized-field zero accessor does not change memory. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_sx_state C.jet_sx_mem
 C.jet_secp_fe_nv C.jet_secp_field_zero C.jet_secp_curve_weak C.jet_secp_field_weak_tight
 C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Import ListNotations Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Lemma field_zero_memory m mf args v:
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero) args E0 mf v ->mf=m.
Proof.
 intro Call;inversion Call;subst.
 match goal with Entry:function_entry2 _ _ _ _ _ _ _ |- _=>inversion Entry;subst;clear Entry end.
 match goal with Alloc:alloc_variables _ _ _ (fn_vars f_secp256k1_fe_is_zero) _ _ |- _=>
  cbn [fn_vars f_secp256k1_fe_is_zero] in Alloc;inversion Alloc;subst;clear Alloc end.
 match goal with Body:exec_stmt function_entry2 secp_ge _ _ _ (fn_body f_secp256k1_fe_is_zero) _ _ _ _ |- _=>
  cbn [fn_body f_secp256k1_fe_is_zero] in Body end.
 repeat match goal with
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Ssequence _ _) _ _ _ _ |- _=>inversion H;subst;clear H
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Sset _ _) _ _ _ _ |- _=>inversion H;subst;clear H
 | H:exec_stmt function_entry2 secp_ge _ _ _ (Sreturn _) _ _ _ _ |- _=>inversion H;subst;clear H
 end;try contradiction.
 all:match goal with Free:Mem.free_list _ (blocks_of_env _ empty_env)=_ |- _=>
  cbn [blocks_of_env empty_env] in Free;inversion Free;reflexivity end.
Qed.
Definition field_words_or w:=Int64.or (Int64.or (Int64.or (Int64.or
 (w 0%nat) (w 1%nat)) (w 2%nat)) (w 3%nat)) (w 4%nat).
Theorem eval_field_zero_readonly w m b:
 fe_at m b 0 (words5 w) ->Mem.range_perm m b 0 40 Cur Freeable ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero) [Vptr b Ptrofs.zero] E0 m
 (Vint (if Int64.eq (field_words_or w) Int64.zero then Int.one else Int.zero)).
Proof.
 intros Field Free.
 assert (Initial:rep (weak_shift_words w) [(b,0)] local_write_initial_regs m).
 { apply curve_weak_initial_rep;[rewrite weak_shift_values;exact Field|exact Free]. }
 destruct (eval_field_zero_from_owned_region m [(b,0)] (weak_shift_words w) Initial)
 as (mf & Call & Final & Frame).
 change (Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero)
  [Vptr b Ptrofs.zero] E0 mf
  (Vint (if Int64.eq (field_words_or w) Int64.zero then Int.one else Int.zero))) in Call.
 pose proof (field_zero_memory m mf _ _ Call);subst mf;exact Call.
Qed.
Require Import C.jet_secp_zero_numeric C.jet_secp_multiply_finish_product.
Lemma field_words_or_zero w:
 Int64.eq (field_words_or w) Int64.zero=true ->radix_value w=0.
Proof.
 intro Zero;apply Int64.same_if_eq in Zero;unfold field_words_or in Zero.
 repeat rewrite int64_or_zero_iff in Zero.
 destruct Zero as [[[[Z0 Z1] Z2] Z3] Z4].
 unfold radix_value;rewrite Z0,Z1,Z2,Z3,Z4,Int64.unsigned_zero;ring.
Qed.
Theorem eval_field_nonzero_readonly w m b:
 fe_at m b 0 (words5 w) ->Mem.range_perm m b 0 40 Cur Freeable ->radix_value w<>0 ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_is_zero) [Vptr b Ptrofs.zero] E0 m (Vint Int.zero).
Proof.
 intros Field Free Nonzero;pose proof (eval_field_zero_readonly w m b Field Free) as Call.
 assert (NotZero:Int64.eq (field_words_or w) Int64.zero=false).
 { apply Bool.not_true_is_false;intro Zero;apply Nonzero;apply field_words_or_zero;exact Zero. }
 rewrite NotZero in Call;exact Call.
Qed.
