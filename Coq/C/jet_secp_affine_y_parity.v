(** Original affine Y normalization and parity accessor, with exact literal
    field parity and preservation for the surrounding public jet caller. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_square_columns C.jet_secp_canonical_normalize
 C.jet_secp_canonical_odd C.jet_secp_rescale_literal C.jet_secp_affine_normalize_y C.jet_secp_affine_odd_y
 C.jet_secp_field_io_preserve C.jet_secp_frame_preserve C.jet_clight_internal_frame C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_odd rescale_field_output.

Lemma affine_output_parity w :
 Bit.toBool(@canonical_fe_is_odd Alg.CoreFunSem(rescale_field_output w))=
 Z.testbit(radix_value w mod feP)0.
Proof.
 rewrite canonical_fe_is_odd_numeric,canonical_fe_normalize_numeric,
  canonical_field_order_matches_limb_model,rescale_field_output_value,field_prime_matches_normalizer,
  Z.mod_mod by(unfold feP,feR;lia);reflexivity.
Qed.

Lemma affine_y_parity_helpers_closed :
 closed_stmtb field_io_helpers(fn_body f_secp256k1_fe_normalize_var)=true /\
 closed_stmtb field_io_helpers(fn_body f_secp256k1_fe_is_odd)=true.
Proof. vm_compute;split;reflexivity. Qed.

Lemma affine_y_normalizer_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_fe_normalize_var)args t mf result -> readonly_preserved m mf.
Proof.
 apply function_preserved_from_body;[|reflexivity].
 intros e le mi tr lef mo out Run Plain.
 exact(proj1(internal_exec_preserved _ _ field_io_helpers_ok)
  e le mi _ tr lef mo out Run Plain(proj1 affine_y_parity_helpers_closed)).
Qed.
Lemma affine_y_parity_preserved m args t mf result :
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_fe_is_odd)args t mf result -> readonly_preserved m mf.
Proof.
 apply function_preserved_from_body;[|reflexivity].
 intros e le mi tr lef mo out Run Plain.
 exact(proj1(internal_exec_preserved _ _ field_io_helpers_ok)
  e le mi _ tr lef mo out Run Plain(proj2 affine_y_parity_helpers_closed)).
Qed.

Theorem eval_affine_normalized_y_odd w m br : square_input_bounds w ->
 fe_at m br 40(words5 w) -> Mem.range_perm m br 0 88 Cur Freeable -> exists mn mf,
 Clight2.eval_funcall secp_ge m(Internal f_secp256k1_fe_normalize_var)
  [Vptr br(Ptrofs.repr 40)]E0 mn Vundef /\
 Clight2.eval_funcall secp_ge mn(Internal f_secp256k1_fe_is_odd)
  [Vptr br(Ptrofs.repr 40)]E0 mf
  (Vint(bit_int(Bit.toBool(@canonical_fe_is_odd Alg.CoreFunSem(rescale_field_output w))))) /\
 Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe(fun b pos=>b<>br \/ pos<40 \/ 80<=pos)m mf /\ readonly_preserved m mf.
Proof.
 intros Bounds Field Free.
 destruct(eval_affine_nv_y_words w m br Bounds Field Free) as(mn & Normalize & Canonical & FreeN & NormFrame).
 destruct(eval_affine_odd_y_value mn br(radix_value w mod feP)Canonical FreeN)
  as(mf & Odd & FieldF & FreeF & OddFrame).
 rewrite <-affine_output_parity in Odd.
 assert(Call:Clight2.eval_funcall secp_ge mn(Internal f_secp256k1_fe_is_odd)
  [Vptr br(Ptrofs.repr 40)]E0 mf
  (Vint(bit_int(Bit.toBool(@canonical_fe_is_odd Alg.CoreFunSem(rescale_field_output w)))))).
 { unfold bit_int;destruct(Bit.toBool(@canonical_fe_is_odd Alg.CoreFunSem(rescale_field_output w)));exact Odd. }
 exists mn,mf;split;[exact Normalize|];split;[exact Call|];split;[exact FreeF|];split.
 - eapply lframe_trans;[exact NormFrame|exact OddFrame].
 - eapply preserved_trans;[eapply affine_y_normalizer_preserved;exact Normalize|
    eapply affine_y_parity_preserved;exact Call].
Qed.
