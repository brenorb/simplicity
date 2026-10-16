(** Actual original scalar-square public read/multiply/write/return AST. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers Values Maps Memory Events Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_wrapper_run.
Require Import C.jet_frame_layout C.jet_frame_inv C.jet_input_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_secp_public_body.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_secp_scalar_public_entry C.jet_secp_scalar_public_calls.
Require Import C.jet_secp_scalar_normalize_rest.
Require Import C.jet_secp_scalar_lambda_global C.jet_secp_canonical_scalar_lambda
  C.jet_secp_scalar_lambda_call_chain C.jet_clight_readonly_frame.
Import ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition scalar_lambda_inplace_stmt :=
  match fn_body f_simplicity_scalar_multiply_lambda with
  | Ssequence _ (Ssequence _ (Ssequence multiply _)) => multiply | _ => Sskip end.
Definition scalar_lambda_rest :=
  match fn_body f_simplicity_scalar_multiply_lambda with Ssequence _ rest => rest | _ => Sskip end.
Lemma scalar_lambda_rest_eq :
  scalar_lambda_rest = Ssequence scalar_public_read_stmt
    (Ssequence scalar_lambda_inplace_stmt
      (Ssequence scalar_normalize_write_stmt (Sreturn (Some (Econst_int (Int.repr 1) tint))))).
Proof. reflexivity. Qed.
Lemma scalar_lambda_symbols :
  Genv.find_symbol secp_ge _secp256k1_scalar_mul = Some (secp_symbol_block _secp256k1_scalar_mul) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block _secp256k1_scalar_mul) Ptrofs.zero) =
    Some (Internal f_secp256k1_scalar_mul).
Proof. vm_compute; split; reflexivity. Qed.
Local Opaque secp_ge canonical_scalar_multiply_lambda encode.

Lemma exec_scalar_lambda_inplace le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_scalar_mul)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr scalar_lambda_block Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m scalar_lambda_inplace_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct scalar_lambda_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block _secp256k1_scalar_mul) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr scalar_lambda_block Ptrofs.zero])
    (f := Internal f_secp256k1_scalar_mul) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_Eaddrof; eapply eval_Evar_global; [reflexivity|exact scalar_lambda_global_symbol].
        -- reflexivity.
        -- apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Theorem exec_scalar_lambda_rest_canonical le m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) m ba bl :
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 32 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba, 0); (bl, 0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  scalar_lambda_global_rep m0 -> scalar_lambda_global_rep m ->
  readonly_region_bounds m scalar_lambda_block 0 32 ->
  scalar_lambda_block <> ba -> scalar_lambda_block <> bl ->
  exists mf,
    Clight2.exec_stmt secp_ge (scalar_public_env bl ba) le m scalar_lambda_rest E0 le mf
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@canonical_scalar_multiply_lambda Alg.CoreFunSem value)) /\
    Mem.range_perm mf ba 0 32 Cur Freeable /\ Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mf.
Proof.
  intros HD HO HI Hrc HM HA HL HS HSeparate HSep HInv HG0 HG HB HNotA HNotL.
  destruct (eval_scalar_read_lambda_write_canonical m0 bd dbase bw outedge cursor N bi edge rc
    value m ba bl HO HI Hrc HM HA HL HS HSeparate HSep HInv HG0 HG HB HNotA HNotL)
    as (mr & mn & mf & HRead & HNeg & HWrite & HFinal & HFreeA & HCursor & HFreeL & HFrame).
  exists mf; split.
  - rewrite scalar_lambda_rest_eq.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + apply exec_scalar_public_read; exact HRead.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * apply exec_scalar_lambda_inplace; exact HNeg.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
        -- eapply exec_scalar_normalize_write; [exact HD|exact HWrite].
        -- apply exec_Sreturn_some; constructor.
  - split; [exact HFinal|]; split; [exact HFreeA|]; split; assumption.
Qed.
