(** Derive negation's initial facts from the actual normalized reader output. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_math C.jet_secp_fe_nv C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_local_regions C.jet_secp_local_call C.jet_secp_b32_exec.
Require Import C.jet_secp_write_fe_numeric C.jet_secp_wrapper_run.
Require Import C.jet_input_layout C.jet_encoding C.jet_output_layout C.jet_frame_inv C.jet_word_repr.
Require Import C.jet_secp_canonical_normalize C.jet_secp_canonical_negate.
Require Import C.jet_secp_negate_input_bridge C.jet_secp_negate_write_calls.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque canonical_fe_normalize canonical_fe_negate Simplicity.Translate.encode.

Lemma field_rho_facts v rc : 0 <= v < 2 ^ 256 ->
  fe_limbs_ok (Int64.unsigned (write_fe_rho v rc 1%nat))
    (Int64.unsigned (write_fe_rho v rc 2%nat)) (Int64.unsigned (write_fe_rho v rc 3%nat))
    (Int64.unsigned (write_fe_rho v rc 4%nat)) (Int64.unsigned (write_fe_rho v rc 5%nat)) /\
  fe_val (Int64.unsigned (write_fe_rho v rc 1%nat))
    (Int64.unsigned (write_fe_rho v rc 2%nat)) (Int64.unsigned (write_fe_rho v rc 3%nat))
    (Int64.unsigned (write_fe_rho v rc 4%nat)) (Int64.unsigned (write_fe_rho v rc 5%nat)) = v.
Proof.
  intro HV. cbn [write_fe_rho]. rewrite !limb_rho_unsigned by exact HV.
  change (fe_limbs_ok (v mod 2 ^ 52) ((v / 2 ^ 52) mod 2 ^ 52)
    ((v / 2 ^ 104) mod 2 ^ 52) ((v / 2 ^ 156) mod 2 ^ 52) (v / 2 ^ 208) /\
    fe_val (v mod 2 ^ 52) ((v / 2 ^ 52) mod 2 ^ 52)
    ((v / 2 ^ 104) mod 2 ^ 52) ((v / 2 ^ 156) mod 2 ^ 52) (v / 2 ^ 208) = v).
  apply fe_limbs_of_ok. exact HV.
Qed.

Theorem eval_negate_write_after_read_field m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word 8)) mr ba bl :
  write_frame_at m0 bd dbase bw outedge cursor N ->
  fe_at mr ba 0 (map Int64.repr (fe_limbs_of
    (@toZ (WordToZ 8) (@canonical_fe_normalize Alg.CoreFunSem value)))) ->
  Mem.range_perm mr ba 0 40 Cur Freeable -> Mem.range_perm mr bl 0 16 Cur Freeable ->
  ba <> bl -> xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) (read_fe_log bi (Ptrofs.repr edge)) mr ->
  exists mn mw,
    Clight2.eval_funcall secp_ge mr (Internal f_secp256k1_fe_negate)
      [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vint Int.one] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mw Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (Simplicity.Translate.encode (@canonical_fe_negate Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(ba,0)] local_write_initial_regs mr) mr mw.
Proof.
  intros HO HField HFreeA HFreeL HSeparate HS HI.
  set (x := @canonical_fe_normalize Alg.CoreFunSem value).
  set (v := @toZ (WordToZ 8) x).
  pose proof (local_write_initial_rep_from_field v rc mr ba HField HFreeA) as HR.
  pose proof (read_fe_final_inv_to_write_initial m0 bd dbase bw outedge cursor N bi edge rc
    value mr HI) as HWI.
  assert (HSW : xsep (extA m0 bd bw bi) [(ba,0)]).
  { intros r Hr. destruct r as [|r]; [apply (HS 0%nat); cbn; lia|cbn in Hr; lia]. }
  assert (HV : 0 <= v < 2 ^ 256) by apply word_toZ_range.
  destruct (field_rho_facts v rc HV) as [Hok HValue].
  assert (Hlt : v < feP).
  { unfold v, x. rewrite <- canonical_field_order_matches_limb_model.
    exact (proj2 (canonical_normalized_field_range value)). }
  destruct (eval_negate_write_calls m0 bd dbase bw outedge cursor N bi rc false [] mr ba
    (write_fe_rho v rc) x HO HR HSW HWI Hok HValue Hlt)
    as (mn & mw & HNeg & HWrite & HFinal & HFreeFinal & HFrame).
  unfold x in HFinal. rewrite canonical_fe_negate_normalized_input in HFinal.
  cbn [app] in HFinal.
  assert (HValidL : Mem.valid_block mr bl).
  { eapply Mem.perm_valid_block with (ofs := 0) (k := Cur) (p := Freeable).
    apply HFreeL. lia. }
  assert (HFreeFinalL : Mem.range_perm mw bl 0 16 Cur Freeable).
  { intros pos HP. apply (proj1 (proj2 HFrame)); [exact HValidL| |apply HFreeL; exact HP].
    split; [exact HValidL|]. split.
    - apply no_local_write_foot. congruence.
    - exact (HS 1%nat ltac:(cbn; lia)). }
  exists mn, mw. split; [exact HNeg|]. split; [exact HWrite|].
  split; [exact HFinal|]. split; [exact HFreeFinal|]. split; assumption.
Qed.
Print Assumptions eval_negate_write_after_read_field.
