(** Actual first branch of mixed addition, including the retained assertion
    loop and NULL-rzr test. Storage premises are discharged by set_ge_owned. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements
  C.jet_secp_double_statements C.jet_secp_double_flag C.jet_secp_double_var_statements
  C.jet_secp_gej_set_ge_owned C.jet_secp_fe_nv C.jet_sx_mem
  C.jet_secp_multiply_normalize_bridge C.jet_secp_point_set_bit.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition mixed_head := match fn_body f_secp256k1_gej_add_ge_var with
  | Ssequence h _ => h | _ => Sskip end.
Definition mixed_tail := match fn_body f_secp256k1_gej_add_ge_var with
  | Ssequence _ t => t | _ => Sskip end.
Lemma mixed_body_source : fn_body f_secp256k1_gej_add_ge_var=Ssequence mixed_head mixed_tail.
Proof. reflexivity. Qed.

Lemma exec_mixed_head_finite e le m ba :
  le!_a=Some (Vptr ba Ptrofs.zero) -> Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
  Clight2.exec_stmt secp_ge e le m mixed_head E0
    (PTree.set _t'4 (Vint Int.zero) le) m Out_normal.
Proof.
  intros HA HF;unfold mixed_head.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint Int.zero));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.

Lemma exec_mixed_head_infinite e le m mf ba br bb flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr br Ptrofs.zero) ->
  le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_secp256k1_gej_set_ge=None -> Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_set_ge)
    [Vptr br Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge e le m mixed_head E0
    (PTree.set _t'4 (Vint flag) le) mf (Out_return None).
Proof.
  intros HA HR HB HN HE HF HFlag HC;unfold mixed_head.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
  - apply exec_Sset;eapply eval_Elvalue.
    + apply eval_double_flag_field;exact HA.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
      change (Mem.load Mint32 m ba 120=Some (Vint flag));exact HF.
  - eapply exec_Sifthenelse with (v1:=Vint flag) (b:=true).
    + apply eval_Etempvar;apply PTree.gss.
    + change (Some (negb (Int.eq flag Int.zero))=Some true).
      rewrite Int.eq_false by exact HFlag;reflexivity.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
      * eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (m1:=m)
          (le1:=PTree.set _t'4 (Vint flag) le) (out1:=Out_normal).
        -- apply exec_Sskip.
        -- constructor.
        -- apply exec_Sbreak.
        -- constructor.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint flag) le).
        -- eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
           ++ apply eval_double_var_null_test;rewrite PTree.gso by discriminate;exact HN.
           ++ reflexivity.
           ++ apply exec_Sskip.
        -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'4 (Vint flag) le).
           ++ change (Clight2.exec_stmt secp_ge e (PTree.set _t'4 (Vint flag) le) m
                (curve_call _secp256k1_gej_set_ge f_secp256k1_gej_set_ge None
                  [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _b (tptr (Tstruct __6121 noattr))])
                E0 (PTree.set _t'4 (Vint flag) le) mf Out_normal).
              eapply exec_curve_call with (vargs:=[Vptr br Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vundef).
              ** unfold secp_pure;repeat (first [left;reflexivity|right]).
              ** exact HE.
              ** eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HR|reflexivity|].
                 eapply eval_Econs;[apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HB|reflexivity|constructor].
              ** exact HC.
           ++ apply exec_Sreturn_none.
Qed.

Theorem mixed_infinite_body_owned e le m ba bb x y flag :
  le!_a=Some (Vptr ba Ptrofs.zero) -> le!_r=Some (Vptr ba Ptrofs.zero) ->
  le!_b=Some (Vptr bb Ptrofs.zero) -> le!_rzr=Some (Vlong Int64.zero) ->
  e!_secp256k1_gej_set_ge=None -> ba<>bb ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  fe_at m bb 0 (words5 x) -> fe_at m bb 40 (words5 y) ->
  Mem.load Mint32 m bb 80=Some (Vint Int.zero) ->
  exists mf,
  Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_ge_var) E0
    (PTree.set _t'4 (Vint flag) le) mf (Out_return None) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
  fe_at mf ba 80 (words5 (C.jet_secp_point_set_bit.point_set_bit_words true)) /\
  Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ lframe (fun b _=>b<>ba) m mf.
Proof.
  intros HA HR HB HN HE HSep HFree HFlag HNZ HX HY HBF.
  destruct (eval_gej_set_ge_owned m ba bb x y Int.zero HSep HFree HX HY HBF)
    as (mf & HC & XO & YO & ZO & FO & HF & Frame).
  exists mf;split.
  - rewrite mixed_body_source;eapply exec_Sseq_2.
    + eapply exec_mixed_head_infinite;eassumption.
    + discriminate.
  - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FO|];split;assumption.
Qed.
