(** Complete original extrakeys even-Y helper, reusing native Y-field proofs. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_fns C.jet_secp_curve_statements
 C.jet_sx_exec C.jet_sx_mem C.jet_readBit_layout C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_field_mul_small
 C.jet_secp_field_negate_separate C.jet_secp_field_odd_words C.jet_secp_affine_odd_y
 C.jet_secp_affine_negate_words C.jet_secp_affine_flag_read C.jet_secp_decompress_statements
 C.jet_secp_swu_word_parity C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Definition extrakeys_even_y_words w:=if field_words_odd w then negate_sep_words w else w.
Definition extrakeys_even_y_temps b:=PTree.set _r (Vptr b Ptrofs.zero)
 (create_undef_temps (fn_temps f_secp256k1_extrakeys_ge_even_y)).
Definition extrakeys_even_y_flag:=Sloop
 (curve_call _secp256k1_ge_is_infinity f_secp256k1_ge_is_infinity (Some _t'1) [Etempvar _r (tptr curve_ge_type)]) Sbreak.
Definition extrakeys_even_y_parity:=Ssequence decompress_odd_call
 (Sifthenelse (Etempvar _t'2 tint)
 (Ssequence decompress_negate_stmt (Sset _y_parity (Econst_int Int.one tint))) Sskip).
Lemma extrakeys_even_y_body_source:fn_body f_secp256k1_extrakeys_ge_even_y=
 Ssequence (Sset _y_parity (Econst_int Int.zero tint))
 (Ssequence extrakeys_even_y_flag (Ssequence extrakeys_even_y_parity (Sreturn (Some (Etempvar _y_parity tint))))).
Proof. reflexivity. Qed.
Local Opaque secp_ge.
Theorem eval_extrakeys_ge_even_y w m b:
 mul_small_input_bounds w ->square_input_bounds w ->fe_at m b 40 (words5 w) ->
 Mem.range_perm m b 0 88 Cur Freeable ->Mem.load Mint32 m b 80=Some (Vint Int.zero) ->exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_extrakeys_ge_even_y)
 [Vptr b Ptrofs.zero] E0 mf (Vint (bit_int (field_words_odd w))) /\
 fe_at mf b 40 (words5 (extrakeys_even_y_words w)) /\square_input_bounds (extrakeys_even_y_words w) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/pos<40 \/80<=pos) m mf /\readonly_preserved m mf.
Proof.
 intros Small Bounds Y Free Flag.
 pose (le:=extrakeys_even_y_temps b).
 pose (le0:=PTree.set _y_parity (Vint Int.zero) le).
 pose (le1:=PTree.set _t'1 (Vint Int.zero) le0).
 assert (Entry:function_entry2 secp_ge f_secp256k1_extrakeys_ge_even_y [Vptr b Ptrofs.zero] m empty_env le m).
 { assert (OK:fn_okb f_secp256k1_extrakeys_ge_even_y=true) by reflexivity.
   destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
   constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity]. }
 assert (R0:le0!_r=Some (Vptr b Ptrofs.zero)) by reflexivity.
 assert (R1:le1!_r=Some (Vptr b Ptrofs.zero)) by reflexivity.
 assert (FlagStmt:Clight2.exec_stmt secp_ge empty_env le0 m extrakeys_even_y_flag E0 le1 m Out_normal).
 { unfold extrakeys_even_y_flag;change E0 with (E0**E0);eapply exec_Sloop_stop2 with (out1:=Out_normal) (out2:=Out_break).
   - eapply exec_curve_call with (vargs:=[Vptr b Ptrofs.zero]) (v:=Vint Int.zero).
     + unfold secp_pure;repeat first [left;reflexivity|right].
     + reflexivity.
     + eapply eval_Econs;[apply eval_Etempvar;exact R0|reflexivity|constructor].
     + apply eval_affine_flag_accessor;[clear;lia|clear;change (88<=18446744073709551615);lia|exact Flag].
   - constructor.
   - constructor.
   - constructor. }
 destruct (eval_affine_odd_y_words w m b Y Free) as (mi & Odd & YI & FI & FrameI).
 assert (OddBit:Int.repr (Int64.unsigned (Int64.and (w 0%nat) Int64.one))=bit_int (field_words_odd w)).
 { rewrite field_words_odd_value;destruct (field_words_odd w);reflexivity. }
 rewrite OddBit in Odd.
 pose (le2:=PTree.set _t'2 (Vint (bit_int (field_words_odd w))) le1).
 assert (R2:le2!_r=Some (Vptr b Ptrofs.zero)) by reflexivity.
 assert (OddStmt:Clight2.exec_stmt secp_ge empty_env le1 m decompress_odd_call E0 le2 mi Out_normal).
 { unfold decompress_odd_call;eapply exec_curve_call with (vargs:=[Vptr b (Ptrofs.repr 40)]) (v:=Vint (bit_int (field_words_odd w))).
   - unfold secp_pure;repeat first [left;reflexivity|right].
   - reflexivity.
   - eapply eval_Econs;[apply eval_decompress_field_address;[right;left;reflexivity|exact R1]|reflexivity|constructor].
   - exact Odd. }
 assert (Branch:exists mf lef,
  Clight2.exec_stmt secp_ge empty_env le1 m extrakeys_even_y_parity E0 lef mf Out_normal /\
  lef!_y_parity=Some (Vint (bit_int (field_words_odd w))) /\
  fe_at mf b 40 (words5 (extrakeys_even_y_words w)) /\square_input_bounds (extrakeys_even_y_words w) /\
  Mem.range_perm mf b 0 88 Cur Freeable /\lframe (fun bx pos=>bx<>b \/pos<40 \/80<=pos) m mf).
 { unfold extrakeys_even_y_parity;destruct (field_words_odd w) eqn:Parity.
   - destruct (eval_affine_y_negate_words w mi b YI FI) as (mf & Negate & YF & FF & FrameN).
     exists mf,(PTree.set _y_parity (Vint Int.one) le2);split.
     + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le2);[exact OddStmt|].
       eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
       * apply eval_Etempvar;unfold le2;apply PTree.gss.
       * reflexivity.
       * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le2).
         -- unfold decompress_negate_stmt;eapply exec_curve_call with
           (vargs:=[Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one]) (v:=Vundef).
            ++ unfold secp_pure;repeat first [left;reflexivity|right].
            ++ reflexivity.
            ++ eapply eval_Econs;[apply eval_decompress_field_address;[right;left;reflexivity|exact R2]|reflexivity|].
               eapply eval_Econs;[apply eval_decompress_field_address;[right;left;reflexivity|exact R2]|reflexivity|].
               eapply eval_Econs;[constructor|reflexivity|constructor].
            ++ exact Negate.
         -- apply exec_Sset;constructor.
     + split;[apply PTree.gss|].
       unfold extrakeys_even_y_words;rewrite Parity;split;[exact YF|];split;[exact (proj2 (negate_sep_numeric w Small))|];
       split;[exact FF|];eapply lframe_trans;[exact FrameI|exact FrameN].
   - exists mi,le2;split.
     + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=le2);[exact OddStmt|].
       eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
       * apply eval_Etempvar;unfold le2;apply PTree.gss.
       * reflexivity.
       * constructor.
     + split;[reflexivity|];unfold extrakeys_even_y_words;rewrite Parity;
       split;[exact YI|];split;[exact Bounds|];split;assumption. }
 destruct Branch as (mf & lef & Parity & Result & YF & BF & FF & Frame).
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_extrakeys_ge_even_y)
 [Vptr b Ptrofs.zero] E0 mf (Vint (bit_int (field_words_odd w)))).
 { eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=lef) (m1:=m) (m2:=mf)
    (out:=Out_return (Some (Vint (bit_int (field_words_odd w)),tint))).
   - exact Entry.
   - rewrite extrakeys_even_y_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le0).
     + apply exec_Sset;constructor.
     + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact FlagStmt|].
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Parity|].
       apply exec_Sreturn_some;apply eval_Etempvar;exact Result.
   - split;[clear;discriminate|reflexivity].
   - reflexivity. }
 exists mf;split;[exact Call|];split;[exact YF|];split;[exact BF|];split;[exact FF|];split;[exact Frame|].
 eapply (secp_closed_function_preserved f_secp256k1_extrakeys_ge_even_y);[reflexivity|reflexivity|exact Call].
Qed.
