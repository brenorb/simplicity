(** Original NULL-rzr double_var, with all execution and memory obligations
    derived from initial point storage.  Not yet a literal-specification bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp
  C.jet_secp_double_var_statements C.jet_secp_double_function C.jet_secp_double_all_calls
  C.jet_secp_point_normalizes_zero C.jet_secp_point_write_run C.jet_secp_square_columns
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_curve_frame C.jet_secp_local_regions C.jet_secp_gej_infinity_owned.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition double_var_entry_temps ba := PTree.set _rzr (Vlong Int64.zero)
  (PTree.set _a (Vptr ba Ptrofs.zero) (PTree.set _r (Vptr ba Ptrofs.zero)
    (create_undef_temps (fn_temps f_secp256k1_gej_double_var)))).
Lemma double_var_function_ok : fn_okb f_secp256k1_gej_double_var=true.
Proof. reflexivity. Qed.
Lemma double_var_function_entry m ba :
  function_entry2 secp_ge f_secp256k1_gej_double_var
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] m empty_env (double_var_entry_temps ba) m.
Proof.
  destruct (fn_okb_true _ double_var_function_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD|constructor|reflexivity].
Qed.

Lemma double_var_store_flag x y z m ba flag :
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Mem.store Mint32 m ba 120 (Vint flag)=Some mf /\
  Mem.load Mint32 mf ba 120=Some (Vint flag) /\
  fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf ba 80 (words5 z) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  lframe (fun b pos => b<>ba \/ pos<120 \/ 124<=pos) m mf.
Proof.
  intros HX HY HZ HF.
  assert (HW : Mem.range_perm m ba 0 128 Cur Writable) by (apply freeable_range_writable;exact HF).
  assert (HV : Mem.valid_access m Mint32 ba 120 Writable).
  { split;[intros pos HP;apply HW;change (120<=pos<124) in HP;lia|exists 30;reflexivity]. }
  destruct (Mem.valid_access_store m Mint32 ba 120 (Vint flag) HV) as (mf & HS).
  assert (HL : lframe (fun b pos => b<>ba \/ pos<120 \/ 124<=pos) m mf).
  { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact HS|].
    intros pos HP;change (120<=pos<124) in HP;intros [HE|[HE|HE]];[contradiction|lia|lia]. }
  exists mf;split;[exact HS|];split;[exact (Mem.load_store_same _ _ _ _ _ _ HS)|].
  split.
  - eapply curve_keep_field_range;[reflexivity|exact HX|exact HL|];intros pos HP;right;left;lia.
  - split.
    + eapply curve_keep_field_range;[reflexivity|exact HY|exact HL|];intros pos HP;right;left;lia.
    + split.
      * eapply curve_keep_field_range;[reflexivity|exact HZ|exact HL|];intros pos HP;right;left;lia.
      * split;[|exact HL];intros pos HP;eapply Mem.perm_store_1;[exact HS|apply HF;exact HP].
Qed.

Definition double_var_zflag y z := if Z.eqb (radix_value (double_output_z_words y z) mod feP) 0
  then Int.one else Int.zero.

Theorem eval_double_var_finite x y z m ba :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_output_x_words x y)) /\
  fe_at mf ba 40 (words5 (double_output_y_words x y)) /\
  fe_at mf ba 80 (words5 (double_output_z_words y z)) /\
  Mem.load Mint32 mf ba 120=Some (Vint (double_var_zflag y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  square_input_bounds (double_output_x_words x y) /\
  square_input_bounds (double_output_y_words x y) /\
  square_input_bounds (double_output_z_words y z) /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  intros BX BY BZ HFlag HX HY HZ HF.
  destruct (eval_double_function x y z m ba Int.zero BX BY BZ HFlag HX HY HZ HF)
    as (md & CD & XD & YD & ZD & FD & BXD & BYD & BZD & HD).
  destruct (eval_point_normalizes_zero PointZ (double_output_z_words y z) md ba BZD ZD FD)
    as (mz & CZ & ZZ & FZ & HZF).
  assert (XZ : fe_at mz ba 0 (words5 (double_output_x_words x y))).
  { eapply curve_keep_field_range;[reflexivity|exact XD|exact HZF|];intros pos HP;right;left;change (pos<80);lia. }
  assert (YZ : fe_at mz ba 40 (words5 (double_output_y_words x y))).
  { eapply curve_keep_field_range;[reflexivity|exact YD|exact HZF|];intros pos HP;right;left;
    change (pos<80);lia. }
  destruct (double_var_store_flag (double_output_x_words x y) (double_output_y_words x y)
    (double_output_z_words y z) mz ba (double_var_zflag y z) XZ YZ ZZ FZ)
    as (mf & HS & LF & XF & YF & ZF & FF & HSF).
  assert (HA : (double_var_entry_temps ba)!_a=Some (Vptr ba Ptrofs.zero)) by reflexivity.
  assert (HR : (double_var_entry_temps ba)!_r=Some (Vptr ba Ptrofs.zero)) by reflexivity.
  assert (HN : (double_var_entry_temps ba)!_rzr=Some (Vlong Int64.zero)) by reflexivity.
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env) (le1:=double_var_entry_temps ba)
      (le2:=PTree.set _t'1 (Vint (double_var_zflag y z)) (PTree.set _t'2 (Vint Int.zero) (double_var_entry_temps ba)))
      (m1:=m) (m2:=mf) (out:=Out_normal).
    + exact (double_var_function_entry m ba).
    + rewrite double_var_source.
      eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _t'2 (Vint Int.zero) (double_var_entry_temps ba)).
      * exact (exec_double_var_head_finite empty_env (double_var_entry_temps ba) m ba HA HFlag).
      * eapply exec_double_var_tail_from_calls with (md:=md) (mz:=mz) (ba:=ba);
          [rewrite PTree.gso by discriminate;exact HA|rewrite PTree.gso by discriminate;exact HR|
           rewrite PTree.gso by discriminate;exact HN|reflexivity|reflexivity|exact CD|exact CZ|exact HS].
    + reflexivity.
    + reflexivity.
  - split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact LF|];split;[exact FF|].
    split;[exact BXD|];split;[exact BYD|];split;[exact BZD|].
    eapply lframe_trans;[exact HD|].
    eapply lframe_trans.
    + eapply lframe_implies;[exact HZF|];intros b pos HO HV;left;exact HO.
    + eapply lframe_implies;[exact HSF|];intros b pos HO HV;left;exact HO.
Qed.

Theorem eval_double_var_infinite m ba flag :
  Mem.load Mint32 m ba 120=Some (Vint flag) -> flag<>Int.zero ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
  fe_at mf ba 0 (repeat Int64.zero 5) /\ fe_at mf ba 40 (repeat Int64.zero 5) /\
  fe_at mf ba 80 (repeat Int64.zero 5) /\ Mem.load Mint32 mf ba 120=Some (Vint Int.one) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  intros HFlag HNZ HF.
  destruct (eval_gej_infinity_initializer_owned m ba 0 ltac:(lia) ltac:(exists 0;reflexivity)
    ltac:(change (128<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ HF))
    as (mf & CI & XF & YF & ZF & LF & HL & HP & HV).
  exists mf;split.
  - eapply eval_funcall_internal with (e:=empty_env) (le1:=double_var_entry_temps ba)
      (le2:=PTree.set _t'2 (Vint flag) (double_var_entry_temps ba))
      (m1:=m) (m2:=mf) (out:=Out_return None).
    + exact (double_var_function_entry m ba).
    + rewrite double_var_source;eapply exec_Sseq_2.
      * eapply exec_double_var_head_infinite with (ba:=ba);
          [reflexivity|reflexivity|reflexivity|reflexivity|exact HFlag|exact HNZ|exact CI].
      * discriminate.
    + reflexivity.
    + reflexivity.
  - split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact LF|];split.
    + intros pos HPos;apply (proj2 (HP ba pos Cur Freeable));apply HF;exact HPos.
    + split.
      * intros chunk b ofs HValid HOther;apply HL;left;apply (HOther ofs).
        pose proof (size_chunk_pos chunk);lia.
      * split.
        -- intros b pos k p HValid HOther HPerm;apply (proj2 (HP b pos k p));exact HPerm.
        -- exact HV.
Qed.

Definition double_var_x_words flag x y := if Int.eq flag Int.zero then double_output_x_words x y else fun _ : nat => Int64.zero.
Definition double_var_y_words flag x y := if Int.eq flag Int.zero then double_output_y_words x y else fun _ : nat => Int64.zero.
Definition double_var_z_words flag y z := if Int.eq flag Int.zero then double_output_z_words y z else fun _ : nat => Int64.zero.
Definition double_var_output_flag flag y z := if Int.eq flag Int.zero then double_var_zflag y z else Int.one.
Lemma square_zero_bounds : square_input_bounds (fun _ : nat => Int64.zero).
Proof.
  intros i HI;change (0<(if Nat.eqb i 4 then 2^52 else 2^56)).
  destruct (Nat.eqb i 4);vm_compute;reflexivity.
Qed.
Lemma words5_zero : words5 (fun _ : nat => Int64.zero)=repeat Int64.zero 5.
Proof. reflexivity. Qed.

Theorem eval_double_var_owned x y z m ba flag :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  Mem.load Mint32 m ba 120=Some (Vint flag) ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_gej_double_var)
    [Vptr ba Ptrofs.zero;Vptr ba Ptrofs.zero;Vlong Int64.zero] E0 mf Vundef /\
  fe_at mf ba 0 (words5 (double_var_x_words flag x y)) /\
  fe_at mf ba 40 (words5 (double_var_y_words flag x y)) /\
  fe_at mf ba 80 (words5 (double_var_z_words flag y z)) /\
  Mem.load Mint32 mf ba 120=Some (Vint (double_var_output_flag flag y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\
  square_input_bounds (double_var_x_words flag x y) /\
  square_input_bounds (double_var_y_words flag x y) /\
  square_input_bounds (double_var_z_words flag y z) /\ lframe (fun b _ => b<>ba) m mf.
Proof.
  intros BX BY BZ HFlag HX HY HZ HF.
  unfold double_var_x_words,double_var_y_words,double_var_z_words,double_var_output_flag.
  destruct (Int.eq flag Int.zero) eqn:HE.
  - apply Int.same_if_eq in HE;subst flag;exact (eval_double_var_finite x y z m ba BX BY BZ HFlag HX HY HZ HF).
  - assert (HN : flag<>Int.zero) by (intro H;subst flag;rewrite Int.eq_true in HE;discriminate).
    destruct (eval_double_var_infinite m ba flag HFlag HN HF) as (mf & HC & XF & YF & ZF & LF & FF & HL).
    exists mf;rewrite !words5_zero.
    split;[exact HC|];split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact LF|];split;[exact FF|].
    split;[exact square_zero_bounds|];split;[exact square_zero_bounds|];split;[exact square_zero_bounds|exact HL].
Qed.
