(** The actual short-circuit output-count/isNullData tag. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec C.jet_elements_bit_expr.
Require Import C.jet_elements_field_eval C.jet_elements_index_eval C.jet_elements_null_data_loads.
Require Import C.jet_elements_null_data_small C.jet_elements_null_data_payload.
Require Import C.jet_output_layout C.jet_elements_effects.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_null_data_output_rep m be ebase bt txbase bout outbase i count (flag : bool) : Prop :=
  0 <= ebase /\ ebase + 8 <= Ptrofs.max_unsigned /\
  0 <= txbase /\ txbase + 712 <= Ptrofs.max_unsigned /\
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
  Mem.load Mint64 m bt (txbase + 704) = Some (Vlong count) /\
  (Int64.ltu i count = true ->
    0 <= outbase /\ outbase + 248 * Int64.unsigned i + 241 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) /\
    Mem.load Mint8unsigned m bout (outbase + 248 * Int64.unsigned i + 240) =
      Some (Vint (if flag then Int.one else Int.zero))).

Definition elements_null_data_output_then : statement :=
  Ssequence
    (Sset _t'45 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset _t'46 (Efield (Ederef (Etempvar _t'45 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _output (tptr (Tstruct _sigOutput noattr))))
      (Ssequence
        (Sset _t'47 (Efield (elements_indexed_deref _t'46 _i _sigOutput) _isNullData tbool))
        (Sset _t'7 (Ecast (Etempvar _t'47 tbool) tbool)))).

Definition elements_null_data_output_prefix : statement :=
  Ssequence
    (Sset _t'43 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset _t'44 (Efield (Ederef (Etempvar _t'43 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _numOutputs tulong))
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _t'44 tulong) tint)
        elements_null_data_output_then (Sset _t'7 (Econst_int Int.zero tint)))).

Definition elements_null_data_output_prefix_temps bt txbase bout outbase i count (flag : bool) le :=
  let le2 := PTree.set _t'44 (Vlong count) (PTree.set _t'43 (Vptr bt (Ptrofs.repr txbase)) le) in
  if Int64.ltu i count then
    PTree.set _t'7 (Vint (if flag then Int.one else Int.zero))
      (PTree.set _t'47 (Vint (if flag then Int.one else Int.zero))
        (PTree.set _t'46 (Vptr bout (Ptrofs.repr outbase))
          (PTree.set _t'45 (Vptr bt (Ptrofs.repr txbase)) le2)))
  else PTree.set _t'7 (Vint Int.zero) le2.

Definition elements_null_data_output_guard : statement :=
  Ssequence elements_null_data_output_prefix
    (elements_bit_expr_stmt (Some _t'8) (Etempvar _t'7 tint)).

Definition elements_null_data_output_guard_temps bt txbase bout outbase i count flag le :=
  PTree.set _t'8 (Vint (if andb (Int64.ltu i count) flag then Int.one else Int.zero))
    (elements_null_data_output_prefix_temps bt txbase bout outbase i count flag le).

Lemma exec_elements_null_data_output_prefix e le m be ebase bt txbase bout outbase i count flag :
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  Clight2.exec_stmt elements_ge e le m elements_null_data_output_prefix E0
    (elements_null_data_output_prefix_temps bt txbase bout outbase i count flag le) m Out_normal.
Proof.
  intros Henv Hi (He0 & HeM & Ht0 & HtM & L1 & L2 & Hmore).
  set (le1 := PTree.set _t'43 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le2 := PTree.set _t'44 (Vlong count) le1).
  unfold elements_null_data_output_prefix, elements_null_data_output_prefix_temps. fold le1 le2.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
  - apply exec_set. eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact elements_txEnv_tx.
    + reflexivity.
    + apply eval_elements_deref_struct; exact Henv.
    + rewrite elements_ptr_add_repr by lia. replace (ebase + 0) with ebase by lia.
      apply elements_loadv_repr; [lia|exact L1].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
    + apply exec_set. eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 704) (chunk := Mint64).
      * reflexivity.
      * exact elements_elementsTransaction_numOutputs.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold le1; apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact L2].
    + assert (HC : eval_expr elements_ge e le2 m
        (Ebinop Olt (Etempvar _i tulong) (Etempvar _t'44 tulong) tint)
        (Vint (if Int64.ltu i count then Int.one else Int.zero))).
      { eapply eval_Ebinop with (v1 := Vlong i) (v2 := Vlong count).
        - apply eval_Etempvar. unfold le2, le1. rewrite !PTree.gso by discriminate. exact Hi.
        - apply eval_Etempvar. unfold le2. apply PTree.gss.
        - change (Some (Val.of_bool (Int64.ltu i count)) = Some (Vint (if Int64.ltu i count then Int.one else Int.zero))).
          destruct (Int64.ltu i count); reflexivity. }
      destruct (Int64.ltu i count) eqn:HR.
      * specialize (Hmore eq_refl) as (Ho0 & HoM & L3 & L4).
        eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true); [exact HC|reflexivity|].
        unfold elements_null_data_output_then.
        set (le3 := PTree.set _t'45 (Vptr bt (Ptrofs.repr txbase)) le2).
        set (le4 := PTree.set _t'46 (Vptr bout (Ptrofs.repr outbase)) le3).
        set (le5 := PTree.set _t'47 (Vint (if flag then Int.one else Int.zero)) le4).
        fold le3 le4 le5.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le3).
        -- apply exec_set. eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
           ++ reflexivity.
           ++ exact elements_txEnv_tx.
           ++ reflexivity.
           ++ apply eval_elements_deref_struct. unfold le2, le1. rewrite !PTree.gso by discriminate. exact Henv.
           ++ rewrite elements_ptr_add_repr by lia. replace (ebase + 0) with ebase by lia.
              apply elements_loadv_repr; [lia|exact L1].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le4).
           ++ apply exec_set. eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 8) (chunk := Mptr).
              ** reflexivity.
              ** exact elements_elementsTransaction_output.
              ** reflexivity.
              ** apply eval_elements_deref_struct. unfold le3; apply PTree.gss.
              ** rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact L3].
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le5).
              ** apply exec_set. eapply eval_elements_indexed_field_value with (sz := 248) (delta := 240)
                   (chunk := Mint8unsigned) (base := outbase) (r := i);
                   [exact elements_sizeof_sigOutput|exact elements_sigOutput_isNullData|reflexivity|
                    unfold le4; apply PTree.gss| |exact Ho0|lia|lia|lia|exact L4].
                 unfold le4, le3, le2, le1. rewrite !PTree.gso by discriminate. exact Hi.
              ** apply exec_set. eapply eval_Ecast with (v1 := Vint (if flag then Int.one else Int.zero)).
                 --- apply eval_Etempvar. unfold le5; apply PTree.gss.
                 --- destruct flag; reflexivity.
      * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false); [exact HC|reflexivity|].
        apply exec_set, eval_Econst_int.
Qed.

Lemma elements_null_data_output_prefix_value bt txbase bout outbase i count flag le :
  (elements_null_data_output_prefix_temps bt txbase bout outbase i count flag le)!_t'7 =
    Some (Vint (if andb (Int64.ltu i count) flag then Int.one else Int.zero)).
Proof.
  unfold elements_null_data_output_prefix_temps. destruct (Int64.ltu i count); apply PTree.gss.
Qed.

Lemma elements_null_data_output_prefix_other bt txbase bout outbase i count flag le k :
  ~ In k [_t'43; _t'44; _t'45; _t'46; _t'47; _t'7] ->
  (elements_null_data_output_prefix_temps bt txbase bout outbase i count flag le)!k = le!k.
Proof.
  intros H. unfold elements_null_data_output_prefix_temps. destruct (Int64.ltu i count);
    repeat rewrite PTree.gso by (simpl in H; intuition congruence); reflexivity.
Qed.

Theorem exec_elements_null_data_output_guard e le m bd dbase bw edge cur
    be ebase bt txbase bout outbase i count flag :
  e!_writeBit = None -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag ->
  write_frame_at m bd dbase bw edge cur 1 ->
  exists mf, Clight2.exec_stmt elements_ge e le m elements_null_data_output_guard E0
    (elements_null_data_output_guard_temps bt txbase bout outbase i count flag le) mf Out_normal /\
    write_effect m mf bd dbase bw edge cur 1 [Some (andb (Int64.ltu i count) flag)].
Proof.
  intros HW HD Henv Hi HP HF.
  set (next := elements_null_data_output_prefix_temps bt txbase bout outbase i count flag le).
  pose proof (exec_elements_null_data_output_prefix e le m be ebase bt txbase bout outbase i count flag Henv Hi HP) as HR.
  assert (HD' : next!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
  { unfold next. rewrite elements_null_data_output_prefix_other; [exact HD|]. vm_compute; intuition discriminate. }
  assert (HC : next!_t'7 = Some (Vint (if andb (Int64.ltu i count) flag then Int.one else Int.zero))).
  { unfold next. apply elements_null_data_output_prefix_value. }
  destruct (exec_elements_bit_expr (andb (Int64.ltu i count) flag) (Some _t'8) (Etempvar _t'7 tint)
    e next m bd dbase bw edge cur eq_refl HW HD' ltac:(apply eval_Etempvar; exact HC) HF)
    as (mf & CALL & EFF).
  exists mf. split; [|exact EFF]. unfold elements_null_data_output_guard, elements_null_data_output_guard_temps.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HR|exact CALL].
Qed.

Fixpoint elements_find_returned_bit_prefix (id : ident) (s : statement) : option statement :=
  match s with
  | Ssequence a b =>
      match b with
      | Scall (Some id') (Evar fn _) _ => if Pos.eqb id id' && Pos.eqb fn _writeBit then Some s else
          elements_stmt_first (elements_find_returned_bit_prefix id a) (elements_find_returned_bit_prefix id b)
      | _ => elements_stmt_first (elements_find_returned_bit_prefix id a) (elements_find_returned_bit_prefix id b)
      end
  | Sifthenelse _ a b | Sloop a b =>
      elements_stmt_first (elements_find_returned_bit_prefix id a) (elements_find_returned_bit_prefix id b)
  | _ => None
  end.

Lemma elements_null_data_output_guard_source :
  elements_find_returned_bit_prefix _t'8 (fn_body f_simplicity_output_null_datum) = Some elements_null_data_output_guard.
Proof. reflexivity. Qed.

Lemma elements_null_data_output_rep_out_of_range m be ebase bt txbase bout outbase i count flag :
  Int64.ltu i count = false ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 712 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 m bt (txbase + 704) = Some (Vlong count) ->
  elements_null_data_output_rep m be ebase bt txbase bout outbase i count flag.
Proof.
  intros HR He0 HeM Ht0 HtM L1 L2.
  unfold elements_null_data_output_rep. do 6 (split; [assumption|]).
  intros Htrue. rewrite HR in Htrue. discriminate.
Qed.

Lemma elements_null_data_output_guard_value bt txbase bout outbase i count flag le :
  (elements_null_data_output_guard_temps bt txbase bout outbase i count flag le)!_t'8 =
    Some (Vint (if andb (Int64.ltu i count) flag then Int.one else Int.zero)).
Proof. unfold elements_null_data_output_guard_temps. apply PTree.gss. Qed.

Lemma elements_null_data_output_guard_other bt txbase bout outbase i count flag le k :
  ~ In k [_t'8; _t'43; _t'44; _t'45; _t'46; _t'47; _t'7] ->
  (elements_null_data_output_guard_temps bt txbase bout outbase i count flag le)!k = le!k.
Proof.
  intros H. unfold elements_null_data_output_guard_temps.
  rewrite PTree.gso by (simpl in H; intuition congruence).
  apply elements_null_data_output_prefix_other. intros HI. apply H. right; exact HI.
Qed.
