(** Both original generator digest-to-point stages: call set_b32, update ret
    with its actual flag, then execute SWU even when that flag is zero.
    SHA and the surrounding generator lifecycle are outside this stage. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.extraMath C.jet_sx_mem C.jet_sx_zval C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_set_b32_owned C.jet_secp_swu_raw_input
  C.jet_secp_swu_startup C.jet_secp_swu_word_parity C.jet_secp_swu_literal
  C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_rescale_literal
  C.jet_secp_field_cmov C.jet_secp_curve_statements C.jet_secp_curve_frame
  C.jet_secp_statement_prefix C.jet_secp_rescale_public_body C.jet_secp_swu_public_body
  C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_swu rescale_field_output swu_words_literal_output.

Definition generator_digest_accept bytes := Z.ltb (be_val bytes) feP.
Definition generator_digest_slot (second:bool) := if second then _t'2 else _t'1.
Definition generator_digest_set_call second := curve_call _secp256k1_fe_set_b32 f_secp256k1_fe_set_b32
  (Some (generator_digest_slot second)) [curve_local_address _t;Evar _b32 (tarray tuchar 32)].
Definition generator_digest_read second := Ssequence (generator_digest_set_call second)
  (Sset _ret (Ebinop Oand (Etempvar _ret tint) (Etempvar (generator_digest_slot second) tint) tint)).
Definition generator_digest_map := rescale_local_call _shallue_van_de_woestijne curve_ge_type curve_fe_type _add _t.
Definition generator_digest_stage second := statement_sequence [generator_digest_read second;generator_digest_map] Sskip.
Definition generator_digest_index (second:bool) := if second then 12%nat else 8%nat.
Definition generator_after_hash second := statement_sequence
  (skipn (generator_digest_index second) (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (snd (split_statement_last (fn_body f_secp256k1_generator_generate_internal))).
Definition generator_after_mapping second := statement_sequence
  (skipn (2+generator_digest_index second) (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (snd (split_statement_last (fn_body f_secp256k1_generator_generate_internal))).
Lemma generator_digest_stage_source second : generator_after_hash second=
  statement_sequence [generator_digest_read second;generator_digest_map] (generator_after_mapping second).
Proof. destruct second;reflexivity. Qed.
Lemma generator_hash_prefix_source second : fn_body f_secp256k1_generator_generate_internal=
  statement_sequence
    (firstn (generator_digest_index second) (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
    (generator_after_hash second).
Proof. destruct second;reflexivity. Qed.

Definition generator_digest_temps second prior bytes le :=
  PTree.set _ret (Vint (cmov_int (prior && generator_digest_accept bytes)))
    (PTree.set (generator_digest_slot second) (Vint (cmov_int (generator_digest_accept bytes))) le).
Lemma generator_digest_bit_repr flag : Int.repr (b2z flag)=cmov_int flag.
Proof. destruct flag;reflexivity. Qed.
Lemma generator_digest_ret second prior bytes le :
  (generator_digest_temps second prior bytes le)!_ret=
    Some (Vint (cmov_int (prior && generator_digest_accept bytes))).
Proof. apply PTree.gss. Qed.
Lemma generator_digest_rejected_ret second prior bytes le : generator_digest_accept bytes=false ->
  (generator_digest_temps second prior bytes le)!_ret=Some (Vint Int.zero).
Proof. intro Rejected;rewrite generator_digest_ret,Rejected,Bool.andb_false_r;reflexivity. Qed.
Lemma generator_digest_temps_other second prior bytes le id : id<>_ret -> id<>generator_digest_slot second ->
  (generator_digest_temps second prior bytes le)!id=le!id.
Proof. intros Ret Slot;unfold generator_digest_temps;rewrite !PTree.gso by assumption;reflexivity. Qed.

Lemma exec_generator_digest_set second e le m mf bt bb flag :
  e!_secp256k1_fe_set_b32=None -> e!_t=Some (bt,curve_fe_type) -> e!_b32=Some (bb,tarray tuchar 32) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_set_b32)
    [Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero] E0 mf (Vint (cmov_int flag)) ->
  Clight2.exec_stmt secp_ge e le m (generator_digest_set_call second) E0
    (PTree.set (generator_digest_slot second) (Vint (cmov_int flag)) le) mf Out_normal.
Proof.
  intros Fun Field Bytes Call;unfold generator_digest_set_call;eapply exec_curve_call with
    (vargs:=[Vptr bt Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vint (cmov_int flag)).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - exact Fun.
  - eapply eval_Econs.
    + apply eval_curve_local;exact Field.
    + reflexivity.
    + eapply eval_Econs.
      * eapply eval_Elvalue;[apply eval_Evar_local;exact Bytes|apply deref_loc_reference;reflexivity].
      * reflexivity.
      * constructor.
  - exact Call.
Qed.
Lemma exec_generator_digest_update second prior bytes e le m : le!_ret=Some (Vint (cmov_int prior)) ->
  Clight2.exec_stmt secp_ge e
    (PTree.set (generator_digest_slot second) (Vint (cmov_int (generator_digest_accept bytes))) le) m
    (Sset _ret (Ebinop Oand (Etempvar _ret tint) (Etempvar (generator_digest_slot second) tint) tint))
    E0 (generator_digest_temps second prior bytes le) m Out_normal.
Proof.
  intro Ret;unfold generator_digest_temps;apply exec_Sset.
  eapply eval_Ebinop with (v1:=Vint (cmov_int prior)) (v2:=Vint (cmov_int (generator_digest_accept bytes))).
  - apply eval_Etempvar;rewrite PTree.gso by (destruct second;discriminate);exact Ret.
  - apply eval_Etempvar;apply PTree.gss.
  - destruct prior,(generator_digest_accept bytes);reflexivity.
Qed.

Theorem exec_generator_digest_mapping second prior bytes e le m bt bb bp :
  (forall mc x,Int64.unsigned x<>0 ->
    Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
      E0 mc (Vint (Int.repr (Z_ctz (Int64.unsigned x))))) ->
  e!_secp256k1_fe_set_b32=None -> e!_shallue_van_de_woestijne=None ->
  e!_t=Some (bt,curve_fe_type) -> e!_add=Some (bp,curve_ge_type) -> e!_b32=Some (bb,tarray tuchar 32) ->
  le!_ret=Some (Vint (cmov_int prior)) ->
  length bytes=32%nat -> Forall (fun x=>0<=x<=255) bytes ->
  bt<>bb -> bp<>bt -> bp<>bb -> swu_startup m ->
  Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bb 0 32 Cur Freeable ->
  Mem.range_perm m bp 0 88 Cur Freeable ->
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned m bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) ->
  exists mf x y,
  Clight2.exec_stmt secp_ge e le m (generator_digest_stage second) E0
    (generator_digest_temps second prior bytes le) mf Out_normal /\
  fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ Mem.load Mint32 mf bp 80=Some (Vint Int.zero) /\
  square_input_bounds x /\ square_input_bounds y /\
  (rescale_field_output x,rescale_field_output y)=
    swu_words_literal_output (swu_raw_words (swu_digest_word bytes)) (swu_digest_word bytes) /\
  (generator_digest_accept bytes=true -> (rescale_field_output x,rescale_field_output y)=
    @literal_swu Alg.CoreFunSem (swu_digest_word bytes)) /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bb 0 32 Cur Freeable /\
  Mem.range_perm mf bp 0 88 Cur Freeable /\
  (forall i,(i<32)%nat -> Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))) /\
  swu_startup mf /\ lframe (fun b _=>b<>bt /\ b<>bb /\ b<>bp) m mf /\ readonly_preserved m mf.
Proof.
  intros Count SetFun MapFun T Add B Ret Len Bytes TB PT PB Ready FT FB FP Loads.
  destruct (eval_set_b32_owned bytes m bt bb Len Bytes TB FT FB Loads)
    as (m1 & ReadCall & Field & FT1 & FB1 & Bytes1 & F1 & R1).
  rewrite generator_digest_bit_repr in ReadCall.
  assert (FP1:Mem.range_perm m1 bp 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FP|exact F1|intros;split;assumption]. }
  assert (Ready1:swu_startup m1) by (eapply swu_startup_preserved;[exact Ready|exact R1]).
  destruct (eval_swu_raw_function (swu_digest_word bytes) m1 bp bt Count PT Ready1
    (swu_digest_input bytes m1 bt Len Bytes Field) FT1 FP1)
    as (mf & x & y & Map & X & Y & Flag & FTF & FPF & BX & BY & Value & ReadyF & F2 & R2).
  assert (FBF:Mem.range_perm mf bb 0 32 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FB1|exact F2|intros;split;congruence]. }
  assert (BytesF:forall i,(i<32)%nat ->
    Mem.load Mint8unsigned mf bb (Z.of_nat i)=Some (Vint (Int.repr (nth i bytes 0)))).
  { intros i Index;rewrite (proj1 F2).
    - apply Bytes1;exact Index.
    - eapply Mem.perm_valid_block;apply (FB1 0);lia.
    - intros;split;congruence. }
  exists mf,x,y;split.
  - unfold generator_digest_stage;cbn [statement_sequence].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=generator_digest_temps second prior bytes le).
    + unfold generator_digest_read;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1)
        (le1:=PTree.set (generator_digest_slot second) (Vint (cmov_int (generator_digest_accept bytes))) le).
      * eapply exec_generator_digest_set;eassumption.
      * apply exec_generator_digest_update;exact Ret.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=generator_digest_temps second prior bytes le).
      * unfold generator_digest_map;eapply exec_rescale_local_call.
        -- exact (proj1 (proj2 swu_public_symbols)).
        -- exact MapFun.
        -- exact Add.
        -- exact T.
        -- reflexivity.
        -- exact Map.
      * constructor.
  - split;[exact X|];split;[exact Y|];split;[exact Flag|];split;[exact BX|];split;[exact BY|];
      split;[exact Value|];split.
    + intro Accepted;rewrite Value;apply swu_raw_accepted_output;rewrite swu_digest_value by assumption.
      apply Z.ltb_lt;exact Accepted.
    + split;[exact FTF|];split;[exact FBF|];split;[exact FPF|];split;[exact BytesF|];split;[exact ReadyF|];split.
      * eapply lframe_trans.
        -- eapply lframe_implies;[exact F1|];intros b pos [NT [NB NP]] Valid;split;assumption.
        -- eapply lframe_implies;[exact F2|];intros b pos [NT [NB NP]] Valid;split;assumption.
      * eapply preserved_trans;[exact R1|exact R2].
Qed.
