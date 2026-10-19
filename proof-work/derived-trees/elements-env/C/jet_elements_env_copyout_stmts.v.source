(** The statements of [copyOutput], one execution lemma each. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx_abs C.jet_sha_be32_exec C.jet_sha_uchars_exec.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_tomidstate C.jet_elements_env_hashbuffer.
Require Import C.jet_elements_env_copyrawamt C.jet_elements_env_copyrawconf C.jet_elements_env_calc_token.
Require Import C.jet_elements_env_isfee C.jet_elements_env_nulldata_count.
Require Import C.jet_elements_env_parse_defs C.jet_elements_env_parse_ops C.jet_elements_env_parse_iter.
Require Import C.jet_elements_env_copyout_defs C.jet_elements_env_copyout_calls.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Ltac zc :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Section CopyOutStmts.
Variable e : env.
Variables (bres : block) (ores : Z) (bout : block) (oout : Z).
Hypothesis Hores : 0 <= ores /\ ores + 248 <= Ptrofs.max_unsigned.
Hypothesis Hoout : 0 <= oout /\ oout + 72 <= Ptrofs.max_unsigned.

Definition col (le : temp_env) : Prop :=
  le!_result = Some (Vptr bres (Ptrofs.repr ores)) /\ le!_output = Some (Vptr bout (Ptrofs.repr oout)).

Lemma col_set id v le : id <> _result -> id <> _output -> col le -> col (PTree.set id v le).
Proof. intros N1 N2 [H1 H2]. unfold col. rewrite !PTree.gso by (apply not_eq_sym; assumption). split; assumption. Qed.

Lemma co_res_field le m fld delta ty :
  col le -> envu_field_at _sigOutput fld delta -> 0 <= delta <= 248 ->
  eval_lvalue sha_ge e le m (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) fld ty)
    bres (Ptrofs.repr (ores + delta)) Full.
Proof.
  intros [Hr _] HF Hd. rewrite <- (envu_ptr_add_repr ores delta) by lia.
  eapply eval_envu_field_lvalue; [reflexivity|exact HF|apply eval_envu_deref_struct; exact Hr].
Qed.

Lemma co_res_addr le m fld delta ty :
  col le -> envu_field_at _sigOutput fld delta -> 0 <= delta <= 248 ->
  eval_expr sha_ge e le m (Eaddrof (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) fld ty) (tptr ty))
    (Vptr bres (Ptrofs.repr (ores + delta))).
Proof. intros. apply eval_Eaddrof. apply co_res_field; assumption. Qed.

Lemma co_res_struct le m fld delta sid :
  col le -> envu_field_at _sigOutput fld delta -> 0 <= delta <= 248 ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) fld (Tstruct sid noattr))
    (Vptr bres (Ptrofs.repr (ores + delta))).
Proof.
  intros. eapply eval_Elvalue with (loc := bres) (ofs := Ptrofs.repr (ores + delta)) (bf := Full);
    [apply co_res_field; assumption|apply deref_loc_copy; reflexivity].
Qed.

Lemma co_out_field le m fld delta ty :
  col le -> envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 72 ->
  eval_lvalue sha_ge e le m (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld ty)
    bout (Ptrofs.repr (oout + delta)) Full.
Proof.
  intros [_ Ho] HF Hd. rewrite <- (envu_ptr_add_repr oout delta) by lia.
  eapply eval_envu_field_lvalue; [reflexivity|exact HF|apply eval_envu_deref_struct; exact Ho].
Qed.

Lemma co_out_addr le m fld delta ty :
  col le -> envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 72 ->
  eval_expr sha_ge e le m (Eaddrof (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld ty) (tptr ty))
    (Vptr bout (Ptrofs.repr (oout + delta))).
Proof. intros. apply eval_Eaddrof. apply co_out_field; assumption. Qed.

Lemma co_out_struct le m fld delta sid :
  col le -> envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 72 ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld (Tstruct sid noattr))
    (Vptr bout (Ptrofs.repr (oout + delta))).
Proof.
  intros. eapply eval_Elvalue with (loc := bout) (ofs := Ptrofs.repr (oout + delta)) (bf := Full);
    [apply co_out_field; assumption|apply deref_loc_copy; reflexivity].
Qed.

Lemma co_out_ptr le m fld delta v :
  col le -> envu_field_at _rawElementsOutput fld delta -> 0 <= delta <= 64 ->
  Mem.load Mptr m bout (oout + delta) = Some v ->
  eval_expr sha_ge e le m (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld (tptr tuchar)) v.
Proof.
  intros HC HF Hd HL. eapply eval_Elvalue; [apply co_out_field; [exact HC|exact HF|lia]|].
  eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv. rewrite Ptrofs.unsigned_repr by lia. exact HL.
Qed.

(** [hashBuffer(&result->scriptPubKey, &output->scriptPubKey);] *)
Lemma co_s1_exec le m m' :
  e!_hashBuffer = None -> col le ->
  Clight2.eval_funcall sha_ge m (Internal f_hashBuffer)
    [Vptr bres (Ptrofs.repr (ores + 180)); Vptr bout (Ptrofs.repr (oout + 24))] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m co_s1 E0 le m' Out_normal.
Proof.
  intros He HC HX. unfold co_s1.
  eapply co_call2 with (f := f_hashBuffer);
    [exact He|exact co_sym_hashBuffer|exact co_fun_hashBuffer|reflexivity
    |apply co_res_addr; [exact HC|exact envu_sout_scriptPubKey|lia]|reflexivity
    |apply co_out_addr; [exact HC|exact envu_rout_scriptPubKey|lia]|reflexivity|exact HX].
Qed.

(** [result->emptyScript = 0 == output->scriptPubKey.len;] *)
Lemma co_s2_exec le m (lenS : int) :
  col le -> Mem.load Mint32 m bout (oout + 32) = Some (Vint lenS) ->
  Mem.perm m bres (ores + 241) Cur Writable ->
  exists m',
    Clight2.exec_stmt sha_ge e le m co_s2 E0 (PTree.set _t'11 (Vint lenS) le) m' Out_normal /\
    Mem.store Mint8unsigned m bres (ores + 241) (Val.of_bool (Int.eq (Int.repr 0) lenS)) = Some m'.
Proof.
  intros HC HL HP.
  assert (VA : Mem.valid_access m Mint8unsigned bres (ores + 241) Writable).
  { split; [intros o Ho; change (size_chunk Mint8unsigned) with 1 in Ho; replace o with (ores + 241) by lia; exact HP
           |exists (ores + 241); change (align_chunk Mint8unsigned) with 1; lia]. }
  destruct (Mem.valid_access_store m Mint8unsigned bres (ores + 241) (Val.of_bool (Int.eq (Int.repr 0) lenS)) VA) as [m' HS].
  exists m'. split; [|exact HS]. unfold co_s2.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'11 (Vint lenS) le) (m1 := m).
  - apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_rawElementsBuffer_len|reflexivity
      |apply co_out_struct; [exact HC|exact envu_rout_scriptPubKey|lia]|].
    rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|].
    replace (oout + 24 + 8) with (oout + 32) by lia. exact HL.
  - eapply exec_Sassign with (v2 := Val.of_bool (Int.eq (Int.repr 0) lenS))
      (v := Val.of_bool (Int.eq (Int.repr 0) lenS)).
    + apply co_res_field; [apply col_set; [discriminate|discriminate|exact HC]|exact envu_sout_emptyScript|lia].
    + eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|reflexivity].
    + destruct (Int.eq (Int.repr 0) lenS); reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

(** [f(&result->rf, output->fld);] for [copyRawConfidential] and [copyRawAmt]. *)
Lemma co_copy_stmt le m m' (tr fid : ident) (f : function) (sid fld rf : ident) (dout dres : Z) (s : rawsrc) :
  e!fid = None ->
  Genv.find_symbol (Clight.genv_genv sha_ge) fid = Some (sha_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block fid) Ptrofs.zero) = Some (Internal f) ->
  type_of_function f = Tfunction (Tcons (tptr (Tstruct sid noattr)) (Tcons (tptr tuchar) Tnil)) tvoid cc_default ->
  tr <> _result -> tr <> _output -> col le ->
  envu_field_at _rawElementsOutput fld dout -> 0 <= dout <= 64 ->
  envu_field_at _sigOutput rf dres -> 0 <= dres <= 248 ->
  Mem.load Mptr m bout (oout + dout) = Some (rs_val s) ->
  Clight2.eval_funcall sha_ge m (Internal f) [Vptr bres (Ptrofs.repr (ores + dres)); rs_val s] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Ssequence (Sset tr (Efield (Ederef (Etempvar _output (tptr ROUT)) ROUT) fld (tptr tuchar)))
       (Scall None
          (Evar fid (Tfunction (Tcons (tptr (Tstruct sid noattr)) (Tcons (tptr tuchar) Tnil)) tvoid cc_default))
          [Eaddrof (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) rf (Tstruct sid noattr))
             (tptr (Tstruct sid noattr)); Etempvar tr (tptr tuchar)]))
    E0 (PTree.set tr (rs_val s) le) m' Out_normal.
Proof.
  intros He HSy HFn HTy N1 N2 HC HF1 Hd1 HF2 Hd2 HL HX.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set tr (rs_val s) le) (m1 := m).
  - apply exec_Sset. eapply co_out_ptr; eassumption.
  - eapply co_call2 with (f := f);
      [exact He|exact HSy|exact HFn|exact HTy
      |apply co_res_addr; [apply col_set; assumption|exact HF2|exact Hd2]|reflexivity
      |apply eval_Etempvar; apply PTree.gss|destruct s; reflexivity|exact HX].
Qed.

(** [parseNullData(&result->pnd, allocation, allocationLen, &output->scriptPubKey);] *)
Lemma co_s6_exec le m m' ba oa bl ol :
  e!_parseNullData = None -> col le ->
  le!_allocation = Some (Vptr ba (Ptrofs.repr oa)) -> le!_allocationLen = Some (Vptr bl (Ptrofs.repr ol)) ->
  Clight2.eval_funcall sha_ge m (Internal f_parseNullData)
    [Vptr bres (Ptrofs.repr (ores + 224)); Vptr ba (Ptrofs.repr oa); Vptr bl (Ptrofs.repr ol);
     Vptr bout (Ptrofs.repr (oout + 24))] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m co_s6 E0 le m' Out_normal.
Proof.
  intros He HC Ha Hl HX. unfold co_s6. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _parseNullData) Ptrofs.zero)
    (vargs := [Vptr bres (Ptrofs.repr (ores + 224)); Vptr ba (Ptrofs.repr oa); Vptr bl (Ptrofs.repr ol);
               Vptr bout (Ptrofs.repr (oout + 24))]) (f := Internal f_parseNullData).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact co_sym_parseNullData]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [apply co_res_addr; [exact HC|exact envu_sout_pnd|lia]|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact Ha|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact Hl|reflexivity|].
    eapply eval_Econs; [apply co_out_addr; [exact HC|exact envu_rout_scriptPubKey|lia]|reflexivity|apply eval_Enil].
  - exact co_fun_parseNullData.
  - reflexivity.
  - exact HX.
Qed.
(** [result->isNullData = NULL != result->pnd.op;] *)
Lemma co_s7_exec le m (v7 : val) (isnd : bool) :
  col le -> Mem.load Mptr m bres (ores + 224) = Some v7 ->
  ((v7 = Vlong Int64.zero /\ isnd = false) \/
   (exists b o, v7 = Vptr b o /\ isnd = true /\ Mem.weak_valid_pointer m b (Ptrofs.unsigned o) = true)) ->
  Mem.perm m bres (ores + 240) Cur Writable ->
  exists m',
    Clight2.exec_stmt sha_ge e le m co_s7 E0 (PTree.set _t'7 v7 le) m' Out_normal /\
    Mem.store Mint8unsigned m bres (ores + 240) (Val.of_bool isnd) = Some m'.
Proof.
  intros HC HL Hv HP.
  assert (VA : Mem.valid_access m Mint8unsigned bres (ores + 240) Writable).
  { split; [intros o Ho; change (size_chunk Mint8unsigned) with 1 in Ho; replace o with (ores + 240) by lia; exact HP
           |exists (ores + 240); change (align_chunk Mint8unsigned) with 1; lia]. }
  destruct (Mem.valid_access_store m Mint8unsigned bres (ores + 240) (Val.of_bool isnd) VA) as [m' HS].
  exists m'. split; [|exact HS]. unfold co_s7.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'7 v7 le) (m1 := m).
  - apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_pnd_op|reflexivity
      |apply co_res_struct; [exact HC|exact envu_sout_pnd|lia]|].
    rewrite pn_add0. apply envu_loadv_repr; [lia|exact HL].
  - eapply exec_Sassign with (v2 := Val.of_bool isnd) (v := Val.of_bool isnd).
    + apply co_res_field; [apply col_set; [discriminate|discriminate|exact HC]|exact envu_sout_isNullData|lia].
    + eapply eval_Ebinop;
        [eapply eval_Ecast; [apply eval_Econst_int|reflexivity]|apply eval_Etempvar; apply PTree.gss|].
      destruct Hv as [[-> ->]|(b & o & -> & -> & HW)].
      * reflexivity.
      * change (option_map Val.of_bool
                  (if Int64.eq (Int64.repr (Int.signed (Int.repr 0))) Int64.zero &&
                      Mem.weak_valid_pointer m b (Ptrofs.unsigned o)
                   then Val.cmp_different_blocks Cne else None) = Some (Val.of_bool true)).
        rewrite HW. reflexivity.
    + destruct isnd; reflexivity.
    + eapply assign_loc_value; [reflexivity|]. unfold Mem.storev. rewrite Ptrofs.unsigned_repr by lia. exact HS.
Qed.

(** The two proof hashes. *)
Lemma co_proof_exec (Hmodel : memcpy_model) (tp tc tb src fld prf cid sid : ident) (dsrc dfld dprf : Z)
    (bK : block) le m (pfx : int) (s : bufsrc) (len : int) :
  e!_is_confidential = None -> e!_hashBuffer = None -> e!cid = Some (bK, RBUF) ->
  envu_field_at _sigOutput src dsrc -> envu_field_at sid _prefix 32 ->
  envu_field_at _sigOutput fld dfld -> envu_field_at _rawElementsOutput prf dprf ->
  0 <= dsrc -> dsrc + 36 <= 248 -> 0 <= dfld -> dfld + 32 <= 248 -> (4 | ores + dfld) ->
  0 <= dprf -> dprf + 16 <= 72 ->
  tp <> _result -> tp <> _output -> tc <> _result -> tc <> _output -> tb <> _result -> tb <> _output ->
  col le ->
  Mem.load Mint32 m bres (ores + dsrc + 32) = Some (Vint pfx) ->
  buf_at m bout (oout + dprf) s len -> buf_other s bres -> buf_other s bK -> bout <> bres -> bout <> bK ->
  bK <> bres -> GC <> bres -> GM <> bres -> GC <> bK -> GM <> bK ->
  Mem.range_perm m bK 0 16 Cur Writable ->
  Mem.range_perm m bres (ores + dfld) (ores + dfld + 32) Cur Writable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists le' m',
    Clight2.exec_stmt sha_ge e le m (co_proof_stmt tp tc tb src fld prf cid (Tstruct sid noattr)) E0 le' m' Out_normal /\
    col le' /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + dfld + 4 * Z.of_nat j) =
         Some (Vint (nth j (hash_buffer_regs (if is_conf pfx then buf_bytes s else [])) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bK ->
       (b <> bres \/ ofs + size_chunk ch <= ores + dfld \/ ores + dfld + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hg1 Hg2 HeK HF1 HF2 HF3 HF4 Hd1 Hd1' Hd2 Hd2' HA Hd3 Hd3' N1 N2 N3 N4 N5 N6 HC HLp HB OB1 OB2 Nor NoK NKr
    NG NM NGK NMK PK PR Hdisp HMax.
  set (le1 := PTree.set tp (Vint pfx) le).
  set (le2 := PTree.set tc (Vint (b2i (is_conf pfx))) le1).
  assert (HC1 : col le1) by (apply col_set; assumption).
  assert (HC2 : col le2) by (apply col_set; assumption).
  assert (X1 : Clight2.exec_stmt sha_ge e le m
     (Ssequence
        (Sset tp (Efield (Efield (Ederef (Etempvar _result (tptr SOUT)) SOUT) src (Tstruct sid noattr)) _prefix tint))
        (Scall (Some tc) (Evar _is_confidential (Tfunction (Tcons tint Tnil) tbool cc_default)) [Etempvar tp tint]))
     E0 le2 m Out_normal).
  { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    - apply exec_Sset. eapply eval_envu_field_value;
        [reflexivity|exact HF2|reflexivity|apply co_res_struct; [exact HC|exact HF1|lia]|].
      rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HLp].
    - change le2 with (set_opttemp (Some tc) (Vint (b2i (is_conf pfx))) le1).
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _is_confidential) Ptrofs.zero)
        (vargs := [Vint pfx]) (f := Internal f_is_confidential).
      + reflexivity.
      + eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg1|exact sha_is_confidential_symbol]|].
        apply deref_loc_reference; reflexivity.
      + eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
      + exact sha_is_confidential_funct.
      + reflexivity.
      + apply eval_is_confidential. }
  assert (HBV : bool_val (Vint (b2i (is_conf pfx))) tbool m = Some (is_conf pfx))
    by (destruct (is_conf pfx); reflexivity).
  assert (PRm : forall o, ores + dfld <= o < ores + dfld + 32 -> Mem.perm m bres o Cur Writable) by exact PR.
  destruct (is_conf pfx) eqn:EC.
  - (* the proof of the raw output *)
    set (le3 := PTree.set tb (Vptr bout (Ptrofs.repr (oout + dprf))) le2).
    destruct (hashbuf_any Hmodel m bres (ores + dfld) bout (oout + dprf) s len) as (m' & HX & HR & HFr & HPm & HV);
      try assumption; try lia.
    exists le3, m'. split; [|split; [apply col_set; assumption|split; [exact HR|split; [|split; assumption]]]].
    + unfold co_proof_stmt.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := m).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m); [exact X1|].
        eapply exec_Sifthenelse with (v1 := Vint (b2i true)) (b := true);
          [apply eval_Etempvar; apply PTree.gss|exact HBV|].
        apply exec_Sset. eapply eval_Ecast; [apply co_out_addr; [exact HC2|exact HF4|lia]|reflexivity].
      * eapply co_call2 with (f := f_hashBuffer);
          [exact Hg2|exact co_sym_hashBuffer|exact co_fun_hashBuffer|reflexivity
          |apply co_res_addr; [apply col_set; assumption|exact HF3|lia]|reflexivity
          |apply eval_Etempvar; apply PTree.gss|reflexivity|exact HX].
    + intros ch b ofs Hb _ Hd. apply HFr; assumption.
  - (* the zero buffer *)
    set (le3 := PTree.set tb (Vptr bK Ptrofs.zero) le2).
    assert (VK1 : Mem.valid_access m Mptr bK 0 Writable).
    { split; [intros o Ho; apply PK; change (size_chunk Mptr) with 8 in Ho; zc|exists 0; reflexivity]. }
    destruct (Mem.valid_access_store m Mptr bK 0 (Vlong Int64.zero) VK1) as [ma S1].
    assert (VK2 : Mem.valid_access ma Mint32 bK 8 Writable).
    { split; [intros o Ho; eapply Mem.perm_store_1; [exact S1|apply PK; change (size_chunk Mint32) with 4 in Ho; zc]
             |exists 2; reflexivity]. }
    destruct (Mem.valid_access_store ma Mint32 bK 8 (Vint Int.zero) VK2) as [mb S2].
    assert (Lab : forall ch b ofs, b <> bK -> Mem.load ch mb b ofs = Mem.load ch m b ofs).
    { intros ch b ofs Nb. rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (left; exact Nb).
      apply (Mem.load_store_other _ _ _ _ _ _ S1). left; exact Nb. }
    assert (Pab : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mb b ofs k p).
    { intros b ofs k p Hp. eapply Mem.perm_store_1; [exact S2|]. eapply Mem.perm_store_1; [exact S1|exact Hp]. }
    assert (Vab : forall b, Mem.valid_block m b -> Mem.valid_block mb b).
    { intros b Hb. eapply Mem.store_valid_block_1; [exact S2|]. eapply Mem.store_valid_block_1; [exact S1|exact Hb]. }
    assert (HBK : buf_at mb bK 0 BNull Int.zero).
    { split; [|split; [reflexivity|]].
      - change (0 + 8) with 8. rewrite (Mem.load_store_same _ _ _ _ _ _ S2). reflexivity.
      - change (Mem.load Mptr mb bK 0 = Some (Vlong Int64.zero)).
        rewrite (Mem.load_store_other _ _ _ _ _ _ S2) by (right; left; simpl; lia).
        rewrite (Mem.load_store_same _ _ _ _ _ _ S1). reflexivity. }
    destruct (hashbuf_any Hmodel mb bres (ores + dfld) bK 0 BNull Int.zero) as (m' & HX & HR & HFr & HPm & HV);
      try assumption; try lia.
    { intros o Ho. apply Pab, PR, Ho. }
    { exact I. }
    { unfold sha_dispatch_ok. rewrite Lab by exact NGK. exact Hdisp. }
    { rewrite Lab by exact NMK. exact HMax. }
    assert (HEK : forall le0 m0, eval_expr sha_ge e le0 m0 (Evar cid RBUF) (Vptr bK Ptrofs.zero)).
    { intros le0 m0. eapply eval_Elvalue; [apply eval_Evar_local; exact HeK|apply deref_loc_copy; reflexivity]. }
    exists le3, m'. split; [|split; [apply col_set; assumption|split; [exact HR|split; [|split]]]].
    + unfold co_proof_stmt.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mb).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m); [exact X1|].
        eapply exec_Sifthenelse with (v1 := Vint (b2i false)) (b := false);
          [apply eval_Etempvar; apply PTree.gss|exact HBV|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mb).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := ma).
           ++ eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vlong Int64.zero).
              ** eapply eval_envu_field_lvalue; [reflexivity|exact envu_rawElementsBuffer_buf|apply HEK].
              ** apply eval_Econst_int.
              ** reflexivity.
              ** eapply assign_loc_value; [reflexivity|]. exact S1.
           ++ eapply exec_Sassign with (v2 := Vint (Int.repr 0)) (v := Vint Int.zero).
              ** eapply eval_envu_field_lvalue; [reflexivity|exact envu_rawElementsBuffer_len|apply HEK].
              ** apply eval_Econst_int.
              ** reflexivity.
              ** eapply assign_loc_value; [reflexivity|]. exact S2.
        -- apply exec_Sset. eapply eval_Ecast; [apply eval_Eaddrof, eval_Evar_local; exact HeK|reflexivity].
      * eapply co_call2 with (f := f_hashBuffer);
          [exact Hg2|exact co_sym_hashBuffer|exact co_fun_hashBuffer|reflexivity
          |apply co_res_addr; [apply col_set; assumption|exact HF3|lia]|reflexivity
          |apply eval_Etempvar; apply PTree.gss|reflexivity|exact HX].
    + intros ch b ofs Hb NbK Hd. rewrite HFr by (try assumption; apply Vab, Hb). apply Lab, NbK.
    + intros b ofs k p Hb Hp. apply HPm; [apply Vab, Hb|apply Pab, Hp].
    + intros b Hb. apply HV, Vab, Hb.
Qed.
End CopyOutStmts.
