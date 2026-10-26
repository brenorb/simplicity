(** Execute the original generator's initial five FE_CONST limb stores,
    ret=1 and the NULL-blinding branch. No initial field value is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_curve_statements
  C.jet_secp_statement_prefix C.jet_secp_multiply_wrapper_layout C.jet_frame_constants
  C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_initial_store i := nth i
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Definition generator_initial_rhs i := match generator_initial_store i with
  Sassign _ rhs=>rhs | _=>Econst_long Int64.zero tulong end.
Definition generator_initial_value i := if Nat.eqb i 0 then Int64.repr 4 else Int64.zero.
Definition generator_initial_lhs i := Ederef
  (Ebinop Oadd (Efield (Evar _t curve_fe_type) _n (tarray tulong 5))
    (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tulong)) tulong.
Lemma generator_initial_store_source i : (i<5)%nat ->
  generator_initial_store i=Sassign (generator_initial_lhs i) (generator_initial_rhs i).
Proof. intro Index;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. Qed.
Lemma generator_initial_rhs_type i : (i<5)%nat ->typeof (generator_initial_rhs i)=tulong.
Proof. intro Index;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. Qed.
Lemma eval_generator_initial_rhs i e le m : (i<5)%nat ->
  eval_expr secp_ge e le m (generator_initial_rhs i) (Vlong (generator_initial_value i)).
Proof.
  intro Index;destruct i as [|[|[|[|[|i]]]]];try lia;
    cbv [generator_initial_rhs generator_initial_store generator_initial_value Nat.eqb
      f_secp256k1_generator_generate_internal fn_body split_statement_last fst nth];eval_closed_frame_constant.
Qed.
Lemma eval_generator_initial_array e le m bt : e!_t=Some (bt,curve_fe_type) ->
  eval_expr secp_ge e le m (Efield (Evar _t curve_fe_type) _n (tarray tulong 5)) (Vptr bt Ptrofs.zero).
Proof.
  intro T;destruct fe_n_layout as (co & Cenv & Offset).
  eapply eval_Elvalue with (loc:=bt) (ofs:=Ptrofs.zero) (bf:=Full).
  - rewrite <-(Ptrofs.add_zero_l Ptrofs.zero);eapply eval_Efield_struct with (co:=co) (delta:=0).
    + eapply eval_Elvalue;[apply eval_Evar_local;exact T|apply deref_loc_copy;reflexivity].
    + reflexivity.
    + exact Cenv.
    + exact Offset.
  - apply deref_loc_reference;reflexivity.
Qed.
Lemma eval_generator_initial_lhs i e le m bt : (i<5)%nat ->e!_t=Some (bt,curve_fe_type) ->
  eval_lvalue secp_ge e le m (generator_initial_lhs i) bt (Ptrofs.repr (8*Z.of_nat i)) Full.
Proof.
  intros Index T;unfold generator_initial_lhs;apply eval_Ederef.
  eapply eval_Ebinop with (v1:=Vptr bt Ptrofs.zero) (v2:=Vint (Int.repr (Z.of_nat i))).
  - apply eval_generator_initial_array;exact T.
  - constructor.
  - change (Some (Vptr bt (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.repr (Int.signed (Int.repr (Z.of_nat i)))))))=
      Some (Vptr bt (Ptrofs.repr (8*Z.of_nat i)))).
    rewrite Int.signed_repr by (change (-2147483648<=Z.of_nat i<=2147483647);lia).
    rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
    rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Fixpoint generator_initial_stores i count := match count with
  O=>Sskip | S count=>Ssequence (generator_initial_store i) (generator_initial_stores (S i) count) end.
Lemma generator_initial_stores_source : generator_initial_stores 0 5=
  statement_sequence (firstn 5 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))) Sskip.
Proof. reflexivity. Qed.
Theorem exec_generator_initial_stores count i e le m bt : (i+count<=5)%nat ->
  e!_t=Some (bt,curve_fe_type) ->Mem.range_perm m bt 0 40 Cur Freeable ->
  exists mi,Clight2.exec_stmt secp_ge e le m (generator_initial_stores i count) E0 le mi Out_normal /\
  Mem.range_perm mi bt 0 40 Cur Freeable /\lframe (fun b _=>b<>bt) m mi /\readonly_preserved m mi.
Proof.
  revert i m;induction count as [|count IH];intros i m Index T Owned.
  - exists m;split;[constructor|];split;[exact Owned|];split;[apply lframe_refl|apply preserved_refl].
  - assert (Access:Mem.valid_access m Mint64 bt (8*Z.of_nat i) Writable).
    { split.
      - intros pos Range;eapply Mem.perm_implies;[apply Owned;change (8*Z.of_nat i<=pos<8*Z.of_nat i+8) in Range;lia|constructor].
      - change (8|8*Z.of_nat i);exists (Z.of_nat i);lia. }
    destruct (Mem.valid_access_store m Mint64 bt (8*Z.of_nat i) (Vlong (generator_initial_value i)) Access) as (ms & Store).
    assert (Assign:Clight2.exec_stmt secp_ge e le m (generator_initial_store i) E0 le ms Out_normal).
    { rewrite generator_initial_store_source by lia.
      eapply exec_Sassign with (loc:=bt) (ofs:=Ptrofs.repr (8*Z.of_nat i)) (bf:=Full)
        (v2:=Vlong (generator_initial_value i)) (v:=Vlong (generator_initial_value i)).
      - apply eval_generator_initial_lhs;[lia|exact T].
      - apply eval_generator_initial_rhs;lia.
      - change (sem_cast (Vlong (generator_initial_value i)) (typeof (generator_initial_rhs i)) tulong m=
          Some (Vlong (generator_initial_value i))).
        rewrite generator_initial_rhs_type by lia;reflexivity.
      - apply assign_loc_value with (chunk:=Mint64);[reflexivity|].
        change (Mem.store Mint64 m bt (Ptrofs.unsigned (Ptrofs.repr (8*Z.of_nat i)))
          (Vlong (generator_initial_value i))=Some ms).
        rewrite Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);exact Store. }
    assert (FreeS:Mem.range_perm ms bt 0 40 Cur Freeable).
    { intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Owned;exact Range]. }
    assert (FrameS:lframe (fun b _=>b<>bt) m ms).
    { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|intros;congruence]. }
    destruct (IH (S i) ms ltac:(lia) T FreeS) as (mi & Rest & FreeI & FrameI & ReadI).
    exists mi;split.
    + cbn [generator_initial_stores];eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Assign|exact Rest].
    + split;[exact FreeI|];split;[eapply lframe_trans;[exact FrameS|exact FrameI]|].
      eapply preserved_trans;[eapply store_preserved;exact Store|exact ReadI].
Qed.

Definition generator_no_blind := nth 6
  (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))) Sskip.
Definition generator_blind_initialize := match generator_no_blind with Sifthenelse _ yes _=>yes | _=>Sskip end.
Definition generator_initial_prefix := statement_sequence
  (firstn 7 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal)))) Sskip.
Definition generator_initial_temps le := PTree.set _ret (Vint Int.one) le.
Lemma generator_no_blind_source : generator_no_blind=
  Sifthenelse (Etempvar _blind32 (tptr tuchar)) generator_blind_initialize Sskip.
Proof. reflexivity. Qed.
Lemma generator_initial_prefix_source : generator_initial_prefix=statement_sequence
  (firstn 5 (fst (split_statement_last (fn_body f_secp256k1_generator_generate_internal))))
  (Ssequence (Sset _ret (Econst_int Int.one tint)) (Ssequence generator_no_blind Sskip)).
Proof. reflexivity. Qed.
Theorem exec_generator_initial_prefix e le m bt : e!_t=Some (bt,curve_fe_type) ->
  le!_blind32=Some (Vlong Int64.zero) ->Mem.range_perm m bt 0 40 Cur Freeable ->
  exists mi,Clight2.exec_stmt secp_ge e le m generator_initial_prefix E0 (generator_initial_temps le) mi Out_normal /\
  Mem.range_perm mi bt 0 40 Cur Freeable /\lframe (fun b _=>b<>bt) m mi /\readonly_preserved m mi.
Proof.
  intros T Null Owned.
  destruct (exec_generator_initial_stores 5 0 e le m bt ltac:(lia) T Owned) as (mi & Stores & Free & Frame & Read).
  exists mi;split;[|split;[exact Free|];split;assumption].
  rewrite generator_initial_prefix_source;apply exec_statement_prefix_then_last with (le1:=le) (m1:=mi).
  - rewrite <-generator_initial_stores_source;exact Stores.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply exec_Sset;constructor|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[|constructor].
    rewrite generator_no_blind_source;eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=false).
    + apply eval_Etempvar;unfold generator_initial_temps;rewrite PTree.gso by discriminate;exact Null.
    + reflexivity.
    + constructor.
Qed.
