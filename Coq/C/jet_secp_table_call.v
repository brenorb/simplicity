(** Complete original signed storage-table lookup: actual assertions, branch,
    indexed decoder call, optional Y negation, function entry and return. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
 ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_affine_fields
 C.jet_secp_table_index C.jet_secp_table_decode C.jet_secp_affine_storage
 C.jet_secp_fe_nv C.jet_clight_readonly_frame.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition table_positive_expr :=
 Ebinop Ogt (Etempvar _n tint) (Econst_int (Int.repr 0) tint) tint.
Definition table_decode_stmt neg := curve_call _secp256k1_ge_from_storage f_secp256k1_ge_from_storage None
 [Etempvar _r (tptr (Tstruct __6121 noattr));table_entry_expr neg].
Definition table_y_expr :=
 Eaddrof (Efield (Ederef (Etempvar _r (tptr (Tstruct __6121 noattr)))
   (Tstruct __6121 noattr)) _y (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr)).
Definition table_negate_stmt := curve_call _secp256k1_fe_negate f_secp256k1_fe_negate None
 [table_y_expr;table_y_expr;Econst_int (Int.repr 1) tint].
Definition table_lookup_branch := Sifthenelse table_positive_expr (table_decode_stmt false)
 (Ssequence (table_decode_stmt true) table_negate_stmt).
Definition table_lookup_body := Ssequence (Sloop Sskip Sbreak)
 (Ssequence (Sloop Sskip Sbreak) (Ssequence (Sloop Sskip Sbreak) table_lookup_branch)).
Lemma table_lookup_body_source : fn_body f_secp256k1_ecmult_table_get_ge_storage=table_lookup_body.
Proof. reflexivity. Qed.

Lemma table_positive_value n e le m :
 le!_n=Some (Vint (Int.repr n)) -> -16384<n<16384 ->
 eval_expr secp_ge e le m table_positive_expr
   (Vint (if 0<?n then Int.one else Int.zero)).
Proof.
 intros HN NB;unfold table_positive_expr.
 eapply eval_Ebinop;[apply eval_Etempvar;exact HN|constructor|].
 change (Some (Val.of_bool (Int.lt (Int.repr 0) (Int.repr n)))=
   Some (Vint (if 0<?n then Int.one else Int.zero))).
 unfold Int.lt;rewrite !table_signed_repr by lia.
 destruct (zlt 0 n);destruct (0<?n) eqn:E;
   try (apply Z.ltb_lt in E;lia);try (apply Z.ltb_ge in E;lia);reflexivity.
Qed.

Lemma exec_table_decode_call neg n le m mf bout bin base :
 le!_r=Some (Vptr bout Ptrofs.zero) -> le!_pre=Some (Vptr bin (Ptrofs.repr base)) ->
 le!_n=Some (Vint (Int.repr n)) -> 0<table_magnitude neg n<16384 -> 0<=base ->
 base+64*table_storage_index n+64<=Ptrofs.max_unsigned ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (base+64*table_storage_index n))] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge empty_env le m (table_decode_stmt neg) E0 le mf Out_normal.
Proof.
 intros HR HP HN Bound Base Max Decode;unfold table_decode_stmt.
 eapply exec_curve_call with (vargs:=[Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (base+64*table_storage_index n))]) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
   eapply eval_Econs;[exact (eval_table_entry_expr neg n empty_env le m bin base HN HP Bound Base Max)|reflexivity|constructor].
 - exact Decode.
Qed.

Lemma exec_table_negate_call le m mf bout :
 le!_r=Some (Vptr bout Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
   [Vptr bout (Ptrofs.repr 40);Vptr bout (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge empty_env le m table_negate_stmt E0 le mf Out_normal.
Proof.
 intros HR Negate;unfold table_negate_stmt.
 assert (Y : eval_expr secp_ge empty_env le m table_y_expr (Vptr bout (Ptrofs.repr 40))).
 { exact (eval_affine_field_address le m bout 0 _r _y 40
     ltac:(right;left;reflexivity) ltac:(lia)
     ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia) HR). }
 eapply exec_curve_call with (vargs:=[Vptr bout (Ptrofs.repr 40);Vptr bout (Ptrofs.repr 40);Vint Int.one]) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - reflexivity.
 - eapply eval_Econs;[exact Y|reflexivity|].
   eapply eval_Econs;[exact Y|reflexivity|].
   eapply eval_Econs;[constructor|reflexivity|constructor].
 - exact Negate.
Qed.

Lemma exec_table_lookup_branch n le m md mf bout bin base :
 le!_r=Some (Vptr bout Ptrofs.zero) -> le!_pre=Some (Vptr bin (Ptrofs.repr base)) ->
 le!_n=Some (Vint (Int.repr n)) -> 0<Z.abs n<16384 -> 0<=base ->
 base+64*table_storage_index n+64<=Ptrofs.max_unsigned ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (base+64*table_storage_index n))] E0 md Vundef ->
 (if negb (0<?n) then Clight2.eval_funcall secp_ge md (Internal f_secp256k1_fe_negate)
   [Vptr bout (Ptrofs.repr 40);Vptr bout (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef else mf=md) ->
 Clight2.exec_stmt secp_ge empty_env le m table_lookup_branch E0 le mf Out_normal.
Proof.
 intros HR HP HN Bound Base Max Decode Tail.
 assert (NB : -16384<n<16384) by (destruct (Z_le_dec 0 n);
   [rewrite Z.abs_eq in Bound by lia|rewrite Z.abs_neq in Bound by lia];lia).
 unfold table_lookup_branch.
 eapply exec_Sifthenelse with (v1:=Vint (if 0<?n then Int.one else Int.zero)) (b:=0<?n).
 - apply table_positive_value;assumption.
 - destruct (0<?n);reflexivity.
 - destruct (0<?n) eqn:Pos;cbn [negb] in Tail.
   + subst mf;apply Z.ltb_lt in Pos.
     eapply exec_table_decode_call;try eassumption.
     unfold table_magnitude;rewrite Z.abs_eq in Bound by lia;exact Bound.
   + apply Z.ltb_ge in Pos.
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=md) (le1:=le).
     * eapply exec_table_decode_call;try eassumption.
       unfold table_magnitude;rewrite Z.abs_neq in Bound by lia;exact Bound.
     * apply exec_table_negate_call with (bout:=bout);assumption.
Qed.

Lemma exec_table_lookup_body n le m md mf bout bin base :
 le!_r=Some (Vptr bout Ptrofs.zero) -> le!_pre=Some (Vptr bin (Ptrofs.repr base)) ->
 le!_n=Some (Vint (Int.repr n)) -> 0<Z.abs n<16384 -> 0<=base ->
 base+64*table_storage_index n+64<=Ptrofs.max_unsigned ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_from_storage)
   [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr (base+64*table_storage_index n))] E0 md Vundef ->
 (if negb (0<?n) then Clight2.eval_funcall secp_ge md (Internal f_secp256k1_fe_negate)
   [Vptr bout (Ptrofs.repr 40);Vptr bout (Ptrofs.repr 40);Vint Int.one] E0 mf Vundef else mf=md) ->
 Clight2.exec_stmt secp_ge empty_env le m table_lookup_body E0 le mf Out_normal.
Proof.
 intros HR HP HN Bound Base Max Decode Tail.
 assert (Skip : Clight2.exec_stmt secp_ge empty_env le m (Sloop Sskip Sbreak) E0 le m Out_normal).
 { eapply exec_Sloop_stop2 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m)
     (out1:=Out_normal) (out2:=Out_break);constructor. }
 unfold table_lookup_body.
 do 3 (eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=le);[exact Skip|]).
 eapply exec_table_lookup_branch;eassumption.
Qed.

Definition table_lookup_temps n bout bin base : temp_env :=
 PTree.set _w (Vint (Int.repr 15)) (PTree.set _n (Vint (Int.repr n))
   (PTree.set _pre (Vptr bin (Ptrofs.repr base))
     (PTree.set _r (Vptr bout Ptrofs.zero) (create_undef_temps [])))).
Lemma table_lookup_entry n m bout bin base :
 function_entry2 secp_ge f_secp256k1_ecmult_table_get_ge_storage
 [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base);Vint (Int.repr n);Vint (Int.repr 15)]
 m empty_env (table_lookup_temps n bout bin base) m.
Proof.
 constructor.
 - constructor.
 - repeat constructor;cbn;intuition discriminate.
 - intros x y HX HY HE;cbn in HY;contradiction.
 - constructor.
 - reflexivity.
Qed.

Theorem eval_ecmult_table_get_ge_storage n w m bout bin base lo hi :
 0<Z.abs n<16384 -> 0<=base -> bout<>bin -> Mem.range_perm m bout 0 88 Cur Freeable ->
 affine_storage_readable m bin (base+64*table_storage_index n) w ->
 readonly_region_bounds m bin lo hi ->
 exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_table_get_ge_storage)
 [Vptr bout Ptrofs.zero;Vptr bin (Ptrofs.repr base);Vint (Int.repr n);Vint (Int.repr 15)] E0 mf Vundef /\
 Mem.range_perm mf bout 0 88 Cur Freeable /\
 (forall k : bool,fe_at mf bout (if k then 40 else 0) (table_signed_coordinate w (negb (0<?n)) k)) /\
 Mem.load Mint32 mf bout 80=Some (Vint Int.zero) /\
 affine_storage_readable mf bin (base+64*table_storage_index n) w /\
 readonly_region_bounds mf bin lo hi /\
 lframe (fun b pos => b<>bout \/ pos<0 \/ 84<=pos) m mf.
Proof.
 intros Bound Base Sep Free Source Readonly.
 destruct (eval_table_decode_signed (negb (0<?n)) w m bout bin
   (base+64*table_storage_index n) lo hi Sep Free Source Readonly)
   as (md & mf & Decode & Tail & Owned & Fields & Infinity & Input & RO & Frame).
 assert (Max : base+64*table_storage_index n+64<=Ptrofs.max_unsigned)
   by exact (proj1 (proj2 (proj2 Source))).
 assert (HR : (table_lookup_temps n bout bin base)!_r=Some (Vptr bout Ptrofs.zero)).
 { unfold table_lookup_temps;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 assert (HP : (table_lookup_temps n bout bin base)!_pre=Some (Vptr bin (Ptrofs.repr base))).
 { unfold table_lookup_temps;rewrite !PTree.gso by discriminate;apply PTree.gss. }
 assert (HN : (table_lookup_temps n bout bin base)!_n=Some (Vint (Int.repr n))).
 { unfold table_lookup_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 exists mf;split.
 - eapply eval_funcall_internal with (e:=empty_env) (le1:=table_lookup_temps n bout bin base)
     (le2:=table_lookup_temps n bout bin base) (m1:=m) (m2:=mf) (out:=Out_normal).
   + apply table_lookup_entry.
   + rewrite table_lookup_body_source;eapply exec_table_lookup_body;eassumption.
   + reflexivity.
   + reflexivity.
 - split;[exact Owned|];split;[exact Fields|];split;[exact Infinity|];
     split;[exact Input|];split;assumption.
Qed.
