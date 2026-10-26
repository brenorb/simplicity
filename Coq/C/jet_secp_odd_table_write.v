(** Actual ge_set_xy call in the odd-multiple table's loop. Every one of the
    eight entry offsets is covered, preserving the rest of the table and the
    source point. This is the writer step, not a proof of the whole loop. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_ge_set_xy_indexed C.jet_secp_statement_prefix C.jet_secp_curve_statements
 C.jet_secp_gej_infinity_layout C.jet_secp_multiply_normalize_bridge
 C.jet_secp_field_read_preservation C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition odd_table_write_statement := match
 nth 7 (fst (split_statement_last (fn_body f_secp256k1_ecmult_odd_multiples_table))) Sskip with
 | Ssequence _ (Sloop (Ssequence _ (Ssequence _ writer)) _) => writer
 | _ => Sskip end.
Definition odd_table_entry_address := Ebinop Oadd (Etempvar _pre_a (tptr curve_ge_type))
 (Etempvar _i tint) (tptr curve_ge_type).
Definition odd_table_local_address fid := Eaddrof
 (Efield (Evar _ai (Tstruct __6123 noattr)) fid curve_fe_type) (tptr curve_fe_type).

Lemma odd_table_write_source : odd_table_write_statement=
 curve_call _secp256k1_ge_set_xy f_secp256k1_ge_set_xy None
 [odd_table_entry_address;odd_table_local_address _x;odd_table_local_address _y].
Proof. reflexivity. Qed.

Lemma eval_odd_table_entry_address e le m br i : 0<=i<8 ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr secp_ge e le m odd_table_entry_address (Vptr br (Ptrofs.repr (88*i))).
Proof.
 intros Index Table I;unfold odd_table_entry_address.
 eapply eval_Ebinop with (v1:=Vptr br Ptrofs.zero) (v2:=Vint (Int.repr i)).
 - apply eval_Etempvar;exact Table.
 - apply eval_Etempvar;exact I.
 - change (Some (Vptr br (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 88) (Ptrofs.repr (Int.signed (Int.repr i))))))=
    Some (Vptr br (Ptrofs.repr (88*i)))).
   rewrite Int.signed_repr by (change (-2147483648<=i<=2147483647);lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma eval_odd_table_local_address e le m ba fid delta :
 In (fid,delta) [(_x,0);(_y,40)] -> e!_ai=Some (ba,Tstruct __6123 noattr) ->
 eval_expr secp_ge e le m (odd_table_local_address fid) (Vptr ba (Ptrofs.repr delta)).
Proof.
 intros Field AI.
 assert (Layout:In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)]) by
   (destruct Field as [Same|[Same|Same]];[left|right;left|contradiction];exact Same).
 destruct (gej_infinity_field_layout fid delta Layout) as (co & Lookup & Offset).
 unfold odd_table_local_address;apply eval_Eaddrof;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Evar_local;exact AI|apply deref_loc_copy;reflexivity].
 - reflexivity.
 - exact Lookup.
 - exact Offset.
Qed.

Theorem exec_odd_table_write e le x y m br ba i :
 0<=i<8 -> br<>ba -> e!_ai=Some (ba,Tstruct __6123 noattr) -> e!_secp256k1_ge_set_xy=None ->
 le!_pre_a=Some (Vptr br Ptrofs.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) ->
 Mem.range_perm m br 0 704 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m odd_table_write_statement E0 le mf Out_normal /\
 fe_at mf br (88*i) (words5 x) /\ fe_at mf br (88*i+40) (words5 y) /\
 Mem.load Mint32 mf br (88*i+80)=Some (Vint Int.zero) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b pos=>b<>br \/ pos<88*i \/ 88*i+84<=pos) m mf /\ readonly_preserved m mf.
Proof.
 intros Index Sep AI Global Table I X Y Free.
 destruct (eval_ge_set_xy_indexed x y m br (88*i) ba Sep ltac:(lia)
   ltac:(exists (11*i);ring) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia)
   X Y ltac:(intros pos Range;apply Free;lia))
  as (mf & Call & RX & RY & Flag & Slot & Perm & Frame & Readonly).
 assert (XF:fe_at mf ba 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact Frame|];intros;left;congruence).
 assert (YF:fe_at mf ba 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y|exact Frame|];intros;left;congruence).
 assert (Full:Mem.range_perm mf br 0 704 Cur Freeable).
 { intros pos Range;apply (proj2 (Perm br pos Cur Freeable));apply Free;exact Range. }
 exists mf;split.
 - rewrite odd_table_write_source;eapply exec_curve_call with
    (vargs:=[Vptr br (Ptrofs.repr (88*i));Vptr ba Ptrofs.zero;Vptr ba (Ptrofs.repr 40)]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact Global.
   + eapply eval_Econs;[apply eval_odd_table_entry_address with (br:=br) (i:=i);[exact Index|exact Table|exact I]|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_address with (ba:=ba) (delta:=0);[left;reflexivity|exact AI]|reflexivity|].
     eapply eval_Econs;[apply eval_odd_table_local_address with (ba:=ba) (delta:=40);[right;left;reflexivity|exact AI]|reflexivity|constructor].
   + exact Call.
 - split;[exact RX|];split;[exact RY|];split;[exact Flag|];split;[exact XF|];split;[exact YF|];
   split;[exact Full|];split;[exact Perm|];split;assumption.
Qed.
