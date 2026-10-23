(** The three original state-pointer assignments before the Strauss call.
    Initial state contents are arbitrary; the stores are derived from ownership. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Errors.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ecmult_state_slots :=
 [(_aux,0,Tstruct __5467 noattr);(_pre_a,8,Tstruct __6121 noattr);
  (_ps,16,Tstruct _secp256k1_strauss_point_state noattr)].
Definition ecmult_state_assignment id ty n :=
 Sassign (Efield (Evar _state (Tstruct _secp256k1_strauss_state noattr)) id (tptr ty))
  (Evar id (tarray ty n)).
Definition ecmult_state_initialize := statement_sequence
 (fst (split_statement_last (fn_body f_secp256k1_ecmult))) Sskip.

Lemma ecmult_state_initialize_source : ecmult_state_initialize=
 Ssequence (ecmult_state_assignment _aux (Tstruct __5467 noattr) 8)
  (Ssequence (ecmult_state_assignment _pre_a (Tstruct __6121 noattr) 8)
   (Ssequence (ecmult_state_assignment _ps (Tstruct _secp256k1_strauss_point_state noattr) 1) Sskip)).
Proof. reflexivity. Qed.

Lemma ecmult_state_layout id delta ty : In (id,delta,ty) ecmult_state_slots ->
 exists co,(genv_cenv secp_ge)!_secp256k1_strauss_state=Some co /\
 field_offset secp_ge id (co_members co)=OK (delta,Full).
Proof.
 intro Slot.
 assert (View:option_map co_members ((genv_cenv secp_ge)!_secp256k1_strauss_state)=
  Some [Member_plain _aux (tptr (Tstruct __5467 noattr));
   Member_plain _pre_a (tptr (Tstruct __6121 noattr));
   Member_plain _ps (tptr (Tstruct _secp256k1_strauss_point_state noattr))]) by (vm_compute;reflexivity).
 destruct ((genv_cenv secp_ge)!_secp256k1_strauss_state) as [co|] eqn:Lookup;[|discriminate].
 exists co;split;[reflexivity|];inversion View as [Members];rewrite Members.
 destruct Slot as [Eq | [Eq | [Eq | Eq]]];try contradiction;inversion Eq;subst;reflexivity.
Qed.

Lemma exec_ecmult_state_assignment e le m mi bs b id delta ty n :
 In (id,delta,ty) ecmult_state_slots ->
 e!_state=Some (bs,Tstruct _secp256k1_strauss_state noattr) ->
 e!id=Some (b,tarray ty n) ->
 Mem.store Mptr m bs delta (Vptr b Ptrofs.zero)=Some mi ->
 Clight2.exec_stmt secp_ge e le m (ecmult_state_assignment id ty n) E0 le mi Out_normal.
Proof.
 intros Slot State Array Store;destruct (ecmult_state_layout id delta ty Slot) as (co & Lookup & Offset).
 assert (Bound:0<=delta<=16).
 { destruct Slot as [Eq | [Eq | [Eq | Eq]]];try contradiction;inversion Eq;lia. }
 unfold ecmult_state_assignment.
 eapply exec_Sassign with (loc:=bs) (ofs:=Ptrofs.repr delta) (bf:=Full)
  (v2:=Vptr b Ptrofs.zero) (v:=Vptr b Ptrofs.zero).
 - rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
   eapply eval_Efield_struct with (co:=co) (delta:=delta).
   + eapply eval_Elvalue;[apply eval_Evar_local;exact State|apply deref_loc_copy;reflexivity].
   + reflexivity.
   + exact Lookup.
   + exact Offset.
 - eapply eval_Elvalue;[apply eval_Evar_local;exact Array|apply deref_loc_reference;reflexivity].
 - reflexivity.
 - eapply assign_loc_value with (chunk:=Mptr);[reflexivity|].
   change (Mem.store Mptr m bs (Ptrofs.unsigned (Ptrofs.repr delta)) (Vptr b Ptrofs.zero)=Some mi).
   rewrite Ptrofs.unsigned_repr;[exact Store|change Ptrofs.max_unsigned with 18446744073709551615;lia].
Qed.

Lemma ecmult_state_store_owned m bs delta b :
 In delta [0;8;16] -> Mem.range_perm m bs 0 24 Cur Freeable ->
 exists mi,Mem.store Mptr m bs delta (Vptr b Ptrofs.zero)=Some mi /\
 Mem.range_perm mi bs 0 24 Cur Freeable /\
 Mem.unchanged_on (fun block pos=>block<>bs \/ pos<delta \/ delta+8<=pos) m mi.
Proof.
 intros Slot Owned.
 assert (Bound:0<=delta /\ delta+8<=24 /\ (8|delta)).
 { destruct Slot as [Eq | [Eq | [Eq | Eq]]];try contradiction;subst delta;
    repeat split;try lia;[exists 0|exists 1|exists 2];reflexivity. }
 assert (Access:Mem.valid_access m Mptr bs delta Writable).
 { split.
   - intros pos Range;eapply Mem.perm_implies;[apply Owned;change (delta<=pos<delta+8) in Range;lia|apply perm_F_any].
   - exact (proj2 (proj2 Bound)). }
 destruct (Mem.valid_access_store m Mptr bs delta (Vptr b Ptrofs.zero) Access) as (mi & Store).
 exists mi;split;[exact Store|];split.
 - intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Owned;exact Range].
 - eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range [Other | [Low | High]];change (delta<=pos<delta+8) in Range;[contradiction|lia|lia].
Qed.

Theorem exec_ecmult_state_initialize e le m bs bx ba bp :
 e!_state=Some (bs,Tstruct _secp256k1_strauss_state noattr) ->
 e!_aux=Some (bx,tarray (Tstruct __5467 noattr) 8) ->
 e!_pre_a=Some (ba,tarray (Tstruct __6121 noattr) 8) ->
 e!_ps=Some (bp,tarray (Tstruct _secp256k1_strauss_point_state noattr) 1) ->
 Mem.range_perm m bs 0 24 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m ecmult_state_initialize E0 le mf Out_normal /\
 Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\
 Mem.load Mptr mf bs 8=Some (Vptr ba Ptrofs.zero) /\
 Mem.load Mptr mf bs 16=Some (Vptr bp Ptrofs.zero) /\
 Mem.range_perm mf bs 0 24 Cur Freeable /\
 Mem.unchanged_on (fun block _=>block<>bs) m mf.
Proof.
 intros State Aux Pre PS Owned.
 destruct (ecmult_state_store_owned m bs 0 bx ltac:(cbn [In];tauto) Owned) as (m1 & S1 & O1 & F1).
 destruct (ecmult_state_store_owned m1 bs 8 ba ltac:(cbn [In];tauto) O1) as (m2 & S2 & O2 & F2).
 destruct (ecmult_state_store_owned m2 bs 16 bp ltac:(cbn [In];tauto) O2) as (mf & S3 & OF & F3).
 exists mf;split.
 - rewrite ecmult_state_initialize_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
   + eapply exec_ecmult_state_assignment;[cbn [ecmult_state_slots In];tauto|exact State|exact Aux|exact S1].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
     * eapply exec_ecmult_state_assignment;[cbn [ecmult_state_slots In];tauto|exact State|exact Pre|exact S2].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le);[|constructor].
       eapply exec_ecmult_state_assignment;[cbn [ecmult_state_slots In];tauto|exact State|exact PS|exact S3].
 - split.
   + erewrite Mem.load_store_other by (exact S3 || (right;left;change (0+8<=16);lia)).
     erewrite Mem.load_store_other by (exact S2 || (right;left;change (0+8<=8);lia)).
     exact (Mem.load_store_same _ _ _ _ _ _ S1).
   + split.
     * erewrite Mem.load_store_other by (exact S3 || (right;left;change (8+8<=16);lia)).
       exact (Mem.load_store_same _ _ _ _ _ _ S2).
     * split;[exact (Mem.load_store_same _ _ _ _ _ _ S3)|];split;[exact OF|].
       eapply Mem.unchanged_on_trans.
       -- eapply Mem.unchanged_on_trans.
          ++ eapply Mem.unchanged_on_implies;[exact F1|];intros block pos Other Valid;left;exact Other.
          ++ eapply Mem.unchanged_on_implies;[exact F2|];intros block pos Other Valid;left;exact Other.
       -- eapply Mem.unchanged_on_implies;[exact F3|];intros block pos Other Valid;left;exact Other.
Qed.
