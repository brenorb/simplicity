(** One actual auxiliary-array update and preservation of the source table
    and earlier products. The multiplication call is derived, not assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_beta_loop_control C.jet_secp_beta_slice C.jet_secp_beta_global
 C.jet_secp_generator_globalz_call C.jet_secp_globalz_loop C.jet_secp_curve_frame
 C.jet_secp_curve_statements C.jet_secp_point_mul_storage C.jet_secp_square_columns
 C.jet_secp_multiply_normalize_bridge C.jet_secp_field_slice_product
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge beta_block.

Definition beta_aux_frame bt bx i b pos :=
 (b<>bx \/ pos<40*i \/ 40*i+40<=pos) /\
 (b<>bt \/ pos<88*i \/ 88*i+40<=pos) /\
 (b<>beta_block \/ pos<0 \/ 40<=pos).
Definition beta_aux_prefix m bx xs n := forall k,(k<n)%nat ->
 fe_at m bx (40*Z.of_nat k) (words5 (point_mul_words (xs k) beta_digits)).

Lemma beta_aux_keeps_table m mf bt bx xs ys i : 0<=i<8 -> bt<>bx -> bt<>beta_block ->
 globalz_table_rep m bt xs ys -> Mem.range_perm m bt 0 704 Cur Freeable ->
 fe_at mf bt (88*i) (words5 (xs (Z.to_nat i))) ->
 lframe (beta_aux_frame bt bx i) m mf -> globalz_table_rep mf bt xs ys.
Proof.
 intros Index TX TB Table Free Selected Frame k Bound.
 destruct (Table k Bound) as (X & Y & Flag).
 assert (Valid:Mem.valid_block m bt) by (eapply Mem.perm_valid_block;apply (Free 0);lia).
 split.
 - destruct (Nat.eq_dec k (Z.to_nat i)) as [->|Different].
   + replace (88*Z.of_nat (Z.to_nat i)+0) with (88*i) by lia;exact Selected.
   + assert (KI:Z.of_nat k<>i) by (intro Same;apply Different;lia).
     eapply curve_keep_field_range;[reflexivity|exact X|exact Frame|].
     intros pos Pos;unfold beta_aux_frame;split;[left;exact TX|];split;[right;lia|left;exact TB].
 - split.
   + eapply curve_keep_field_range;[reflexivity|exact Y|exact Frame|].
     intros pos Pos;unfold beta_aux_frame;split;[left;exact TX|];split;[right;lia|left;exact TB].
   + rewrite (proj1 Frame Mint32 bt (88*Z.of_nat k+80) Valid);[exact Flag|].
     intros pos Pos;change (88*Z.of_nat k+80<=pos<88*Z.of_nat k+80+4) in Pos.
     unfold beta_aux_frame;split;[left;exact TX|];split;[right;lia|left;exact TB].
Qed.

Lemma beta_aux_extends_prefix m mf bt bx xs n : bx<>bt -> bx<>beta_block ->
 beta_aux_prefix m bx xs n ->
 fe_at mf bx (40*Z.of_nat n) (words5 (point_mul_words (xs n) beta_digits)) ->
 lframe (beta_aux_frame bt bx (Z.of_nat n)) m mf -> beta_aux_prefix mf bx xs (S n).
Proof.
 intros XT XB Prefix Last Frame k Bound.
 destruct (Nat.eq_dec k n) as [->|Different];[exact Last|].
 eapply curve_keep_field_range;[reflexivity|apply Prefix;lia|exact Frame|].
 intros pos Pos;unfold beta_aux_frame;split;[right;left;lia|];split;[left;exact XT|left;exact XB].
Qed.

Theorem exec_beta_aux_iteration e le xs ys m bs bt bx i :
 0<=i<8 -> bs<>bt -> bs<>bx -> bs<>beta_block -> bt<>bx -> bt<>beta_block -> bx<>beta_block ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_const_beta=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_i=Some (Vint (Int.repr i)) ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) -> Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> (forall k,(k<8)%nat -> square_input_bounds (xs k)) ->
 Mem.range_perm m bs 0 24 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable -> beta_initialized m -> exists mf,
 Clight2.exec_stmt secp_ge e le m beta_aux_iteration E0 (beta_aux_temps le bx bt) mf Out_normal /\
 globalz_table_rep mf bt xs ys /\
 fe_at mf bx (40*i) (words5 (point_mul_words (xs (Z.to_nat i)) beta_digits)) /\
 Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\ Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\
 Mem.range_perm mf bs 0 24 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\ beta_initialized mf /\ keeps_permissions m mf /\
 readonly_preserved m mf /\ lframe (beta_aux_frame bt bx i) m mf.
Proof.
 intros Index ST SX SB TX TB XB Global Const State NP I PX PT Table Bounds FreeS FreeT FreeX Init.
 assert (NatIndex:(Z.to_nat i<8)%nat) by lia.
 destruct (Table _ NatIndex) as (X & Y & Flag).
 replace (88*Z.of_nat (Z.to_nat i)+0) with (88*i) in X by lia.
 destruct (eval_beta_slice_product (xs (Z.to_nat i)) m bx (40*i) bt (88*i)
  (Bounds _ NatIndex) ltac:(left;congruence) ltac:(left;exact XB) ltac:(left;exact TB)
  ltac:(lia) ltac:(exists (5*i);ring) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;lia)
  ltac:(intros pos Pos;eapply Mem.perm_implies;[apply FreeX;lia|constructor]) X Init)
  as (mf & Call & Out & Source & Literal & OutBound & InitF & Keep & RO & Frame).
 change (lframe (beta_aux_frame bt bx i) m mf) in Frame.
 assert (XF:(beta_aux_temps le bx bt)!_t'30=Some (Vptr bx Ptrofs.zero)).
 { unfold beta_aux_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
 assert (TF:(beta_aux_temps le bx bt)!_t'31=Some (Vptr bt Ptrofs.zero)) by apply PTree.gss.
 assert (NPF:(beta_aux_temps le bx bt)!_np=Some (Vlong Int64.zero)).
 { rewrite beta_aux_temps_other by discriminate;exact NP. }
 assert (IF:(beta_aux_temps le bx bt)!_i=Some (Vint (Int.repr i))).
 { rewrite beta_aux_temps_other by discriminate;exact I. }
 assert (Body:Clight2.exec_stmt secp_ge e le m beta_aux_iteration E0 (beta_aux_temps le bx bt) mf Out_normal).
 { rewrite beta_aux_iteration_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'30 (Vptr bx Ptrofs.zero) le).
   - apply exec_Sset;eapply (eval_generator_state_pointer e le m bs 0 _aux 0 curve_fe_type).
     + right;left;reflexivity.
     + exact State.
     + lia.
     + change (24<=18446744073709551615);lia.
     + exact PX.
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=beta_aux_temps le bx bt).
     + apply exec_Sset;eapply eval_generator_state_pointer with (b:=bs) (base:=0) (delta:=8).
       * left;reflexivity.
       * rewrite PTree.gso by discriminate;exact State.
       * lia.
       * change (24<=18446744073709551615);lia.
       * exact PT.
     + unfold beta_aux_call;eapply exec_curve_call with
       (vargs:=[Vptr bx (Ptrofs.repr (40*i));Vptr bt (Ptrofs.repr (88*i));Vptr beta_block Ptrofs.zero]) (v:=Vundef).
       * unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
       * exact Global.
       * eapply eval_Econs with (v1:=Vptr bx (Ptrofs.repr (40*i)));
         [exact (eval_beta_aux_out e _ m bx i Index NPF IF XF)|reflexivity|].
         eapply eval_Econs with (v1:=Vptr bt (Ptrofs.repr (88*i)));
         [exact (eval_beta_aux_in e _ m bt i Index NPF IF TF)|reflexivity|].
         eapply eval_Econs with (v1:=Vptr beta_block Ptrofs.zero);
         [apply eval_beta_aux_constant;exact Const|reflexivity|constructor].
       * exact Call. }
 assert (TableF:globalz_table_rep mf bt xs ys).
 { eapply beta_aux_keeps_table;[exact Index|exact TX|exact TB|exact Table|exact FreeT|exact Source|exact Frame]. }
 assert (ValidS:Mem.valid_block m bs) by (eapply Mem.perm_valid_block;apply (FreeS 0);lia).
 assert (StateFrame:forall pos,beta_aux_frame bt bx i bs pos).
 { intro pos;unfold beta_aux_frame;split;[left;exact SX|];split;[left;exact ST|left;exact SB]. }
 exists mf;split;[exact Body|];split;[exact TableF|];split;[exact Out|];split.
 - rewrite (proj1 Frame Mptr bs 0 ValidS);[exact PX|intros;apply StateFrame].
 - split.
   + rewrite (proj1 Frame Mptr bs 8 ValidS);[exact PT|intros;apply StateFrame].
   + split;[intros pos Pos;apply Keep,FreeS;exact Pos|];split;
     [intros pos Pos;apply Keep,FreeT;exact Pos|];split;
     [intros pos Pos;apply Keep,FreeX;exact Pos|];split;[exact InitF|];split;[exact Keep|];split;assumption.
Qed.
