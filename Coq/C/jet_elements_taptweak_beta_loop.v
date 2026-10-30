(** Original eight-product auxiliary loop for the single-point caller.
    Every stored beta-product and every iteration execution is derived. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_beta_loop_control C.jet_secp_beta_loop_step C.jet_secp_beta_slice C.jet_secp_beta_global
 C.jet_secp_generator_globalz_call C.jet_secp_globalz_loop C.jet_secp_square_columns
 C.jet_secp_point_mul_storage C.jet_secp_multiply_normalize_bridge
 C.jet_secp_point_mul_numeric C.jet_secp_beta_spec C.jet_secp_rescale_literal
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Require Import C.jet_secp_beta_loop C.jet_elements_taptweak_pure C.jet_elements_taptweak_beta.
Require Import C.jet_elements_taptweak_beta_control C.jet_elements_taptweak_beta_step.
Local Opaque secp_ge elements_taptweak_ge elements_taptweak_beta_block.
Definition elements_taptweak_beta_aux_loop_frame bt bx b (_:Z) := b<>bx /\ b<>bt /\ b<>elements_taptweak_beta_block.

Definition elements_taptweak_beta_aux_final_memory m mf bs bt bx xs ys :=
 globalz_table_rep mf bt xs ys /\ beta_aux_prefix mf bx xs 8 /\
 Mem.load Mptr mf bs 0=Some (Vptr bx Ptrofs.zero) /\ Mem.load Mptr mf bs 8=Some (Vptr bt Ptrofs.zero) /\
 Mem.range_perm mf bs 0 24 Cur Freeable /\ Mem.range_perm mf bt 0 704 Cur Freeable /\
 Mem.range_perm mf bx 0 320 Cur Freeable /\ elements_taptweak_beta_initialized mf /\ keeps_permissions m mf /\
 readonly_preserved m mf /\ lframe (elements_taptweak_beta_aux_loop_frame bt bx) m mf.

Lemma exec_elements_taptweak_beta_aux_inner_done e le m : le!_i=Some (Vint (Int.repr 8)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_inner E0 le m Out_normal.
Proof.
 intro I;rewrite beta_aux_inner_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
 exact (eval_elements_taptweak_beta_aux_guard e le m 8 ltac:(lia) I).
Qed.

Lemma exec_elements_taptweak_beta_aux_inner_join e le m i le1 m1 le2 lef mf : 0<=i<8 -> le!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_iteration E0 le1 m1 Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e le1 m1 beta_aux_step E0 le2 m1 Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e le2 m1 beta_aux_inner E0 lef mf Out_normal ->
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_inner E0 lef mf Out_normal.
Proof.
 intros Index I Body Step Rest;rewrite beta_aux_inner_source in Rest|-*.
 eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (le1:=le1) (m1:=m1)
  (le2:=le2) (m2:=m1) (out1:=Out_normal).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
     pose proof (eval_elements_taptweak_beta_aux_guard e le m i ltac:(lia) I) as Guard.
     rewrite (proj2 (Z.ltb_lt i 8) ltac:(lia)) in Guard;exact Guard.
   + exact Body.
 - constructor.
 - exact Step.
 - exact Rest.
Qed.

Theorem exec_elements_taptweak_beta_aux_inner_from (remaining:nat) : forall n,(n+remaining=8)%nat ->
 forall e le xs ys m bs bt bx,
 bs<>bt -> bs<>bx -> bs<>elements_taptweak_beta_block -> bt<>bx -> bt<>elements_taptweak_beta_block -> bx<>elements_taptweak_beta_block ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_const_beta=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_i=Some (Vint (Int.repr (Z.of_nat n))) ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) -> Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> (forall k,(k<8)%nat -> square_input_bounds (xs k)) ->
 beta_aux_prefix m bx xs n ->
 Mem.range_perm m bs 0 24 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable -> elements_taptweak_beta_initialized m -> exists lef mf,
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_inner E0 lef mf Out_normal /\
 lef!_i=Some (Vint (Int.repr 8)) /\
 (forall id,id<>_i -> id<>_t'30 -> id<>_t'31 -> lef!id=le!id) /\
 elements_taptweak_beta_aux_final_memory m mf bs bt bx xs ys.
Proof.
 induction remaining as [|remaining IH];intros n Count e le xs ys m bs bt bx
  ST SX SB TX TB XB Global Const State NP I PX PT Table Bounds Prefix FreeS FreeT FreeX Init.
 - assert (N:n=8%nat) by lia;subst n;exists le,m;split;[apply exec_elements_taptweak_beta_aux_inner_done;exact I|];
   split;[exact I|];split;[intros;reflexivity|];split;[exact Table|];split;[exact Prefix|];
   split;[exact PX|];split;[exact PT|];split;[exact FreeS|];split;[exact FreeT|];split;[exact FreeX|];
   split;[exact Init|];split;[apply keeps_permissions_refl|];split;[apply preserved_refl|apply lframe_refl].
 - assert (Index:0<=Z.of_nat n<8) by lia.
   destruct (exec_elements_taptweak_beta_aux_iteration e le xs ys m bs bt bx (Z.of_nat n)
    Index ST SX SB TX TB XB Global Const State NP I PX PT Table Bounds FreeS FreeT FreeX Init)
    as (m1 & Body & Table1 & Last & PX1 & PT1 & FreeS1 & FreeT1 & FreeX1 & Init1 & Keep1 & RO1 & Frame1).
   rewrite Nat2Z.id in Last.
   assert (Prefix1:beta_aux_prefix m1 bx xs (S n)).
   { eapply (elements_taptweak_beta_aux_extends_prefix m m1 bt bx xs n);[congruence|exact XB|exact Prefix|exact Last|exact Frame1]. }
   set (le1:=PTree.set _i (Vint (Int.repr (Z.of_nat n+1))) (beta_aux_temps le bx bt)).
   assert (Temps:forall id,id<>_i -> id<>_t'30 -> id<>_t'31 -> le1!id=le!id).
   { intros id NI N30 N31;unfold le1;rewrite PTree.gso by congruence;
     apply beta_aux_temps_other;assumption. }
   assert (Index1:le1!_i=Some (Vint (Int.repr (Z.of_nat (S n))))).
   { unfold le1;rewrite Nat2Z.inj_succ;replace (Z.succ (Z.of_nat n)) with (Z.of_nat n+1) by lia;apply PTree.gss. }
   assert (Step:Clight2.exec_stmt elements_taptweak_ge e (beta_aux_temps le bx bt) m1 beta_aux_step E0 le1 m1 Out_normal).
   { apply exec_elements_taptweak_beta_aux_step;[exact Index|rewrite beta_aux_temps_other by discriminate;exact I]. }
   destruct (IH (S n) ltac:(lia) e le1 xs ys m1 bs bt bx ST SX SB TX TB XB Global Const
    ltac:(rewrite Temps by discriminate;exact State) ltac:(rewrite Temps by discriminate;exact NP)
    Index1 PX1 PT1 Table1 Bounds Prefix1 FreeS1 FreeT1 FreeX1 Init1)
    as (lef & mf & Rest & FinalI & FinalTemps & TableF & PrefixF & PXF & PTF & FreeSF & FreeTF & FreeXF
      & InitF & KeepF & ROF & FrameF).
   exists lef,mf;split.
   + eapply exec_elements_taptweak_beta_aux_inner_join;[exact Index|exact I|exact Body|exact Step|exact Rest].
   + split;[exact FinalI|];split.
     * intros id NI N30 N31;rewrite FinalTemps,Temps by assumption;reflexivity.
     * split;[exact TableF|];split;[exact PrefixF|];split;[exact PXF|];split;[exact PTF|];
       split;[exact FreeSF|];split;[exact FreeTF|];split;[exact FreeXF|];split;[exact InitF|];split.
       -- eapply keeps_permissions_trans;[exact Keep1|exact KeepF].
       -- split;[eapply preserved_trans;[exact RO1|exact ROF]|].
          eapply lframe_trans;[|exact FrameF];eapply lframe_implies;[exact Frame1|].
          intros b pos (NX & NT & NB) Valid;unfold elements_taptweak_beta_aux_frame;
          split;[left;exact NX|];split;[left;exact NT|left;exact NB].
Qed.

Theorem exec_elements_taptweak_beta_aux_body e le xs ys m bs bt bx :
 bs<>bt -> bs<>bx -> bs<>elements_taptweak_beta_block -> bt<>bx -> bt<>elements_taptweak_beta_block -> bx<>elements_taptweak_beta_block ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_const_beta=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) -> Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> (forall k,(k<8)%nat -> square_input_bounds (xs k)) ->
 Mem.range_perm m bs 0 24 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable -> elements_taptweak_beta_initialized m -> exists lef mf,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_auxiliary_body E0 lef mf Out_normal /\
 lef!_i=Some (Vint (Int.repr 8)) /\
 (forall id,id<>_i -> id<>_t'30 -> id<>_t'31 -> lef!id=le!id) /\
 elements_taptweak_beta_aux_final_memory m mf bs bt bx xs ys.
Proof.
 intros ST SX SB TX TB XB Global Const State NP PX PT Table Bounds FreeS FreeT FreeX Init.
 set (le0:=PTree.set _i (Vint Int.zero) le).
 destruct (exec_elements_taptweak_beta_aux_inner_from 8 0 eq_refl e le0 xs ys m bs bt bx ST SX SB TX TB XB Global Const
  ltac:(unfold le0;rewrite PTree.gso by discriminate;exact State)
  ltac:(unfold le0;rewrite PTree.gso by discriminate;exact NP)
  ltac:(unfold le0;apply PTree.gss) PX PT Table Bounds ltac:(intros k Bound;lia) FreeS FreeT FreeX Init)
  as (lef & mf & Inner & I & Other & Memory).
 exists lef,mf;split.
 - rewrite beta_aux_body_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le0) (m1:=m);
   [apply exec_Sset;constructor|exact Inner].
 - split;[exact I|];split;[|exact Memory].
   intros id NI N30 N31;rewrite Other by assumption;unfold le0;rewrite PTree.gso by congruence;reflexivity.
Qed.

Lemma exec_elements_taptweak_beta_aux_outer_done e le m : le!_np=Some (Vlong Int64.one) -> le!_no=Some (Vlong Int64.one) ->
 Clight2.exec_stmt elements_taptweak_ge e le m beta_aux_outer E0 le m Out_normal.
Proof.
 intros NP No;rewrite beta_aux_outer_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
 exact (eval_elements_taptweak_beta_aux_outer_guard e le m true NP No).
Qed.

Theorem exec_elements_taptweak_beta_auxiliary_one e le xs ys m bs bt bx :
 bs<>bt -> bs<>bx -> bs<>elements_taptweak_beta_block -> bt<>bx -> bt<>elements_taptweak_beta_block -> bx<>elements_taptweak_beta_block ->
 e!_secp256k1_fe_mul=None -> e!_secp256k1_const_beta=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_no=Some (Vlong Int64.one) ->
 Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) -> Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> (forall k,(k<8)%nat -> square_input_bounds (xs k)) ->
 Mem.range_perm m bs 0 24 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable -> elements_taptweak_beta_initialized m -> exists lef mf,
 Clight2.exec_stmt elements_taptweak_ge e le m generator_auxiliary_statement E0 lef mf Out_normal /\
 lef!_np=Some (Vlong Int64.one) /\ lef!_i=Some (Vint (Int.repr 8)) /\
 (forall id,id<>_np -> id<>_i -> id<>_t'30 -> id<>_t'31 -> lef!id=le!id) /\
 elements_taptweak_beta_aux_final_memory m mf bs bt bx xs ys /\
 (forall k,(k<8)%nat -> square_input_bounds (beta_aux_values xs k)) /\
 (forall k,(k<8)%nat -> rescale_field_output (beta_aux_values xs k)=
   @literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))).
Proof.
 intros ST SX SB TX TB XB Global Const State No PX PT Table Bounds FreeS FreeT FreeX Init.
 set (le0:=PTree.set _np (Vlong Int64.zero) le).
 destruct (exec_elements_taptweak_beta_aux_body e le0 xs ys m bs bt bx ST SX SB TX TB XB Global Const
  ltac:(unfold le0;rewrite PTree.gso by discriminate;exact State)
  ltac:(unfold le0;apply PTree.gss) PX PT Table Bounds FreeS FreeT FreeX Init)
  as (le1 & mf & Body & I & Other & Memory).
 assert (NP1:le1!_np=Some (Vlong Int64.zero)).
 { rewrite Other by discriminate;unfold le0;apply PTree.gss. }
 assert (No1:le1!_no=Some (Vlong Int64.one)).
 { rewrite Other by discriminate;unfold le0;rewrite PTree.gso by discriminate;exact No. }
 set (lef:=PTree.set _np (Vlong Int64.one) le1).
 assert (NPF:lef!_np=Some (Vlong Int64.one)) by apply PTree.gss.
 assert (NoF:lef!_no=Some (Vlong Int64.one)).
 { unfold lef;rewrite PTree.gso by discriminate;exact No1. }
 assert (Loop:Clight2.exec_stmt elements_taptweak_ge e le0 m beta_aux_outer E0 lef mf Out_normal).
 { rewrite beta_aux_outer_source.
   eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (le1:=le1) (m1:=mf)
    (le2:=lef) (m2:=mf) (out1:=Out_normal).
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le0) (m1:=m).
     + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[|reflexivity|constructor].
       apply (eval_elements_taptweak_beta_aux_outer_guard e le0 m false);[unfold le0;apply PTree.gss|].
       unfold le0;rewrite PTree.gso by discriminate;exact No.
     + exact Body.
   - constructor.
   - exact (exec_elements_taptweak_beta_aux_outer_step e le1 mf NP1).
   - pose proof (exec_elements_taptweak_beta_aux_outer_done e lef mf NPF NoF) as Done;rewrite beta_aux_outer_source in Done;exact Done. }
 exists lef,mf;split.
 - rewrite beta_aux_statement_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le0) (m1:=m);
   [apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity]|exact Loop].
 - split;[exact NPF|];split;[unfold lef;rewrite PTree.gso by discriminate;exact I|];split.
   + intros id NNP NI N30 N31;unfold lef;rewrite PTree.gso by congruence;rewrite Other by assumption;
     unfold le0;rewrite PTree.gso by congruence;reflexivity.
   + split;[exact Memory|];split;intros k Bound;unfold beta_aux_values.
     * exact (proj2 (point_mul_value_and_bounds (xs k) beta_digits (Bounds k Bound) beta_slice_bounds)).
     * apply beta_slice_literal;apply Bounds;exact Bound.
Qed.
Theorem exec_elements_taptweak_auxiliary_empty e le m : le!_no=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_auxiliary_statement E0
  (PTree.set _np (Vlong Int64.zero) le) m Out_normal.
Proof.
 intro No;rewrite generator_auxiliary_statement_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _np (Vlong Int64.zero) le).
 - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
 - eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
   eapply exec_Sseq_2;[|discriminate].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Ebinop.
   + apply eval_Etempvar;apply PTree.gss.
   + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact No.
   + reflexivity.
Qed.

