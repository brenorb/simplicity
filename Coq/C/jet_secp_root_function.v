(** Original square-root helper environment and function entry. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_secp_curve_statements C.jet_secp_fe_nv C.jet_secp_square_columns
 C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_root_chain_owned C.jet_secp_root_chain_numeric C.jet_secp_root_check C.jet_secp_root_suffix.
Require Import Simplicity.Ty Simplicity.Word.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge root_chain_candidate.
Definition root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt := 
 PTree.set _t1 (bt,curve_fe_type) 
  (PTree.set _x223 (b223,curve_fe_type) 
  (PTree.set _x220 (b220,curve_fe_type) 
  (PTree.set _x176 (b176,curve_fe_type) 
  (PTree.set _x88 (b88,curve_fe_type) 
  (PTree.set _x44 (b44,curve_fe_type) 
  (PTree.set _x22 (b22,curve_fe_type) 
  (PTree.set _x11 (b11,curve_fe_type) 
  (PTree.set _x9 (b9,curve_fe_type) 
  (PTree.set _x6 (b6,curve_fe_type) 
  (PTree.set _x3 (b3,curve_fe_type) 
  (PTree.set _x2 (b2,curve_fe_type) (empty_env)))))))))))).
Definition root_helper_bindings b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt : list (ident*block) := [(_x2,b2);(_x3,b3);(_x6,b6);(_x9,b9);(_x11,b11);(_x22,b22);(_x44,b44);(_x88,b88);(_x176,b176);(_x220,b220);(_x223,b223);(_t1,bt)].
Definition root_entry_temps br ba := PTree.set _a (Vptr ba Ptrofs.zero)
 (PTree.set _r (Vptr br Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_fe_sqrt_var))).
Lemma root_function_ok : fn_okb f_secp256k1_fe_sqrt_var=true.
Proof. reflexivity. Qed.
Lemma root_function_entry m m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 mi br ba b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt :
 Mem.alloc m 0 40=(m1,b2) ->
 Mem.alloc m1 0 40=(m2,b3) ->
 Mem.alloc m2 0 40=(m3,b6) ->
 Mem.alloc m3 0 40=(m4,b9) ->
 Mem.alloc m4 0 40=(m5,b11) ->
 Mem.alloc m5 0 40=(m6,b22) ->
 Mem.alloc m6 0 40=(m7,b44) ->
 Mem.alloc m7 0 40=(m8,b88) ->
 Mem.alloc m8 0 40=(m9,b176) ->
 Mem.alloc m9 0 40=(m10,b220) ->
 Mem.alloc m10 0 40=(m11,b223) ->
 Mem.alloc m11 0 40=(mi,bt) ->
 function_entry2 secp_ge f_secp256k1_fe_sqrt_var [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] m
 (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) (root_entry_temps br ba) mi.
Proof.
 intros A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12;destruct (fn_okb_true _ root_function_ok) as (HN1 & HN2 & HD).
 constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=m1) (b1:=b2);[exact A1|].
 eapply alloc_variables_cons with (m1:=m2) (b1:=b3);[exact A2|].
 eapply alloc_variables_cons with (m1:=m3) (b1:=b6);[exact A3|].
 eapply alloc_variables_cons with (m1:=m4) (b1:=b9);[exact A4|].
 eapply alloc_variables_cons with (m1:=m5) (b1:=b11);[exact A5|].
 eapply alloc_variables_cons with (m1:=m6) (b1:=b22);[exact A6|].
 eapply alloc_variables_cons with (m1:=m7) (b1:=b44);[exact A7|].
 eapply alloc_variables_cons with (m1:=m8) (b1:=b88);[exact A8|].
 eapply alloc_variables_cons with (m1:=m9) (b1:=b176);[exact A9|].
 eapply alloc_variables_cons with (m1:=m10) (b1:=b220);[exact A10|].
 eapply alloc_variables_cons with (m1:=m11) (b1:=b223);[exact A11|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=bt);[exact A12|constructor].
Qed.

Lemma root_helper_binding b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt id b :
 In id root_private_ids -> (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt)!id=Some (b,curve_fe_type) ->
 In (id,b) (root_helper_bindings b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt).
Proof.
 intros HI HB;cbn [root_private_ids In] in HI.
 repeat destruct HI as [<-|HI];try contradiction.
 all: cbn [root_helper_env PTree.set PTree.get] in HB;injection HB as <-.
 all: unfold root_helper_bindings;repeat (first [left;reflexivity|right]).
Qed.
Lemma root_helper_member b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt id b :
 In id root_private_ids -> (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt)!id=Some (b,curve_fe_type) ->
 In b [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt].
Proof.
 intros HI HB;pose proof (root_helper_binding b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt id b HI HB) as HP.
 exact (in_map snd _ _ HP).
Qed.
Lemma root_bindings_distinct (bindings : list (ident*block)) :
 NoDup (map snd bindings) -> forall i j bi bj,
 In (i,bi) bindings -> In (j,bj) bindings -> i<>j -> bi<>bj.
Proof.
 induction bindings as [|[id b] tail IH];intros ND i j bi bj HI HJ NE HE;[contradiction|].
 inversion ND as [|v vs NB NT];subst v vs;subst bj.
 destruct HI as [HI|HI],HJ as [HJ|HJ].
 - inversion HI;inversion HJ;subst;contradiction.
 - inversion HI;subst;apply NB;exact (in_map snd _ _ HJ).
 - inversion HJ;subst;apply NB;exact (in_map snd _ _ HI).
 - exact (IH NT i j bi bi HI HJ NE eq_refl).
Qed.
Lemma root_helper_separated b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt :
 NoDup [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt] -> root_locals_separated (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt).
Proof.
 intros ND i j bi bj HI HJ EI EJ NE.
 exact (root_bindings_distinct (root_helper_bindings b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) ND i j bi bj
   (root_helper_binding b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt i bi HI EI)
   (root_helper_binding b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt j bj HJ EJ) NE).
Qed.
Lemma root_helper_owned b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt m :
 (forall b, In b [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt] -> Mem.range_perm m b 0 40 Cur Freeable) ->
 root_locals_owned (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) m.
Proof.
 intros Free id HI;cbn [root_private_ids In] in HI;repeat destruct HI as [<-|HI];try contradiction.
 all: eexists;split;[reflexivity|apply Free;repeat (first [left;reflexivity|right])].
Qed.
Lemma root_helper_outside b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt b :
 (forall other,In other [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt] -> b<>other) ->
 root_chain_frame (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) b 0.
Proof.
 intros HO id HI HE;apply (HO b);[|reflexivity].
 exact (root_helper_member b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt id b HI HE).
Qed.


Lemma root_function_blocks b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt :
 blocks_of_env secp_ge (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt)=[(b88,0,40);(b44,0,40);(b220,0,40);(b22,0,40);(b223,0,40);(b2,0,40);(b6,0,40);(b11,0,40);(b176,0,40);(b9,0,40);(b3,0,40);(bt,0,40)].
Proof. reflexivity. Qed.

Lemma root_helper_binding_values b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt :
 Forall (fun p : ident*block => In (fst p) root_private_ids /\
   (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt)!(fst p)=Some (snd p,curve_fe_type))
 (root_helper_bindings b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt).
Proof.
 apply Forall_forall;intros [id b] HI;cbn [root_helper_bindings In] in HI.
 repeat destruct HI as [HI|HI];try contradiction;inversion HI;subst id b;split.
 all: try reflexivity.
 all: unfold root_private_ids;repeat (first [left;reflexivity|right]).
Qed.
Lemma root_helper_free b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt m :
 root_locals_owned (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) m ->
 forall b, In b [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt] -> Mem.range_perm m b 0 40 Cur Freeable.
Proof.
 intros Owned b HB;change (In b (map snd (root_helper_bindings b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt))) in HB.
 apply in_map_iff in HB;destruct HB as [[id bi] [HE HP]];cbn in HE;subst bi.
 pose proof (proj1 (Forall_forall _ _) (root_helper_binding_values b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) (id,b) HP) as [ID EB].
 cbn [fst snd] in ID,EB.
 destruct (Owned id ID) as (b' & EB' & FB);rewrite EB in EB';injection EB' as <-;exact FB.
Qed.

Local Ltac root_allocated_valid := first [assumption |
 match goal with Alloc : Mem.alloc _ _ _=(?mm,?bb) |- Mem.valid_block ?mm ?bb =>
   eapply Mem.valid_new_block;exact Alloc end |
 match goal with Alloc : Mem.alloc _ _ _=(?mm,_) |- Mem.valid_block ?mm _ =>
   eapply Mem.valid_block_alloc;[exact Alloc|root_allocated_valid] end].
Local Ltac root_allocated_distinct := first [assumption |
 match goal with Alloc : Mem.alloc _ _ _=(_,?bb) |- ?ba<>?bb =>
   let HE := fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite <-HE;root_allocated_valid end |
 match goal with Alloc : Mem.alloc _ _ _=(_,?ba) |- ?ba<>?bb =>
   let HE := fresh "HE" in intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ Alloc);rewrite HE;root_allocated_valid end].
Local Ltac root_allocated_perm Bound := first [
 match goal with Alloc : Mem.alloc _ _ _=(?mm,?bb) |- Mem.perm ?mm ?bb _ _ _ =>
   eapply Mem.perm_alloc_2;[exact Alloc|exact Bound] end |
 match goal with Alloc : Mem.alloc _ _ _=(?mm,_) |- Mem.perm ?mm _ _ _ _ =>
   eapply Mem.perm_alloc_1;[exact Alloc|root_allocated_perm Bound] end].
Local Ltac root_allocated_frame :=
 lazymatch goal with |- lframe _ ?ma ?mb =>
 tryif constr_eq ma mb then apply lframe_refl else
 match goal with Alloc : Mem.alloc ma _ _=(?mi,_) |- _ =>
   eapply lframe_trans with (m2:=mi);
     [apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc|root_allocated_frame] end end.
Local Ltac root_separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HS : _ /\ _ |- _ => destruct HS end;
 repeat match goal with HS : ~(?P \/ ?Q) |- _ =>
   let HP := fresh "Sep" in let HQ := fresh "Sep" in
   assert (HP : ~P) by (intro;apply HS;left;assumption);
   assert (HQ : ~Q) by (intro;apply HS;right;assumption);clear HS end.

Theorem eval_root_function w (x : Ty.tySem (Word 8)) m br ba :
 ba<>br -> root_words_match w x -> fe_at m ba 0 (words5 w) ->
 Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m br 0 40 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqrt_var)
   [Vptr br Ptrofs.zero;Vptr ba Ptrofs.zero] E0 mf
   (Vint (if root_check_flag w then Int.one else Int.zero)) /\
 fe_at mf br 0 (words5 (root_chain_candidate w)) /\
 Mem.range_perm mf ba 0 40 Cur Freeable /\ Mem.range_perm mf br 0 40 Cur Freeable /\
 lframe (fun b _=>b<>ba /\ b<>br) m mf.
Proof.
 intros AR Match A FA FR.
 assert (HVA : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (FA 0);lia).
 assert (HVR : Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (FR 0);lia).
 destruct (Mem.alloc m 0 40) as (m1 & b2) eqn:A1.
 destruct (Mem.alloc m1 0 40) as (m2 & b3) eqn:A2.
 destruct (Mem.alloc m2 0 40) as (m3 & b6) eqn:A3.
 destruct (Mem.alloc m3 0 40) as (m4 & b9) eqn:A4.
 destruct (Mem.alloc m4 0 40) as (m5 & b11) eqn:A5.
 destruct (Mem.alloc m5 0 40) as (m6 & b22) eqn:A6.
 destruct (Mem.alloc m6 0 40) as (m7 & b44) eqn:A7.
 destruct (Mem.alloc m7 0 40) as (m8 & b88) eqn:A8.
 destruct (Mem.alloc m8 0 40) as (m9 & b176) eqn:A9.
 destruct (Mem.alloc m9 0 40) as (m10 & b220) eqn:A10.
 destruct (Mem.alloc m10 0 40) as (m11 & b223) eqn:A11.
 destruct (Mem.alloc m11 0 40) as (mi & bt) eqn:A12.
 assert (Sep : NoDup [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt]).
 { repeat rewrite NoDup_cons_iff;repeat rewrite not_in_cons;
   repeat split;try apply NoDup_nil;try apply in_nil;root_allocated_distinct. }
 assert (Old : forall b, Mem.valid_block m b -> forall other,In other [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt] -> b<>other).
 { intros b HV other HI;cbn [In] in HI;repeat destruct HI as [<-|HI];try contradiction;root_allocated_distinct. }
 assert (FAlloc : lframe (fun _ _=>True) m mi) by root_allocated_frame.
 assert (OwnedI : root_locals_owned (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) mi).
 { apply root_helper_owned;intros b HI;cbn [In] in HI;repeat destruct HI as [<-|HI];try contradiction.
   all: intros pos HP;root_allocated_perm HP. }
 assert (SepI : root_locals_separated (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt)) by (apply root_helper_separated;exact Sep).
 assert (OutsideA : root_chain_frame (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) ba 0)
   by (apply root_helper_outside;exact (Old ba HVA)).
 assert (OutsideR : root_chain_frame (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) br 0)
   by (apply root_helper_outside;exact (Old br HVR)).
 pose proof (field_at_lframe m mi ba 0 _ _ A FAlloc ltac:(intros;exact I)) as AI.
 pose proof (curve_keep_free _ m mi ba 40 ltac:(lia) FA FAlloc ltac:(intros;exact I)) as FAI.
 pose proof (curve_keep_free _ m mi br 40 ltac:(lia) FR FAlloc ltac:(intros;exact I)) as FRI.
 destruct (exec_root_complete_body (root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt) (root_entry_temps br ba) mi ba br w x
   SepI OwnedI OutsideA OutsideR AR eq_refl eq_refl eq_refl eq_refl eq_refl Match AI FAI FRI)
   as (mo & lef & Body & OwnedO & RO & FAO & FRO & FrameB).
 pose proof Sep as Sep0;root_separate_blocks Sep0.
 destruct (free_list_exists [(b88,0,40);(b44,0,40);(b220,0,40);(b22,0,40);(b223,0,40);(b2,0,40);(b6,0,40);(b11,0,40);(b176,0,40);(b9,0,40);(b3,0,40);(bt,0,40)] mo) as (mf & Free & Unchanged).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Hin;cbn [In] in Hin;repeat destruct Hin as [Hin|Hin];try contradiction;
     inversion Hin;subst b lo hi;apply (root_helper_free b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt mo OwnedO);
     repeat (first [left;reflexivity|right]).
 - assert (FFree : lframe (fun b _=>forall other,In other [b2;b3;b6;b9;b11;b22;b44;b88;b176;b220;b223;bt] -> b<>other) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos HO _ Hin;apply (HO b);[|reflexivity].
     cbn [map fst snd In] in Hin |- *;tauto. }
   pose proof (field_at_lframe mo mf br 0 _ _ RO FFree ltac:(intros;exact (Old br HVR))) as RF.
   pose proof (curve_keep_free _ mo mf ba 40 ltac:(lia) FAO FFree ltac:(intros;exact (Old ba HVA))) as FAF.
   pose proof (curve_keep_free _ mo mf br 40 ltac:(lia) FRO FFree ltac:(intros;exact (Old br HVR))) as FRF.
   assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>ba /\ b<>br) m mf).
   { eapply lframe_trans.
     - eapply lframe_implies;[exact FAlloc|];intros;exact I.
     - eapply lframe_trans.
       + eapply lframe_implies;[exact FrameB|];intros b pos [HV [NA NR]] _;split.
         * apply root_helper_outside;exact (Old b HV).
         * split;assumption.
       + eapply lframe_implies;[exact FFree|];intros b pos [HV _] _;exact (Old b HV). }
   assert (Frame : lframe (fun b _=>b<>ba /\ b<>br) m mf).
   { eapply lframe_implies;[exact FrameOld|];intros b pos HP HV;split;assumption. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=root_helper_env b2 b3 b6 b9 b11 b22 b44 b88 b176 b220 b223 bt)
       (le1:=root_entry_temps br ba) (le2:=lef) (m1:=mi) (m2:=mo)
       (out:=Out_return (Some (Vint (if root_check_flag w then Int.one else Int.zero),tint))).
     * eapply root_function_entry;eassumption.
     * exact Body.
     * split;[discriminate|reflexivity].
     * rewrite root_function_blocks;exact Free.
   + split;[exact RF|];split;[exact FAF|];split;assumption.
Qed.
