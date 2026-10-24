(** Original field-inverse finishing statements, on the actual field global. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem C.jet_sx_u64_transport.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_copies C.jet_secp_modinv_var_zero.
Require Import C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg.
Require Import C.jet_secp_modinv_normalize62_exec C.jet_secp_modinv_normalize62_numeric.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_signed62_assign C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_signed62_numeric C.jet_secp_modinv_de_numeric.
Require Import C.jet_secp_local_regions C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_modinv_normalize62_words.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_finish := match inv_after_ready with Ssequence _ rest=>rest | _=>Sskip end.
Definition inv_finish_sign_load := Sset _t'2 (inv_local_index _f (inv_len_sub 1)).
Definition inv_finish_normalize := curve_call _secp256k1_modinv64_normalize_62
 f_secp256k1_modinv64_normalize_62 None
 [inv_s62_address _d;Etempvar _t'2 tlong;inv_metadata_arg].
Definition inv_finish_copy := curve_call _secp256k1_modinv64_signed62_assign
 f_secp256k1_modinv64_signed62_assign None
 [Etempvar _x (tptr fg_s62_type);inv_s62_address _d].
Lemma inv_finish_source : inv_finish=Ssequence (Ssequence inv_finish_sign_load inv_finish_normalize) inv_finish_copy.
Proof. reflexivity. Qed.
Definition inv_finish_sign len (rho : nat->int64) := rho (15+(len-1))%nat.
Definition inv_finish_d (rho : nat->int64) i := rho (5+i)%nat.
Definition inv_finish_words len rho := norm62_machine (inv_finish_d rho) modinfo_fe_limb (inv_finish_sign len rho).

Lemma inv_finish_global rho beta m : rep rho beta inv_loop_regs m ->
 blk beta 1=modinfo_fe_block -> bas beta 1=0 -> modinfo_fe_global_rep m.
Proof.
 intros Rep Block Base;pose proof (rep_region _ _ _ _ 1 _ Rep eq_refl) as Region.
 assert (Loads : forall i w,nth_error modinfo_fe_words i=Some w ->
  Mem.load Mint64 m modinfo_fe_block (8*Z.of_nat i)=Some (Vlong w)).
 { intros i w At;rewrite <-Block.
   pose proof (region_load rho beta m 1 _ (8*Z.of_nat i) Mint64 (XLc w) Region
    ltac:(change (In (mkcell (8*Z.of_nat i) Mint64 (Some (XLc w))) (u64_cells 0 (map XLc modinfo_fe_words)));
      replace (8*Z.of_nat i) with (0+8*Z.of_nat i) by lia;apply u64_cells_nth;
      rewrite nth_error_map,At;reflexivity)) as Load.
   rewrite Base,Z.add_0_l in Load;exact Load. }
 split;[rewrite <-Block;exact (proj1 (proj2 Region))|];split;[|exact Loads].
 intros pos Range.
 assert (Cases : 0<=pos<8 \/ 8<=pos<16 \/ 16<=pos<24 \/ 24<=pos<32 \/ 32<=pos<40 \/ 40<=pos<48) by lia.
 destruct Cases as [Case|[Case|[Case|[Case|[Case|Case]]]]];
 [pose proof (Loads 0%nat _ eq_refl) as Load|pose proof (Loads 1%nat _ eq_refl) as Load|
  pose proof (Loads 2%nat _ eq_refl) as Load|pose proof (Loads 3%nat _ eq_refl) as Load|
  pose proof (Loads 4%nat _ eq_refl) as Load|pose proof (Loads 5%nat _ eq_refl) as Load];
 apply Mem.load_valid_access in Load;apply (proj1 Load);exact Case.
Qed.
Lemma inv_finish_storage rho beta m : rep rho beta inv_loop_regs m ->
 fe_at m (blk beta 2) 0 (words5 (inv_finish_d rho)).
Proof.
 intro Rep;pose proof (rep_region _ _ _ _ 2 _ Rep eq_refl) as Region.
 destruct (rep_free_region _ _ _ _ 2 40 Rep ltac:(cbn [inv_loop_regs length];lia) eq_refl) as (Base & Free).
 rewrite <-Base;apply (u64_region_fe_at rho beta m 2 (inv_finish_d rho) (Some 40)).
 eapply region_u64_transport with (rho:=rho) (beta:=beta) (r:=2%nat)
  (xs:=vars5 5) (ys:=map XL (words5 (inv_finish_d rho)));try reflexivity;exact Region.
Qed.
Lemma eval_inv_finish_sign len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 eval_expr secp_ge e le m (inv_local_index _f (inv_len_sub 1)) (Vlong (inv_finish_sign len rho)).
Proof.
 intros Len Rep Env Length.
 assert (Base : bas beta 4=0) by (eapply rep_owned_region_base_zero;[exact Rep|reflexivity|reflexivity]).
 pose proof (xload_u64_defined_sound _ _ _ _ _ _ _ Rep (inv_fg_load_expr false (len-1)%nat ltac:(lia))) as Load.
 change (Mem.load Mint64 m (blk beta 4) (bas beta 4+8*Z.of_nat (len-1))=
  Some (Vlong (inv_finish_sign len rho))) in Load;rewrite Base,Z.add_0_l in Load.
 apply (eval_inv_local_load e le m _f (blk beta 4) (inv_len_sub 1) (len-1)%nat (inv_finish_sign len rho));
  [lia|reflexivity|exact (proj1 (Env _f))|apply eval_inv_len_sub;[lia|exact Length]|exact Load].
Qed.

Lemma inv_finish_d_word rho i : (i<5)%nat -> inv_finish_d rho i=de62_array (inv_de_rho rho) false i.
Proof. destruct i as [|[|[|[|[|i]]]]];intro I;try lia;reflexivity. Qed.
Lemma inv_finish_d_value rho : norm62_value_z 4 (fun i=>Int64.signed (inv_finish_d rho i))=
 de62_input_value (inv_de_rho rho) false.
Proof.
 unfold de62_input_value;apply norm62_value_ext;intros i I;rewrite inv_finish_d_word by lia;reflexivity.
Qed.
Lemma inv_finish_d_bounds rho : de62_state_bounds (inv_de_rho rho) -> norm62_limb_bounds (inv_finish_d rho).
Proof. intros (Limbs & _ ) i I;rewrite inv_finish_d_word by exact I;apply Limbs;exact I. Qed.
Lemma inv_finish_norm_arguments rho beta e le m sign : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=modinfo_fe_block -> bas beta 1=0 ->
 le!_t'2=Some (Vlong sign) -> le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 eval_exprlist secp_ge e le m [inv_s62_address _d;Etempvar _t'2 tlong;inv_metadata_arg]
 (type_of_params (fn_params f_secp256k1_modinv64_normalize_62))
 [Vptr (blk beta 2) Ptrofs.zero;Vlong sign;Vptr modinfo_fe_block Ptrofs.zero].
Proof.
 intros Rep Env Block Base Sign Modinfo.
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _d))|reflexivity|].
 eapply eval_Econs;[apply eval_Etempvar;exact Sign|reflexivity|].
 eapply eval_Econs;[apply eval_Etempvar;rewrite Block,Base in Modinfo;exact Modinfo|reflexivity|constructor].
Qed.
Lemma inv_finish_copy_arguments beta e le m : ematch beta (snd inv_start_alloc) e ->
 le!_x=Some (Vptr (blk beta 0) Ptrofs.zero) ->
 eval_exprlist secp_ge e le m [Etempvar _x (tptr fg_s62_type);inv_s62_address _d]
 (type_of_params (fn_params f_secp256k1_modinv64_signed62_assign))
 [Vptr (blk beta 0) Ptrofs.zero;Vptr (blk beta 2) Ptrofs.zero].
Proof.
 intros Env X;eapply eval_Econs;[apply eval_Etempvar;exact X|reflexivity|].
 eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact (proj1 (Env _d))|reflexivity|constructor].
Qed.

Definition inv_finish_temps len rho le := PTree.set _t'2 (Vlong (inv_finish_sign len rho)) le.
Theorem exec_inv_finish len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=modinfo_fe_block -> bas beta 1=0 ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 le!_x=Some (Vptr (blk beta 0) Ptrofs.zero) -> de62_state_bounds (inv_de_rho rho) -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_finish E0 (inv_finish_temps len rho le) mf Out_normal /\
 fe_at mf (blk beta 0) 0 (words5 (inv_finish_words len rho)) /\
 fe_at mf (blk beta 2) 0 (words5 (inv_finish_words len rho)) /\
 signed62_normalized (inv_finish_words len rho) /\
 signed62_unsigned_value (inv_finish_words len rho)=
  ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
   de62_input_value (inv_de_rho rho) false) mod feP /\
 Mem.range_perm mf (blk beta 0) 0 40 Cur Freeable /\
 Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable /\ modinfo_fe_global_rep mf /\
 lframe (fun b ofs=>norm62_outside (blk beta 2) modinfo_fe_block b ofs /\ b<>blk beta 0) m mf.
Proof.
 intros Len Rep Env Block Base Length Modinfo X Bounds.
 pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 assert (DG : blk beta 2<>modinfo_fe_block) by (rewrite <-Block;apply Distinct;lia).
 assert (XD : blk beta 0<>blk beta 2) by (apply Distinct;lia).
 assert (XG : blk beta 0<>modinfo_fe_block) by (rewrite <-Block;apply Distinct;lia).
 destruct (rep_free_region _ _ _ _ 0 40 Rep ltac:(cbn [inv_loop_regs length];lia) eq_refl) as (BaseX & FreeX).
 destruct (rep_free_region _ _ _ _ 2 40 Rep ltac:(cbn [inv_loop_regs length];lia) eq_refl) as (BaseD & FreeD).
 assert (Range : -2*feP<norm62_value_z 4 (fun i=>Int64.signed (inv_finish_d rho i))<feP).
 { rewrite inv_finish_d_value;exact (proj2 Bounds false). }
 destruct (eval_field_norm62_numeric (inv_finish_d rho) (inv_finish_sign len rho) m (blk beta 2)
  (inv_finish_d_bounds rho Bounds) Range DG (inv_finish_storage rho beta m Rep) FreeD
  (inv_finish_global rho beta m Rep Block Base))
  as (mn & NormCall & DField & Normalized & Numeric & DFree & Global & NFrame).
 assert (XFreeN : Mem.range_perm mn (blk beta 0) 0 40 Cur Freeable).
 { intros pos P;eapply (proj1 (proj2 NFrame)).
   - exact (proj1 (proj2 (rep_region _ _ _ _ 0 _ Rep eq_refl))).
   - split;left;assumption.
   - apply FreeX;exact P. }
 destruct (eval_signed62_assign_from_storage (inv_finish_words len rho) mn (blk beta 0) (blk beta 2)
  XD XFreeN DField DFree) as (mf & CopyCall & XField & DFieldF & XFreeF & DFreeF & CFrame).
 set (lf:=inv_finish_temps len rho le).
 assert (SignLoad : Clight2.exec_stmt secp_ge e le m inv_finish_sign_load E0 lf m Out_normal).
 { apply exec_Sset;exact (eval_inv_finish_sign len rho beta e le m Len Rep Env Length). }
 assert (NormExec : Clight2.exec_stmt secp_ge e lf m inv_finish_normalize E0 lf mn Out_normal).
 { unfold inv_finish_normalize;eapply exec_curve_call with (result:=None) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact (proj1 (Env _secp256k1_modinv64_normalize_62)).
   - eapply inv_finish_norm_arguments;[exact Rep|exact Env|exact Block|exact Base| |].
     + apply PTree.gss.
     + unfold lf,inv_finish_temps;rewrite PTree.gso by discriminate;exact Modinfo.
   - exact NormCall. }
 assert (CopyExec : Clight2.exec_stmt secp_ge e lf mn inv_finish_copy E0 lf mf Out_normal).
 { unfold inv_finish_copy;eapply exec_curve_call with (result:=None) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact (proj1 (Env _secp256k1_modinv64_signed62_assign)).
   - apply inv_finish_copy_arguments;[exact Env|].
     unfold lf,inv_finish_temps;rewrite PTree.gso by discriminate;exact X.
   - exact CopyCall. }
 assert (GlobalF : modinfo_fe_global_rep mf).
 { eapply modinfo_fe_global_lframe;[exact Global|exact CFrame|intros pos;congruence]. }
 exists mf;split.
 - rewrite inv_finish_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=mn);[|exact CopyExec].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=m);[exact SignLoad|exact NormExec].
 - split;[exact XField|];split;[exact DFieldF|];split;[exact Normalized|];split.
   + unfold inv_finish_words;rewrite Numeric,inv_finish_d_value;reflexivity.
   + split;[exact XFreeF|];split;[exact DFreeF|];split;[exact GlobalF|].
     eapply lframe_trans.
     * eapply lframe_implies;[exact NFrame|intros b ofs Both _;exact (proj1 Both)].
     * eapply lframe_implies;[exact CFrame|intros b ofs Both _;exact (proj2 Both)].
Qed.
