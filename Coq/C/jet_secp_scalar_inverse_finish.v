(** Execute the actual inverse core's sign load, scalar-order normalization
    and copy-back. This is a terminal-state suffix, not the inverse loop or
    the complete scalar-invert jet. Reclaim the core's five actual locals. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_de
 C.jet_secp_modinv_var_finish C.jet_secp_modinv_var_free C.jet_secp_modinv_fg_index.
Require Import C.jet_secp_scalar_normalize62 C.jet_secp_modinfo_scalar_global C.jet_secp_scalar_inverse_caller
 C.jet_secp_canonical_scalar C.jet_secp_modinv_normalize62_exec C.jet_secp_modinv_normalize62_modulus
 C.jet_secp_modinv_normalize62_words C.jet_secp_signed62_numeric C.jet_secp_signed62_assign
 C.jet_secp_fe_nv C.jet_secp_multiply_normalize_bridge C.jet_secp_field_read_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Definition scalar_inv_finish_words len d f :=
 norm62_machine d modinfo_scalar_limb (f (len-1)%nat).
Definition scalar_inv_finish_temps len (f : nat -> int64) le :=
 PTree.set _t'2 (Vlong (f (len-1)%nat)) le.

Lemma eval_scalar_inv_finish_sign len f beta e le m : (0<len<=5)%nat ->
 ematch beta (snd inv_start_alloc) e -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 fe_at m (blk beta 4) 0 (words5 f) ->
 eval_expr secp_ge e le m (inv_local_index _f (inv_len_sub 1)) (Vlong(f (len-1)%nat)).
Proof.
 intros Len Env Length Field.
 assert (Index : ((len-1)<5)%nat) by lia.
 assert (At : nth_error (words5 f) (len-1)%nat=Some(f (len-1)%nat)).
 { remember (len-1)%nat as i;destruct i as [|[|[|[|[|i]]]]];try lia;reflexivity. }
 pose proof ((proj2 (proj2 (proj2 (proj2 Field)))) _ _ At) as Load.
 rewrite Z.add_0_l in Load.
 apply (eval_inv_local_load e le m _f (blk beta 4) (inv_len_sub 1) (len-1)%nat (f (len-1)%nat));
 [exact Index|reflexivity|exact (proj1 (Env _f))|apply eval_inv_len_sub;[lia|exact Length]|exact Load].
Qed.

(** Initial storage and bounds are internal loop-exit obligations. The
    normalize call, its output and the subsequent copy execution are derived. *)
Theorem exec_scalar_inv_finish len d f beta e le m : (0<len<=5)%nat ->
 ematch beta (snd inv_start_alloc) e ->
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 le!_modinfo=Some(Vptr scalar_inv_modinfo_block Ptrofs.zero) ->
 le!_x=Some(Vptr (blk beta 0) Ptrofs.zero) ->
 modnorm62_limb_bounds d ->
 -2*canonical_group_order<norm62_value_z 4 (fun i=>Int64.signed(d i))<canonical_group_order ->
 fe_at m (blk beta 2) 0 (words5 d) -> fe_at m (blk beta 4) 0 (words5 f) ->
 Mem.range_perm m (blk beta 2) 0 40 Cur Freeable ->
 Mem.range_perm m (blk beta 0) 0 40 Cur Freeable ->
 blk beta 2<>scalar_inv_modinfo_block -> blk beta 0<>blk beta 2 ->
 blk beta 0<>scalar_inv_modinfo_block -> modinfo_scalar_global_rep m -> exists mf,
 Clight2.exec_stmt secp_ge e le m inv_finish E0 (scalar_inv_finish_temps len f le) mf Out_normal /\
 fe_at mf (blk beta 0) 0 (words5(scalar_inv_finish_words len d f)) /\
 fe_at mf (blk beta 2) 0 (words5(scalar_inv_finish_words len d f)) /\
 signed62_normalized(scalar_inv_finish_words len d f) /\
 signed62_unsigned_value(scalar_inv_finish_words len d f)=
  ((if Int64.lt (f (len-1)%nat) Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed(d i))) mod canonical_group_order /\
 Mem.range_perm mf (blk beta 0) 0 40 Cur Freeable /\
 Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable /\ modinfo_scalar_global_rep mf /\
 lframe (fun b ofs=>norm62_outside (blk beta 2) scalar_inv_modinfo_block b ofs /\ b<>blk beta 0) m mf.
Proof.
 intros Len Env Length Modinfo X Bounds Value DField FField FreeD FreeX DG XD XG Global.
 destruct (eval_scalar_norm62_numeric d (f (len-1)%nat) m (blk beta 2)
   Bounds Value DG DField FreeD Global)
   as (mn & NormCall & DNorm & Normal & Numeric & DFree & GlobalN & NFrame).
 assert (FreeXN : Mem.range_perm mn (blk beta 0) 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FreeX|exact NFrame|];intros;split;left;assumption. }
 destruct (eval_signed62_assign_from_storage (scalar_inv_finish_words len d f)
   mn (blk beta 0) (blk beta 2) XD FreeXN DNorm DFree)
   as (mf & CopyCall & XField & DFieldF & XFreeF & DFreeF & CFrame).
 set (lf:=scalar_inv_finish_temps len f le).
 assert (SignLoad : Clight2.exec_stmt secp_ge e le m inv_finish_sign_load E0 lf m Out_normal).
 { apply exec_Sset;exact (eval_scalar_inv_finish_sign len f beta e le m Len Env Length FField). }
 assert (NormExec : Clight2.exec_stmt secp_ge e lf m inv_finish_normalize E0 lf mn Out_normal).
 { unfold inv_finish_normalize;eapply exec_curve_call with (result:=None) (v:=Vundef).
   - unfold secp_pure;repeat(first[left;reflexivity|right]).
   - exact (proj1 (Env _secp256k1_modinv64_normalize_62)).
   - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact(proj1(Env _d))|reflexivity|].
     eapply eval_Econs;[apply eval_Etempvar;apply PTree.gss|reflexivity|].
     eapply eval_Econs.
     + apply eval_Etempvar;unfold lf,scalar_inv_finish_temps;
       rewrite PTree.gso by discriminate;exact Modinfo.
     + reflexivity.
     + constructor.
   - exact NormCall. }
 assert (CopyExec : Clight2.exec_stmt secp_ge e lf mn inv_finish_copy E0 lf mf Out_normal).
 { unfold inv_finish_copy;eapply exec_curve_call with (result:=None) (v:=Vundef).
   - unfold secp_pure;repeat(first[left;reflexivity|right]).
   - exact (proj1 (Env _secp256k1_modinv64_signed62_assign)).
   - apply inv_finish_copy_arguments;[exact Env|].
     unfold lf,scalar_inv_finish_temps;rewrite PTree.gso by discriminate;exact X.
   - exact CopyCall. }
 assert (GlobalF : modinfo_scalar_global_rep mf).
 { eapply modinfo_scalar_global_lframe;[exact GlobalN|exact CFrame|];intros;congruence. }
 exists mf;split.
 - rewrite inv_finish_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=mn);[|exact CopyExec].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=m);[exact SignLoad|exact NormExec].
 - split;[exact XField|];split;[exact DFieldF|];split;[exact Normal|];split;[exact Numeric|].
   split;[exact XFreeF|];split;[exact DFreeF|];split;[exact GlobalF|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact NFrame|];intros b ofs Both _;exact(proj1 Both).
   + eapply lframe_implies;[exact CFrame|];intros b ofs Both _;exact(proj2 Both).
Qed.

(** Reuse the same actual local-list/size derivation as the field caller.
    The memory/trajectory facts at loop exit remain to be established. *)
Theorem exec_scalar_inv_finish_and_free len d f beta e le m :
 (0<len<=5)%nat -> length beta=7%nat -> inv_loop_distinct beta ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=scalar_inv_modinfo_block ->
 le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 le!_modinfo=Some(Vptr scalar_inv_modinfo_block Ptrofs.zero) ->
 le!_x=Some(Vptr (blk beta 0) Ptrofs.zero) ->
 modnorm62_limb_bounds d ->
 -2*canonical_group_order<norm62_value_z 4 (fun i=>Int64.signed(d i))<canonical_group_order ->
 fe_at m (blk beta 2) 0 (words5 d) -> fe_at m (blk beta 4) 0 (words5 f) ->
 Mem.range_perm m (blk beta 0) 0 40 Cur Freeable ->
 (forall r,(2<=r<7)%nat -> Mem.range_perm m (blk beta r) 0 (inv_local_size r) Cur Freeable) ->
 modinfo_scalar_global_rep m -> exists mf mr,
 Clight2.exec_stmt secp_ge e le m inv_finish E0 (scalar_inv_finish_temps len f le) mf Out_normal /\
 Mem.free_list mf (blocks_of_env secp_ge e)=Some mr /\
 fe_at mr (blk beta 0) 0 (words5(scalar_inv_finish_words len d f)) /\
 signed62_normalized(scalar_inv_finish_words len d f) /\
 signed62_unsigned_value(scalar_inv_finish_words len d f)=
  ((if Int64.lt (f (len-1)%nat) Int64.zero then -1 else 1)*
   norm62_value_z 4 (fun i=>Int64.signed(d i))) mod canonical_group_order /\
 Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ modinfo_scalar_global_rep mr /\
 lframe (fun b ofs=>norm62_outside (blk beta 2) scalar_inv_modinfo_block b ofs /\
   b<>blk beta 0 /\ inv_free_outside beta b) m mr.
Proof.
 intros Len Size Distinct Env Block Length Modinfo X Bounds Value DField FField FreeX Owned Global.
 assert (DG : blk beta 2<>scalar_inv_modinfo_block) by (rewrite <-Block;apply Distinct;lia).
 assert (XD : blk beta 0<>blk beta 2) by (apply Distinct;lia).
 assert (XG : blk beta 0<>scalar_inv_modinfo_block) by (rewrite <-Block;apply Distinct;lia).
 pose proof (Owned 2%nat ltac:(lia)) as FreeD.
 change (Mem.range_perm m (blk beta 2) 0 40 Cur Freeable) in FreeD.
 destruct (exec_scalar_inv_finish len d f beta e le m Len Env Length Modinfo X
   Bounds Value DField FField FreeD FreeX DG XD XG Global)
   as (mf & Run & XField & DFieldF & Normal & Numeric & XFree & DFree & GlobalF & Frame).
 assert (FreeLocals : forall r,(2<=r<7)%nat ->
   Mem.range_perm mf (blk beta r) 0 (inv_local_size r) Cur Freeable).
 { intros r R;destruct (Nat.eq_dec r 2) as [->|Other];[exact DFree|].
   eapply curve_keep_free;[unfold inv_local_size;destruct(Nat.eqb r 6);lia|apply Owned;exact R|exact Frame|].
   intros pos;split.
   - split;left;[apply Distinct;lia|rewrite <-Block;apply Distinct;lia].
   - apply Distinct;lia. }
 destruct (inv_free_env_blocks_structural beta e Size Distinct Env) as (Blocks & NoRepeat).
 destruct (free_list_exists (blocks_of_env secp_ge e) mf NoRepeat) as (mr & Free & Unchanged).
 - intros b lo hi Member;destruct (Blocks b lo hi Member) as (r & R & -> & -> & ->).
   apply FreeLocals;exact R.
 - assert (FFrame : lframe (fun b _=>inv_free_outside beta b) mf mr).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b ofs Outside Valid Member;apply in_map_iff in Member.
     destruct Member as ([[br lo] hi] & Eq & Member);cbn in Eq;subst br.
     destruct (Blocks b lo hi Member) as (r & R & Eq & _);apply (Outside r R);exact Eq. }
   assert (XOutside : inv_free_outside beta (blk beta 0)) by (intros r R;apply Distinct;lia).
   assert (GOutside : inv_free_outside beta scalar_inv_modinfo_block).
   { rewrite <-Block;intros r R;apply Distinct;lia. }
   assert (XFieldR : fe_at mr (blk beta 0) 0 (words5(scalar_inv_finish_words len d f))).
   { eapply field_at_lframe;[exact XField|exact FFrame|];intros;exact XOutside. }
   assert (XFreeR : Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable).
   { eapply field_freeable_lframe;[exact XField|exact XFree|exact FFrame|];intros;exact XOutside. }
   assert (GlobalR : modinfo_scalar_global_rep mr).
   { eapply modinfo_scalar_global_lframe;[exact GlobalF|exact FFrame|];intros;exact GOutside. }
   exists mf,mr;split;[exact Run|];split;[exact Free|];split;[exact XFieldR|].
   split;[exact Normal|];split;[exact Numeric|];split;[exact XFreeR|];split;[exact GlobalR|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact Frame|];intros b ofs (N & NX & O) _;split;assumption.
   + eapply lframe_implies;[exact FFrame|];intros b ofs (N & NX & O) _;exact O.
Qed.
