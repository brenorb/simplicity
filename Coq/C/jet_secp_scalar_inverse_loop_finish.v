(** Compose the original scalar inverse loop with normalization, copy-back
    and all five frees. All finishing premises come from the proved loop.
    CTZ is still an explicit internal dependency, not a public theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word C.jet_toZ C.jet_predicate_spec.
Require Import C.extraMath C.divstep C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem
 C.jet_sx_rep C.jet_sx_u64_transport C.jet_secp_linkage C.jets_secp
 C.jet_secp_scalar_inverse_loop C.jet_secp_scalar_inverse_batch C.jet_secp_scalar_inverse_result
 C.jet_secp_scalar_inverse_finish C.jet_secp_scalar_invert_literal C.jet_secp_scalar_inverse_seed
 C.jet_secp_scalar_inverse_caller C.jet_secp_modinfo_scalar_global
 C.jet_secp_modinv_loop_modulus C.jet_secp_modinv_entry_modulus C.jet_secp_modinv_var_entry
 C.jet_secp_modinv_var_de C.jet_secp_modinv_var_fg C.jet_secp_modinv_var_tail
 C.jet_secp_modinv_var_finish C.jet_secp_modinv_var_free C.jet_secp_modinv_var_invariant
 C.jet_secp_scalar_de_ranges C.jet_secp_scalar_de_invariant C.jet_secp_scalar_normalize62
 C.jet_secp_modinv_de_numeric C.jet_secp_modinv_normalize62_words C.jet_secp_modinv_normalize62_modulus
 C.jet_secp_signed62_numeric C.jet_secp_canonical_scalar C.jet_secp_fe_nv C.jet_secp_local_regions
 C.jet_secp_u128_shift64_rep C.jet_secp_modinv_normalize62_exec C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge scalar_inv_modinfo_block.

Lemma scalar_inv_loop_array rho beta m r n : rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m ->
 nth_error (inv_mod_loop_regs modinfo_scalar_limb) r=Some(mkreg(u64_cells 0 (vars5 n)) true (Some 40)) ->
 fe_at m (blk beta r) 0 (words5(fun i=>rho(n+i)%nat)).
Proof.
 intros Rep At;pose proof(rep_region _ _ _ _ r _ Rep At) as Region.
 assert(Base:bas beta r=0) by(eapply rep_owned_region_base_zero;[exact Rep|exact At|reflexivity]).
 rewrite <-Base;apply(u64_region_fe_at rho beta m r (fun i=>rho(n+i)%nat) (Some 40)).
 eapply region_u64_transport with(rho:=rho) (beta:=beta) (r:=r) (xs:=vars5 n)
  (ys:=map XL (words5(fun i=>rho(n+i)%nat)));try reflexivity.
 - cbn [words5 vars5 map den];rewrite Nat.add_0_r;reflexivity.
 - exact Region.
Qed.

Lemma scalar_inv_loop_global rho beta m : rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m ->
 blk beta 1=scalar_inv_modinfo_block -> bas beta 1=0 -> modinfo_scalar_global_rep m.
Proof.
 intros Rep Block Base;pose proof(rep_region _ _ _ _ 1 _ Rep eq_refl) as Region.
 assert(Loads:forall i w,nth_error modinfo_scalar_words i=Some w ->
  Mem.load Mint64 m scalar_inv_modinfo_block (8*Z.of_nat i)=Some(Vlong w)).
 { intros i w At;rewrite <-Block.
   rewrite scalar_inv_start_words in Region.
   pose proof(region_load rho beta m 1 _ (8*Z.of_nat i) Mint64 (XLc w) Region
    ltac:(change(In(mkcell (8*Z.of_nat i) Mint64 (Some(XLc w))) (u64_cells 0 (map XLc modinfo_scalar_words)));
      replace(8*Z.of_nat i) with(0+8*Z.of_nat i) by lia;apply u64_cells_nth;
      rewrite nth_error_map,At;reflexivity)) as Load.
   rewrite Base,Z.add_0_l in Load;exact Load. }
 split;[rewrite <-Block;exact(proj1(proj2 Region))|];split;[|exact Loads].
 intros pos Range.
 assert(Cases:0<=pos<8 \/ 8<=pos<16 \/ 16<=pos<24 \/ 24<=pos<32 \/ 32<=pos<40 \/ 40<=pos<48) by lia.
 destruct Cases as[Case|[Case|[Case|[Case|[Case|Case]]]]];
 [pose proof(Loads 0%nat _ eq_refl) as Load|pose proof(Loads 1%nat _ eq_refl) as Load|
  pose proof(Loads 2%nat _ eq_refl) as Load|pose proof(Loads 3%nat _ eq_refl) as Load|
  pose proof(Loads 4%nat _ eq_refl) as Load|pose proof(Loads 5%nat _ eq_refl) as Load];
 apply Mem.load_valid_access in Load;apply(proj1 Load);exact Case.
Qed.

Lemma scalar_inv_loop_owned rho beta m r : rep rho beta (inv_mod_loop_regs modinfo_scalar_limb) m ->
 (2<=r<7)%nat -> Mem.range_perm m (blk beta r) 0 (inv_local_size r) Cur Freeable.
Proof.
 intros Rep R.
 assert(Owned:rfree(nth r (inv_mod_loop_regs modinfo_scalar_limb) (mkreg [] true None))=Some(inv_local_size r))
  by(destruct r as [|[|[|[|[|[|[|r]]]]]]];try lia;reflexivity).
 exact(proj2(rep_free_region rho beta (inv_mod_loop_regs modinfo_scalar_limb) m r (inv_local_size r)
  Rep ltac:(change(r<7)%nat;lia) Owned)).
Qed.

Definition scalar_inv_loop_finish_frame beta b ofs := scalar_inv_batch_frame beta b ofs /\
 norm62_outside (blk beta 2) scalar_inv_modinfo_block b ofs /\ b<>blk beta 0 /\ inv_free_outside beta b.

Theorem exec_scalar_inv_loop_finish value n beta e le m len rho :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 0<=value<canonical_group_order -> scalar_inv_loop_ready value n beta e le m len rho ->
 blk beta 1=scalar_inv_modinfo_block -> bas beta 1=0 -> le!_x=Some(Vptr(blk beta 0) Ptrofs.zero) ->
 exists words lef mf mr,
 Clight2.exec_stmt secp_ge e le m (Ssequence C.jet_secp_modinv_var_zero.inv_caller_loop inv_finish)
  E0 lef mf Out_normal /\ Mem.free_list mf (blocks_of_env secp_ge e)=Some mr /\
 fe_at mr (blk beta 0) 0 (words5 words) /\ signed62_normalized words /\
 signed62_unsigned_value words=literal_scalar_invert_numeric value /\
 (forall input:Ty.tySem(Word 8),value=@toZ (WordToZ 8) input mod canonical_group_order ->
  @fromZ (WordToZ 8) (signed62_unsigned_value words)=@literal_scalar_invert Alg.CoreFunSem input) /\
 Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ modinfo_scalar_global_rep mr /\
 lframe(scalar_inv_loop_finish_frame beta) m mr /\ readonly_preserved m mr.
Proof.
 intros CountCall Range Ready Block Base X.
 pose proof Ready as(_ & _ & Env & _ & Modinfo & _).
 destruct(exec_scalar_inv_loop CountCall value n beta e le m len rho Range Ready)
  as(nf & lenf & rhof & lf & ml & Loop & Progress &
    (Length & Rep & Eta & Len & DE & State & Link & Limbs & Capacity & Low & Zero & Stop) & Temps & Frame & LoopReadonly).
 assert(ModinfoF:lf!_modinfo=Some(Vptr scalar_inv_modinfo_block Ptrofs.zero)).
 { rewrite(Temps _modinfo) by(unfold C.jet_secp_modinv_var_post.inv_post_modified,
    C.jet_secp_modinv_var_zero.inv_test_modified,C.jet_secp_modinv_var_shorten.inv_shorten_modified;
    cbn [app In];intuition discriminate).
   rewrite Block,Base in Modinfo;exact Modinfo. }
 assert(XF:lf!_x=Some(Vptr(blk beta 0) Ptrofs.zero)).
 { rewrite(Temps _x) by(unfold C.jet_secp_modinv_var_post.inv_post_modified,
    C.jet_secp_modinv_var_zero.inv_test_modified,C.jet_secp_modinv_var_shorten.inv_shorten_modified;
    cbn [app In];intuition discriminate);exact X. }
 assert(DBounds:modnorm62_limb_bounds(inv_finish_d rhof)).
 { intros i I;rewrite inv_finish_d_word by exact I;apply(proj1 DE false i I). }
 assert(DValue: -2*canonical_group_order<norm62_value_z 4 (fun i=>Int64.signed(inv_finish_d rhof i))<canonical_group_order).
 { rewrite inv_finish_d_value;apply(proj2 DE). }
 assert(FreeX:Mem.range_perm ml (blk beta 0) 0 40 Cur Freeable).
 { exact(proj2(rep_free_region _ _ _ _ 0 40 Rep ltac:(change(0<7)%nat;lia) eq_refl)). }
 assert(LinkD:(value*norm62_value_z 4 (fun i=>Int64.signed(inv_finish_d rhof i))) mod canonical_group_order=
   norm62_value_z (lenf-1)%nat (fun i=>Int64.signed(rhof(15+i)%nat)) mod canonical_group_order).
 { rewrite inv_finish_d_value;pose proof(Link false) as L;rewrite(proj1 State) in L;exact L. }
 assert(MatchF:norm62_value_z (lenf-1)%nat (fun i=>Int64.signed(rhof(15+i)%nat))=
   f(scalar_inv_trajectory value nf)) by(symmetry;exact(proj1 State)).
 assert(LowF:forall i,(i<(lenf-1))%nat -> 0<=Int64.signed(rhof(15+i)%nat)<2^62).
 { intros i I;apply(Low false i);lia. }
 assert(ZeroD:value=0 -> norm62_value_z 4 (fun i=>Int64.signed(inv_finish_d rhof i)) mod canonical_group_order=0).
 { rewrite inv_finish_d_value;exact Zero. }
 destruct(exec_scalar_inv_finish_literal value nf lenf (inv_finish_d rhof) (fun i=>rhof(15+i)%nat) beta e lf ml
  Length (proj1 Rep) (inv_mod_loop_distinct _ _ _ _ Rep) Env Block Len ModinfoF XF DBounds DValue
  (scalar_inv_loop_array rhof beta ml 2 5 Rep eq_refl) (scalar_inv_loop_array rhof beta ml 4 15 Rep eq_refl)
  FreeX (fun r R=>scalar_inv_loop_owned rhof beta ml r Rep R) (scalar_inv_loop_global rhof beta ml Rep Block Base)
  Range LowF LinkD MatchF Stop ZeroD)
  as(mf & mr & Finish & Free & Output & Normal & Numeric & Original & Simplicity & Owned & Global & FFrame).
 exists(scalar_inv_finish_words lenf (inv_finish_d rhof) (fun i=>rhof(15+i)%nat)),
  (scalar_inv_finish_temps lenf (fun i=>rhof(15+i)%nat) lf),mf,mr;split.
 - eapply exec_Sseq_1 with(t1:=E0)(t2:=E0);[exact Loop|exact Finish].
 - split;[exact Free|];split;[exact Output|];split;[exact Normal|];split;[exact Numeric|];
   split;[exact Simplicity|];split;[exact Owned|];split;[exact Global|];split.
   + eapply lframe_trans;[eapply lframe_implies;[exact Frame|]|eapply lframe_implies;[exact FFrame|]];
     intros b ofs [LoopOutside FinishOutside] Valid;assumption.
   + eapply preserved_trans;[exact LoopReadonly|].
     eapply preserved_trans;[|eapply freelist_preserved;exact Free].
     eapply secp_closed_stmt_preserved;[exact Finish|apply(inv_env_plain beta e Env)|exact secp_closed_finish].
Qed.
