(** Free the original inverse's actual local blocks after its finishing path. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_modinv_var_entry C.jet_secp_modinv_var_de.
Require Import C.jet_secp_modinv_var_finish C.jet_secp_modinv_normalize62_exec C.jet_secp_modinfo_fe_global.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_multiply_normalize_bridge.
Require Import C.jet_secp_signed62_numeric C.jet_secp_modinv_de_numeric C.jet_secp_fe_math.
Require Import C.jet_secp_field_read_preservation.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition inv_local_size r : Z := if Nat.eqb r 6 then 32 else 40.
Definition inv_local_id r := match r with
 | 2%nat=>_d | 3%nat=>_e | 4%nat=>_f | 5%nat=>_g | _=>_t end.
Lemma inv_local_lookup id r ty : vlookup (snd inv_start_alloc) id=Some (r,ty) ->
 (2<=r<7)%nat /\ sizeof (genv_cenv secp_ge) ty=inv_local_size r /\ id=inv_local_id r.
Proof.
 cbn [inv_start_alloc snd vlookup].
 repeat match goal with |- context[if ?D then _ else _]=>let Key:=fresh "Key" in destruct D eqn:Key end;
 intro At;try discriminate;injection At as <- <-;
 repeat match goal with H : Pos.eqb _ _=true |- _=>apply Pos.eqb_eq in H end;
 subst;repeat split;try reflexivity;lia.
Qed.
Lemma inv_local_owned r : (2<=r<7)%nat ->
 rfree (nth r inv_loop_regs (mkreg [] true None))=Some (inv_local_size r).
Proof. destruct r as [|[|[|[|[|[|[|r]]]]]]];intro R;try lia;reflexivity. Qed.
Lemma inv_finish_locals_freeable rho beta m mf : rep rho beta inv_loop_regs m ->
 blk beta 1=modinfo_fe_block -> Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable ->
 lframe (fun b ofs=>norm62_outside (blk beta 2) modinfo_fe_block b ofs /\ b<>blk beta 0) m mf ->
 forall r,(2<=r<7)%nat -> Mem.range_perm mf (blk beta r) 0 (inv_local_size r) Cur Freeable.
Proof.
 intros Rep Block DFree Frame r R;destruct (Nat.eq_dec r 2) as [->|Other];[exact DFree|].
 pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 destruct (rep_free_region rho beta inv_loop_regs m r (inv_local_size r) Rep
  ltac:(change (r<7)%nat;lia) (inv_local_owned r R)) as (Base & OldFree).
 pose proof (nth_error_nth' inv_loop_regs (mkreg [] true None) (n:=r) ltac:(change (r<7)%nat;lia)) as At.
 pose proof (proj1 (proj2 (rep_region _ _ _ _ r _ Rep At))) as Valid.
 intros pos P;eapply (proj1 (proj2 Frame));[exact Valid| |apply OldFree;exact P].
 split.
 - split;left;[apply Distinct;lia|rewrite <-Block;apply Distinct;lia].
 - apply Distinct;lia.
Qed.
Theorem inv_free_env_blocks rho beta e m : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e ->
 (forall b lo hi,In (b,lo,hi) (blocks_of_env secp_ge e) ->
  exists r,(2<=r<7)%nat /\ b=blk beta r /\ lo=0 /\ hi=inv_local_size r) /\
 list_norepet (map (fun x=>fst (fst x)) (blocks_of_env secp_ge e)).
Proof.
 intros Rep Env;pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 assert (Size : length beta=7%nat) by exact (proj1 Rep).
 destruct (callee_env_blocks secp_ge beta (snd inv_start_alloc) e) as (Blocks & NoRepeat).
 - intros id1 id2 r1 r2 ty1 ty2 A B Equal.
   destruct (Nat.eq_dec r1 r2) as [Same|Ne];[exact Same|exfalso].
   destruct (inv_local_lookup _ _ _ A) as (R1 & _).
   destruct (inv_local_lookup _ _ _ B) as (R2 & _).
   apply (Distinct r1 r2 ltac:(lia) ltac:(lia) Ne);exact Equal.
 - intro id;exact (proj1 (Env id)).
 - intros id r ty At;rewrite Size;exact (proj2 (proj1 (inv_local_lookup id r ty At))).
 - intros id1 id2 r ty1 ty2 A B;rewrite (proj2 (proj2 (inv_local_lookup _ _ _ A))),
    (proj2 (proj2 (inv_local_lookup _ _ _ B)));reflexivity.
 - split;[|exact NoRepeat];intros b lo hi Member.
   destruct (Blocks b lo hi Member) as (id & r & ty & At & -> & -> & ->).
   destruct (inv_local_lookup id r ty At) as (R & Ty & Key).
   exists r;split;[exact R|];split;[reflexivity|];split;[reflexivity|exact Ty].
Qed.

Definition inv_free_outside beta b := forall r,(2<=r<7)%nat -> b<>blk beta r.
Lemma inv_free_not_listed rho beta e m b : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> inv_free_outside beta b ->
 ~In b (map (fun x=>fst (fst x)) (blocks_of_env secp_ge e)).
Proof.
 intros Rep Env Outside Member;apply in_map_iff in Member.
 destruct Member as ([[br lo] hi] & Equal & Member);cbn in Equal;subst br.
 destruct (proj1 (inv_free_env_blocks rho beta e m Rep Env) b lo hi Member) as (r & R & Eq & _).
 apply (Outside r R);exact Eq.
Qed.
Theorem inv_free_actual_locals rho beta e m mf : rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=modinfo_fe_block ->
 Mem.range_perm mf (blk beta 2) 0 40 Cur Freeable ->
 lframe (fun b ofs=>norm62_outside (blk beta 2) modinfo_fe_block b ofs /\ b<>blk beta 0) m mf ->
 exists mr,Mem.free_list mf (blocks_of_env secp_ge e)=Some mr /\
 lframe (fun b _=>inv_free_outside beta b) mf mr.
Proof.
 intros Rep Env Block DFree Frame.
 destruct (inv_free_env_blocks rho beta e m Rep Env) as (Blocks & NoRepeat).
 destruct (free_list_exists (blocks_of_env secp_ge e) mf NoRepeat) as (mr & Free & Unchanged).
 - intros b lo hi Member;destruct (Blocks b lo hi Member) as (r & R & -> & -> & ->).
   apply (inv_finish_locals_freeable rho beta m mf Rep Block DFree Frame r R).
 - exists mr;split;[exact Free|].
   eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
   intros b ofs Outside _;apply (inv_free_not_listed rho beta e m b Rep Env Outside).
Qed.

Theorem exec_inv_finish_and_free len rho beta e le m : (0<len<=5)%nat -> rep rho beta inv_loop_regs m ->
 ematch beta (snd inv_start_alloc) e -> blk beta 1=modinfo_fe_block -> bas beta 1=0 ->
 le!_len=Some (Vint (Int.repr (Z.of_nat len))) ->
 le!_modinfo=Some (Vptr (blk beta 1) (Ptrofs.repr (bas beta 1))) ->
 le!_x=Some (Vptr (blk beta 0) Ptrofs.zero) -> de62_state_bounds (inv_de_rho rho) -> exists mf mr,
 Clight2.exec_stmt secp_ge e le m inv_finish E0 (inv_finish_temps len rho le) mf Out_normal /\
 Mem.free_list mf (blocks_of_env secp_ge e)=Some mr /\
 fe_at mr (blk beta 0) 0 (words5 (inv_finish_words len rho)) /\
 signed62_normalized (inv_finish_words len rho) /\
 signed62_unsigned_value (inv_finish_words len rho)=
  ((if Int64.lt (inv_finish_sign len rho) Int64.zero then -1 else 1)*
   de62_input_value (inv_de_rho rho) false) mod feP /\
 Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable /\ modinfo_fe_global_rep mr /\
 lframe (fun b ofs=>norm62_outside (blk beta 2) modinfo_fe_block b ofs /\ b<>blk beta 0 /\
  inv_free_outside beta b) m mr.
Proof.
 intros Len Rep Env Block Base Length Modinfo X Bounds.
 destruct (exec_inv_finish len rho beta e le m Len Rep Env Block Base Length Modinfo X Bounds)
  as (mf & Exec & XField & DField & Normalized & Numeric & XFree & DFree & Global & Frame).
 destruct (inv_free_actual_locals rho beta e m mf Rep Env Block DFree Frame) as (mr & Free & FFrame).
 pose proof (inv_loop_rep_distinct rho beta m Rep) as Distinct.
 assert (XOutside : inv_free_outside beta (blk beta 0)) by (intros r R;apply Distinct;lia).
 assert (GOutside : inv_free_outside beta modinfo_fe_block).
 { rewrite <-Block;intros r R;apply Distinct;lia. }
 assert (XFieldR : fe_at mr (blk beta 0) 0 (words5 (inv_finish_words len rho))).
 { eapply field_at_lframe;[exact XField|exact FFrame|intros;exact XOutside]. }
 assert (XFreeR : Mem.range_perm mr (blk beta 0) 0 40 Cur Freeable).
 { eapply field_freeable_lframe;[exact XField|exact XFree|exact FFrame|intros;exact XOutside]. }
 assert (GlobalR : modinfo_fe_global_rep mr).
 { eapply modinfo_fe_global_lframe;[exact Global|exact FFrame|intros;exact GOutside]. }
 exists mf,mr;split;[exact Exec|];split;[exact Free|];split;[exact XFieldR|];split;[exact Normalized|].
 split;[exact Numeric|];split;[exact XFreeR|];split;[exact GlobalR|].
 eapply lframe_trans.
 - eapply lframe_implies;[exact Frame|intros b ofs (N & XN & O) _;split;assumption].
 - eapply lframe_implies;[exact FFrame|intros b ofs (N & XN & O) _;exact O].
Qed.
