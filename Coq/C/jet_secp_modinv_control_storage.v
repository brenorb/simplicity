(** Actual inverse shortening from storage, independent of the unused
    modulus/global representation. Reuses the checked address, condition
    and prefix execution proofs; no C execution is assumed. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
 C.jet_secp_modinv_var_zero C.jet_secp_modinv_var_shorten C.jet_secp_modinv_var_post C.jet_secp_modinv_fg_index.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem exec_inv_shorten_array_storage len high w b e le m : (2<=len<=5)%nat ->
 e!(inv_shorten_id high)=Some(b,fg_s62_type) -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 le!(inv_shorten_top high)=Some(Vlong(w(len-1)%nat)) ->
 Mem.range_perm m b 0 40 Cur Freeable ->
 (forall i,(i<5)%nat -> Mem.load Mint64 m b (8*Z.of_nat i)=Some(Vlong(w i))) -> exists mf,
 Clight2.exec_stmt secp_ge e le m (inv_shorten_array_step high) E0
  (PTree.set (inv_shorten_tmp high) (Vlong(w(len-2)%nat)) le) mf Out_normal /\
 (forall i,(i<5)%nat -> Mem.load Mint64 mf b (8*Z.of_nat i)=Some(Vlong(inv_shorten_words len w i))) /\
 Mem.range_perm mf b 0 40 Cur Freeable /\ lframe(fun bx _=>bx<>b) m mf.
Proof.
 intros Len Env Length Top Free Loads.
 assert(Access:Mem.valid_access m Mint64 b (8*Z.of_nat(len-2)) Writable).
 { split.
   - intros pos Range;eapply Mem.perm_implies;[apply Free;change(8*Z.of_nat(len-2)<=pos<8*Z.of_nat(len-2)+8) in Range;lia|constructor].
   - change(8|8*Z.of_nat(len-2));exists(Z.of_nat(len-2));ring. }
 destruct(Mem.valid_access_store m Mint64 b (8*Z.of_nat(len-2))
  (Vlong(inv_shorten_limb (w(len-2)%nat) (w(len-1)%nat))) Access) as(mf & Store).
 exists mf;split.
 - rewrite inv_shorten_array_source;eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set (inv_shorten_tmp high) (Vlong(w(len-2)%nat)) le).
   + apply exec_Sset;eapply eval_inv_local_load with(j:=(len-2)%nat);
     [lia|reflexivity|exact Env|apply eval_inv_len_sub;[lia|exact Length]|apply Loads;lia].
   + eapply exec_Sassign with(loc:=b) (ofs:=Ptrofs.repr(8*Z.of_nat(len-2))) (bf:=Full)
      (v2:=Vlong(inv_shorten_limb (w(len-2)%nat) (w(len-1)%nat)))
      (v:=Vlong(inv_shorten_limb (w(len-2)%nat) (w(len-1)%nat))).
     * apply eval_inv_local_index;[lia|reflexivity|exact Env|].
       apply eval_inv_len_sub;[lia|rewrite PTree.gso;[exact Length|destruct high;discriminate]].
     * unfold inv_shorten_limb;eapply eval_Ebinop.
       -- apply eval_Etempvar;apply PTree.gss.
       -- eapply eval_Ebinop.
          ++ eapply eval_Ecast;[apply eval_Etempvar;rewrite PTree.gso;[exact Top|destruct high;discriminate]|reflexivity].
          ++ constructor.
          ++ reflexivity.
       -- reflexivity.
     * reflexivity.
     * apply assign_loc_value with(chunk:=Mint64);[reflexivity|].
       unfold Mem.storev;rewrite Ptrofs.unsigned_repr;
        [exact Store|change Ptrofs.max_unsigned with(2^64-1);lia].
 - split.
   + intros i I;unfold inv_shorten_words;destruct(Nat.eqb_spec i (len-2)) as[->|Ne].
     * exact(Mem.load_store_same _ _ _ _ _ _ Store).
     * rewrite(Mem.load_store_other _ _ _ _ _ _ Store);[apply Loads;exact I|].
       right;change(8*Z.of_nat i+8<=8*Z.of_nat(len-2) \/ 8*Z.of_nat(len-2)+8<=8*Z.of_nat i);lia.
   + split.
     * intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Free;exact Range].
     * apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
       intros pos Range Outside;contradiction.
Qed.

Theorem exec_inv_shortening_storage len rho bf bg e le m : (0<len<=5)%nat -> bf<>bg ->
 e!_f=Some(bf,fg_s62_type) -> e!_g=Some(bg,fg_s62_type) -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 Mem.range_perm m bf 0 40 Cur Freeable -> Mem.range_perm m bg 0 40 Cur Freeable ->
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 m (if high then bg else bf) (8*Z.of_nat i)=
  Some(Vlong(inv_control_word rho high i))) -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_shortening E0 lef mf Out_normal /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (if high then bg else bf) (8*Z.of_nat i)=
  Some(Vlong(inv_control_short_word len rho high i))) /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\ Mem.range_perm mf bg 0 40 Cur Freeable /\
 lef!_len=Some(Vint(Int.repr(Z.of_nat(inv_shortened_length len rho)))) /\
 (0<inv_shortened_length len rho<=5)%nat /\ inv_shorten_temp_frame le lef /\
 lframe(fun b _=>b<>bf /\ b<>bg) m mf.
Proof.
 intros Bound Sep F G Length FF FG Loads.
 set(f:=inv_control_word rho false (len-1)).
 set(g:=inv_control_word rho true (len-1)).
 set(lp:=inv_short_prefix_env le len f g).
 pose proof(exec_inv_short_prefix len f g bf bg e le m Bound F G Length
  (Loads false (len-1)%nat ltac:(lia)) (Loads true (len-1)%nat ltac:(lia))) as Prefix.
 assert(LP:lp!_len=Some(Vint(Int.repr(Z.of_nat len)))) by(unfold lp;rewrite inv_short_prefix_len;exact Length).
 assert(Cond:lp!_cond=Some(Vlong(inv_shorten_cond len f g))) by apply PTree.gss.
 pose proof(eval_inv_long_zero e lp m _cond (inv_shorten_cond len f g) Cond) as Check.
 change(eval_expr secp_ge e lp m
  (Ebinop Oeq (Etempvar _cond tlong) (Econst_int Int.zero tint) tint)
  (Vint(if inv_control_shrink len rho then Int.one else Int.zero))) in Check.
 destruct(inv_control_shrink len rho) eqn:Shrink.
 - assert(Can:inv_shorten_guard len f g=true) by exact Shrink.
   destruct(proj1(inv_shorten_guard_correct len f g Bound) Can) as(Len2 & SignF & SignG).
   destruct(exec_inv_shorten_array_storage len false (inv_control_word rho false) bf e lp m ltac:(lia)
    F LP (inv_short_prefix_top le len f g false) FF (Loads false)) as(m1 & CopyF & OutF & FreeF & FrameF).
   set(l1:=PTree.set _t'4 (Vlong(inv_control_word rho false (len-2))) lp).
   assert(L1:l1!_len=Some(Vint(Int.repr(Z.of_nat len)))).
   { unfold l1;rewrite PTree.gso by discriminate;exact LP. }
   assert(G1:l1!_gn=Some(Vlong g)).
   { unfold l1;rewrite PTree.gso by discriminate;exact(inv_short_prefix_top le len f g true). }
   assert(LoadsG:forall i,(i<5)%nat -> Mem.load Mint64 m1 bg (8*Z.of_nat i)=Some(Vlong(inv_control_word rho true i))).
   { intros i I;rewrite(proj1 FrameF).
     - exact(Loads true i I).
     - eapply Mem.perm_valid_block;apply(FG 0);lia.
     - intros;congruence. }
   assert(FreeG:Mem.range_perm m1 bg 0 40 Cur Freeable).
   { intros pos Range;eapply(proj1(proj2 FrameF));[eapply Mem.perm_valid_block;apply(FG 0);lia|congruence|apply FG;exact Range]. }
   destruct(exec_inv_shorten_array_storage len true (inv_control_word rho true) bg e l1 m1 ltac:(lia)
    G L1 G1 FreeG LoadsG) as(mf & CopyG & OutG & FreeGFinal & FrameG).
   set(l2:=PTree.set _t'3 (Vlong(inv_control_word rho true (len-2))) l1).
   set(lf:=PTree.set _len (Vint(Int.repr(Z.of_nat(len-1)))) l2).
   assert(FreeFFinal:Mem.range_perm mf bf 0 40 Cur Freeable).
   { intros pos Range;eapply(proj1(proj2 FrameG));[eapply Mem.perm_valid_block;apply(FreeF 0);lia|exact Sep|apply FreeF;exact Range]. }
   exists lf,mf;split.
   + rewrite inv_shorten_source;eapply exec_statement_prefix_then_last;[exact Prefix|].
     eapply exec_Sifthenelse with(v1:=Vint Int.one) (b:=true);[exact Check|reflexivity|].
     rewrite inv_shorten_body_source;eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (le1:=l1) (m1:=m1);[exact CopyF|].
     eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (le1:=l2) (m1:=mf);[exact CopyG|].
     rewrite inv_shorten_len_source;apply exec_Sset;apply eval_inv_len_sub;[lia|].
     unfold l2;rewrite PTree.gso by discriminate;exact L1.
   + split.
     * intros high i I;unfold inv_control_short_word;rewrite Shrink;destruct high.
       -- exact(OutG i I).
       -- rewrite(proj1 FrameG).
          ++ exact(OutF i I).
          ++ eapply Mem.perm_valid_block;apply(FreeF 0);lia.
          ++ intros;exact Sep.
     * split;[exact FreeFFinal|];split;[exact FreeGFinal|];split.
       -- unfold inv_shortened_length;rewrite Shrink;apply PTree.gss.
       -- split;[unfold inv_shortened_length;rewrite Shrink;lia|];split.
          ++ intros id Outside;unfold lf,l2,l1;rewrite !PTree.gso;
             try(apply inv_short_prefix_frame;exact Outside);
             unfold inv_shorten_modified in Outside;cbn [In] in Outside;intuition congruence.
          ++ eapply lframe_trans;[eapply lframe_implies;[exact FrameF|]|eapply lframe_implies;[exact FrameG|]];
             intros b pos [Fout Gout] Valid;assumption.
 - exists lp,m;split.
   + rewrite inv_shorten_source;eapply exec_statement_prefix_then_last;[exact Prefix|].
     eapply exec_Sifthenelse with(v1:=Vint Int.zero) (b:=false);[exact Check|reflexivity|constructor].
   + split.
     * intros high i I;unfold inv_control_short_word;rewrite Shrink;exact(Loads high i I).
     * split;[exact FF|];split;[exact FG|];split.
       -- unfold inv_shortened_length;rewrite Shrink;exact LP.
       -- split;[unfold inv_shortened_length;rewrite Shrink;exact Bound|];split;[apply inv_short_prefix_frame|apply lframe_refl].
Qed.

(** Includes the short-circuited break path and the actual two-store path.
    It assumes only initial storage/permissions, not decoded limb bounds. *)
Theorem exec_inv_post_storage len rho bf bg e le m : (0<len<=5)%nat -> bf<>bg ->
 e!_f=Some(bf,fg_s62_type) -> e!_g=Some(bg,fg_s62_type) -> le!_len=Some(Vint(Int.repr(Z.of_nat len))) ->
 Mem.range_perm m bf 0 40 Cur Freeable -> Mem.range_perm m bg 0 40 Cur Freeable ->
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 m (if high then bg else bf) (8*Z.of_nat i)=
  Some(Vlong(inv_control_word rho high i))) -> exists lef mf,
 Clight2.exec_stmt secp_ge e le m inv_post_control E0 lef mf (inv_post_out len rho) /\
 (forall (high : bool) i,(i<5)%nat -> Mem.load Mint64 mf (if high then bg else bf) (8*Z.of_nat i)=
  Some(Vlong(inv_post_word len rho high i))) /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\ Mem.range_perm mf bg 0 40 Cur Freeable /\
 lef!_len=Some(Vint(Int.repr(Z.of_nat(inv_post_length len rho)))) /\
 (0<inv_post_length len rho<=5)%nat /\ inv_post_temp_frame le lef /\
 lframe(fun b _=>b<>bf /\ b<>bg) m mf.
Proof.
 intros Bound Sep F G Length FF FG Loads.
 destruct(exec_inv_zero_from_loads len (inv_control_word rho true) e le m bg Bound G Length
  ltac:(intros i I;exact(Loads true i ltac:(lia)))) as(lz & Zero & ZFrame).
 assert(ZLen:lz!_len=Some(Vint(Int.repr(Z.of_nat len)))).
 { rewrite(inv_test_frame_length le lz ZFrame);exact Length. }
 change(Clight2.exec_stmt secp_ge e le m inv_zero_test E0 lz m (inv_post_out len rho)) in Zero.
 unfold inv_post_out in Zero|-*;destruct(inv_control_stops len rho) eqn:Stops.
 - exists lz,m;split.
   + unfold inv_post_control;eapply exec_Sseq_2;[exact Zero|discriminate].
   + split.
     * intros high i I;unfold inv_post_word;rewrite Stops;exact(Loads high i I).
     * split;[exact FF|];split;[exact FG|];split.
       -- unfold inv_post_length;rewrite Stops;exact ZLen.
       -- split;[unfold inv_post_length;rewrite Stops;exact Bound|];split;[apply inv_post_test_frame;exact ZFrame|apply lframe_refl].
 - destruct(exec_inv_shortening_storage len rho bf bg e lz m Bound Sep F G ZLen FF FG Loads)
    as(lef & mf & Short & Out & FFinal & GFinal & Len & Range & SFrame & Frame).
   exists lef,mf;split.
   + unfold inv_post_control;eapply exec_Sseq_1 with(t1:=E0) (t2:=E0) (le1:=lz) (m1:=m);eassumption.
   + split.
     * intros high i I;unfold inv_post_word;rewrite Stops;exact(Out high i I).
     * split;[exact FFinal|];split;[exact GFinal|];split.
       -- unfold inv_post_length;rewrite Stops;exact Len.
       -- split;[unfold inv_post_length;rewrite Stops;exact Range|];split;[eapply inv_post_frames;eassumption|exact Frame].
Qed.
