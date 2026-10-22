(** Complete original ge_set_xo_var call and both private allocations/frees.
    Actual limb results are retained for the subsequent literal writer bridge. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_multiply_normalize_bridge C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_field_read_preservation C.jet_secp_root_chain_numeric C.jet_secp_root_check
 C.jet_secp_rescale_literal C.jet_secp_decompress_literal C.jet_secp_decompress_numeric
 C.jet_secp_decompress_prefix C.jet_secp_decompress_body.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge decompress_body_y decompress_body_return.

Definition decompress_helper_env b2 b3 :=
 PTree.set _x3 (b3,curve_fe_type) (PTree.set _x2 (b2,curve_fe_type) empty_env).
Definition decompress_helper_temps bx br (odd : bool) :=
 PTree.set _odd (Vint (if odd then Int.one else Int.zero))
 (PTree.set _x (Vptr bx Ptrofs.zero)
 (PTree.set _r (Vptr br Ptrofs.zero) (create_undef_temps (fn_temps f_secp256k1_ge_set_xo_var)))).

Lemma decompress_helper_entry m m1 mi bx br b2 b3 (odd : bool) :
 Mem.alloc m 0 40=(m1,b2) -> Mem.alloc m1 0 40=(mi,b3) ->
 function_entry2 secp_ge f_secp256k1_ge_set_xo_var
  [Vptr br Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (if odd then Int.one else Int.zero)] m
  (decompress_helper_env b2 b3) (decompress_helper_temps bx br odd) mi.
Proof.
 intros A1 A2;assert (Ok : fn_okb f_secp256k1_ge_set_xo_var=true) by reflexivity.
 destruct (fn_okb_true _ Ok) as (HN1 & HN2 & HD);constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
 eapply alloc_variables_cons with (m1:=m1) (b1:=b2);[exact A1|].
 eapply alloc_variables_cons with (m1:=mi) (b1:=b3);[exact A2|constructor].
Qed.
Lemma decompress_helper_blocks b2 b3 :
 blocks_of_env secp_ge (decompress_helper_env b2 b3)=[(b2,0,40);(b3,0,40)].
Proof. reflexivity. Qed.

Theorem eval_decompress_function w (x : Ty.tySem (Word 8)) (odd : bool) m bx br :
 bx<>br -> root_words_match w x -> fe_at m bx 0 (words5 w) ->
 Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xo_var)
  [Vptr br Ptrofs.zero;Vptr bx Ptrofs.zero;Vint (if odd then Int.one else Int.zero)] E0 mf
  (Vint (decompress_body_return w)) /\
 fe_at mf br 0 (words5 w) /\ fe_at mf br 40 (decompress_body_y w odd) /\
 Mem.load Mint32 mf br 80=Some (Vint Int.zero) /\
 @literal_y_from_x Alg.CoreFunSem x=(if root_check_flag (decompress_root_words w)
  then inr (rescale_field_output (root_chain_candidate (decompress_root_words w))) else inl tt) /\
 Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
 lframe (fun b _=>b<>bx /\ b<>br) m mf.
Proof.
 intros XR Match Field XF RF.
 assert (VX : Mem.valid_block m bx) by (eapply Mem.perm_valid_block;apply (XF 0);lia).
 assert (VR : Mem.valid_block m br) by (eapply Mem.perm_valid_block;apply (RF 0);lia).
 destruct (Mem.alloc m 0 40) as (m1 & b2) eqn:A1.
 destruct (Mem.alloc m1 0 40) as (mi & b3) eqn:A2.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ A1) as Fresh2.
 pose proof (Mem.fresh_block_alloc _ _ _ _ _ A2) as Fresh3.
 assert (V2 : Mem.valid_block m1 b2) by (eapply Mem.valid_new_block;exact A1).
 assert (Pairs : bx<>b2 /\ br<>b2 /\ bx<>b3 /\ br<>b3 /\ b2<>b3).
 { repeat split;intro Same;subst;first [apply Fresh2;assumption|apply Fresh3;assumption|
    apply Fresh3;eapply Mem.valid_block_alloc;[exact A1|assumption]]. }
 destruct Pairs as (X2 & R2 & X3 & R3 & N23).
 assert (Sep : NoDup [bx;br;b2;b3]).
 { repeat rewrite NoDup_cons_iff;cbn [In];repeat split;try apply NoDup_nil;intuition congruence. }
 assert (FrameA : lframe (fun _ _=>True) m mi).
 { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
 pose proof (field_at_lframe m mi bx 0 _ _ Field FrameA ltac:(intros;exact Logic.I)) as FI.
 pose proof (curve_keep_free _ m mi bx 40 ltac:(lia) XF FrameA ltac:(intros;exact Logic.I)) as XFI.
 pose proof (curve_keep_free _ m mi br 88 ltac:(lia) RF FrameA ltac:(intros;exact Logic.I)) as RFI.
 assert (F2I : Mem.range_perm mi b2 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact A2|eapply Mem.perm_alloc_2;eassumption]. }
 assert (F3I : Mem.range_perm mi b3 0 40 Cur Freeable).
 { intros pos Range;eapply Mem.perm_alloc_2;eassumption. }
 destruct (exec_decompress_body_owned (decompress_helper_env b2 b3) (decompress_helper_temps bx br odd)
  mi bx br b2 b3 w x odd eq_refl eq_refl eq_refl eq_refl eq_refl
  eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl Sep Match FI XFI RFI F2I F3I)
  as (mo & Body & RX & RY & Finite & Literal & XFO & RFO & F2O & F3O & FrameB).
 destruct (free_list_exists [(b2,0,40);(b3,0,40)] mo) as (mf & Free & Unchanged).
 - cbn;repeat constructor;cbn;intuition congruence.
 - intros b lo hi Hin;cbn [In] in Hin.
   destruct Hin as [Hin | [Hin | Hin]];try contradiction;inversion Hin;subst;assumption.
 - assert (FrameF : lframe (fun b _=>b<>b2 /\ b<>b3) mo mf).
   { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
     intros b pos [N2 N3] _;cbn;intuition congruence. }
   assert (RXF : fe_at mf br 0 (words5 w)).
   { eapply field_at_lframe;[exact RX|exact FrameF|];intros;split;assumption. }
   assert (RYF : fe_at mf br 40 (decompress_body_y w odd)).
   { eapply field_at_lframe;[exact RY|exact FrameF|];intros;split;assumption. }
   assert (FiniteF : Mem.load Mint32 mf br 80=Some (Vint Int.zero)).
   { rewrite (proj1 FrameF Mint32 br 80 ltac:(eapply Mem.perm_valid_block;apply (RFO 0);lia)
      ltac:(intros;split;assumption));exact Finite. }
   assert (XFF : Mem.range_perm mf bx 0 40 Cur Freeable).
   { eapply curve_keep_free;[lia|exact XFO|exact FrameF|];intros;split;assumption. }
   assert (RFF : Mem.range_perm mf br 0 88 Cur Freeable).
   { eapply curve_keep_free;[lia|exact RFO|exact FrameF|];intros;split;assumption. }
   assert (Old : forall b, Mem.valid_block m b -> b<>b2 /\ b<>b3).
   { intros b VB;split;intro Same;subst b.
     - apply Fresh2;exact VB.
     - apply Fresh3;eapply Mem.valid_block_alloc;[exact A1|exact VB]. }
   assert (FrameOld : lframe (fun b _=>Mem.valid_block m b /\ b<>bx /\ b<>br) m mf).
   { eapply lframe_trans;[eapply lframe_implies;[exact FrameA|];intros;exact Logic.I|].
     eapply lframe_trans.
     - eapply lframe_implies;[exact FrameB|];intros b pos [VB [NX NR]] _.
       destruct (Old b VB);repeat split;assumption.
     - eapply lframe_implies;[exact FrameF|];intros b pos [VB _] _;apply Old;exact VB. }
   exists mf;split.
   + eapply eval_funcall_internal with (e:=decompress_helper_env b2 b3)
      (le1:=decompress_helper_temps bx br odd)
      (le2:=decompress_body_temps (decompress_helper_temps bx br odd) w) (m1:=mi) (m2:=mo)
      (out:=Out_return (Some (Vint (decompress_body_return w),tint))).
     * eapply decompress_helper_entry;eassumption.
     * exact Body.
     * split;[discriminate|reflexivity].
     * rewrite decompress_helper_blocks;exact Free.
   + split;[exact RXF|];split;[exact RYF|];split;[exact FiniteF|];split;[exact Literal|].
     split;[exact XFF|];split;[exact RFF|].
     eapply lframe_implies;[exact FrameOld|];intros b pos HP VB;split;assumption.
Qed.
