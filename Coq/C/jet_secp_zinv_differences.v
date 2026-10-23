(** Actual four H/I statements after the proved zinv preparation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_weak_loose
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix
 C.jet_secp_mixed_difference C.jet_secp_zinv_shared_preparation C.jet_secp_zinv_s2
 C.jet_secp_zinv_preparation C.jet_secp_zinv_start C.jet_secp_zinv_initial_products.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words mixed_difference_words.
Definition zinv_h_words x z u inv := mixed_difference_words (weak_loose_words x) (point_mul_words u (zinv_z12_words z inv)).
Definition zinv_i_words y z v inv := mixed_difference_words
 (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv)) (weak_loose_words y).
Definition zinv_after_difference := zinv_statement_drop 4 zinv_after_s2_az.
Lemma zinv_difference_source : zinv_after_s2_az=statement_sequence mixed_difference_statements zinv_after_difference.
Proof. reflexivity. Qed.
Definition zinv_difference_frame bu bv bs bt bz baz bp ba bb bh bi bx pos :=
 zinv_start_frame bu bv bs bt bz baz bp ba bb bx pos /\ bx<>bh /\ bx<>bi.
Local Ltac separate_blocks HSep :=
 repeat rewrite NoDup_cons_iff in HSep;cbn [In] in HSep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.

Theorem exec_zinv_differences x y z u v inv e le m bp ba bb baz bz bu bv bs bt bh bi :
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi] ->
 zinv_start_fields m bp ba bb baz bz bu bv bs bt x y z u v inv ->
 zinv_start_owned m bp ba bb baz bz bu bv bs bt -> zinv_start_tight x y z u v inv ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence mixed_difference_statements Sskip) E0 le mf Out_normal /\
 zinv_start_fields mf bp ba bb baz bz bu bv bs bt x y z u v inv /\
 zinv_start_owned mf bp ba bb baz bz bu bv bs bt /\
 fe_at mf bh 0 (words5 (zinv_h_words x z u inv)) /\ fe_at mf bi 0 (words5 (zinv_i_words y z v inv)) /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 radix_value (zinv_h_words x z u inv)=4*feP-radix_value (weak_loose_words x)+radix_value (point_mul_words u (zinv_z12_words z inv)) /\
 radix_value (zinv_i_words y z v inv)=4*feP-radix_value (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv))+radix_value (weak_loose_words y) /\
 square_input_bounds (zinv_h_words x z u inv) /\ square_input_bounds (zinv_i_words y z v inv) /\
 lframe (zinv_difference_frame bu bv bs bt bz baz bp ba bb bh bi) m mf.
Proof.
 intros EH EI EU EV ES ET EN EA Sep Fields Owned Tight HF IF.
 destruct Fields as (X & Y & ZAt & U & V & I & AZ & T & U1 & U2 & S1 & S2).
 destruct Owned as (PF & AF & InvF & AZF & ZF & UF & VF & SF & TF).
 destruct Tight as (TX & TY & TAZ & TZ & TU & TS).
 separate_blocks Sep.
 assert (SepD : NoDup [bh;bi;bu;bv;bs;bt]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 destruct (exec_mixed_differences e le m bh bi bu bv bs bt
   (weak_loose_words x) (point_mul_words u (zinv_z12_words z inv)) (weak_loose_words y)
   (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv))
   EH EI EU EV ES ET EN EA SepD TX TU TY TS U1 U2 S1 S2 HF IF UF VF SF TF)
   as (mf & Call & HOut & IOut & U1Out & U2Out & S1Out & S2Out & HFree & IFree & UFree & VFree & SFree & TFree & ValueH & ValueI & BH & BI & Frame).
 assert (OutP : forall pos : Z,bp<>bh /\ bp<>bi /\ bp<>bu /\ bp<>bv /\ bp<>bs /\ bp<>bt) by (intro;repeat split;congruence).
 assert (OutA : forall pos : Z,ba<>bh /\ ba<>bi /\ ba<>bu /\ ba<>bv /\ ba<>bs /\ ba<>bt) by (intro;repeat split;congruence).
 assert (OutI : forall pos : Z,bb<>bh /\ bb<>bi /\ bb<>bu /\ bb<>bv /\ bb<>bs /\ bb<>bt) by (intro;repeat split;congruence).
 assert (OutAZ : forall pos : Z,baz<>bh /\ baz<>bi /\ baz<>bu /\ baz<>bv /\ baz<>bs /\ baz<>bt) by (intro;repeat split;congruence).
 assert (OutZ : forall pos : Z,bz<>bh /\ bz<>bi /\ bz<>bu /\ bz<>bv /\ bz<>bs /\ bz<>bt) by (intro;repeat split;congruence).
 pose proof (field_at_lframe _ _ _ _ _ _ X Frame OutP) as XF.
 pose proof (field_at_lframe _ _ _ _ _ _ Y Frame OutP) as YF.
 pose proof (field_at_lframe _ _ _ _ _ _ ZAt Frame OutP) as ZFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ U Frame OutA) as UFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ V Frame OutA) as VFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ I Frame OutI) as IFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ AZ Frame OutAZ) as AZFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ T Frame OutZ) as TFinal.
 pose proof (curve_keep_free _ _ _ _ 128 ltac:(lia) PF Frame OutP) as PFF.
 pose proof (curve_keep_free _ _ _ _ 88 ltac:(lia) AF Frame OutA) as AFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) InvF Frame OutI) as InvFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) AZF Frame OutAZ) as AZFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) ZF Frame OutZ) as ZFF.
 exists mf;split;[exact Call|];split.
 - unfold zinv_start_fields;repeat first [assumption|split].
 - split.
   + unfold zinv_start_owned;repeat first [assumption|split].
   + split;[exact HOut|];split;[exact IOut|];split;[exact HFree|];split;[exact IFree|];
     split;[exact ValueH|];split;[exact ValueI|];split;[exact BH|];split;[exact BI|].
     eapply lframe_implies;[exact Frame|].
     intros bx pos (Base & NH & NI) Valid.
     destruct Base as (NU & NV & NS & NT & NZ & NAZ & NP & NA & NB).
     repeat split;assumption.
Qed.

Definition zinv_difference_prefix := zinv_start_statements ++ mixed_difference_statements.
Lemma zinv_difference_prefix_source : zinv_finite_suffix =
 statement_sequence zinv_difference_prefix zinv_after_difference.
Proof. rewrite zinv_start_source,zinv_difference_source;reflexivity. Qed.

(** The initial H/I fields need only writable storage: the original thirteen
    statements derive their contents from the caller's six input fields. *)
Theorem exec_zinv_difference_prefix x y z u v inv e le m bp ba bb baz bz bu bv bs bt bh bi :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) -> le!_bzinv=Some (Vptr bb Ptrofs.zero) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
 e!_z12=Some (bz,curve_fe_type) -> e!_az=Some (baz,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi] ->
 (forall i,(i<5)%nat -> Int64.unsigned (x i)<=2^60) ->
 (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) ->
 square_input_bounds z -> square_input_bounds inv -> square_input_bounds u -> square_input_bounds v ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 zinv_start_owned m bp ba bb baz bz bu bv bs bt ->
 Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_difference_prefix Sskip) E0 le mf Out_normal /\
 zinv_start_fields mf bp ba bb baz bz bu bv bs bt x y z u v inv /\
 zinv_start_owned mf bp ba bb baz bz bu bv bs bt /\
 fe_at mf bh 0 (words5 (zinv_h_words x z u inv)) /\ fe_at mf bi 0 (words5 (zinv_i_words y z v inv)) /\
 Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 radix_value (zinv_h_words x z u inv)=4*feP-radix_value (weak_loose_words x)+radix_value (point_mul_words u (zinv_z12_words z inv)) /\
 radix_value (zinv_i_words y z v inv)=4*feP-radix_value (zinv_s2_words v (zinv_z12_words z inv) (zinv_az_words z inv))+radix_value (weak_loose_words y) /\
 square_input_bounds (zinv_h_words x z u inv) /\ square_input_bounds (zinv_i_words y z v inv) /\
 lframe (zinv_difference_frame bu bv bs bt bz baz bp ba bb bh bi) m mf.
Proof.
 intros HA HB HInv EU EV ES ET EZ EAZ EH EI EW EM EQ EN EA Sep BX BY BZ BInv BU BV
   X Y ZAt U V Inv Owned HF IF.
 pose proof Sep as SepAll;separate_blocks Sep.
 assert (SepStart : NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 destruct (exec_zinv_start x y z u v inv e le m bp ba bb baz bz bu bv bs bt
   HA HB HInv EU EV ES ET EZ EAZ EW EM EQ SepStart BX BY BZ BInv BU BV X Y ZAt U V Inv Owned)
   as (mi & Start & Fields & OwnedI & Tight & FrameS).
 assert (OutH : forall pos,zinv_start_frame bu bv bs bt bz baz bp ba bb bh pos).
 { intro pos;unfold zinv_start_frame;repeat split;try (left;congruence);congruence. }
 assert (OutI : forall pos,zinv_start_frame bu bv bs bt bz baz bp ba bb bi pos).
 { intro pos;unfold zinv_start_frame;repeat split;try (left;congruence);congruence. }
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) HF FrameS OutH) as HFI.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) IF FrameS OutI) as IFI.
 destruct (exec_zinv_differences x y z u v inv e le mi bp ba bb baz bz bu bv bs bt bh bi
   EH EI EU EV ES ET EN EA SepAll Fields OwnedI Tight HFI IFI)
   as (mf & Differences & FieldsF & OwnedF & HOut & IOut & HFree & IFree & ValueH & ValueI & BH & BI & FrameD).
 exists mf;split.
 - change (Clight2.exec_stmt secp_ge e le m
     (statement_sequence zinv_start_statements (statement_sequence mixed_difference_statements Sskip)) E0 le mf Out_normal).
   eapply exec_statement_prefix_then_last;[exact Start|exact Differences].
 - split;[exact FieldsF|];split;[exact OwnedF|];split;[exact HOut|];split;[exact IOut|];
   split;[exact HFree|];split;[exact IFree|];split;[exact ValueH|];split;[exact ValueI|];
   split;[exact BH|];split;[exact BI|].
   eapply lframe_trans;[|exact FrameD].
   eapply lframe_implies;[exact FrameS|];intros bx pos (Base & NH & NI) Valid;exact Base.
Qed.
