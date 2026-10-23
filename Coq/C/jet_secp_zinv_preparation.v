(** All seven preparation statements after az/z12, deriving the local-az S2 call. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_curve_mul
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_weak_loose
 C.jet_secp_field_pair_multiply C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_statement_prefix C.jet_secp_zinv_initial_products C.jet_secp_zinv_shared_preparation C.jet_secp_zinv_s2.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words field_pair_product.
Definition zinv_preparation_statements := zinv_shared_preparation++[zinv_s2_az_statement].
Definition zinv_s2_words v t az := field_pair_product (point_mul_words v t) az.
Definition zinv_preparation_frame (bu bv bs bt bz baz ba bx : block) pos :=
 bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt /\ bx<>bz /\ bx<>baz /\ (bx<>ba \/ pos<0 \/ 80<=pos).
Lemma zinv_preparation_source : zinv_after_z12=statement_sequence zinv_preparation_statements zinv_after_s2_az.
Proof. rewrite zinv_shared_preparation_source,zinv_s2_az_source;reflexivity. Qed.
Local Ltac separate_blocks HSep :=
 repeat rewrite NoDup_cons_iff in HSep;cbn [In] in HSep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.

Theorem exec_zinv_preparation x y u v t az e le m bp ba baz bu bv bs bt bz :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
 e!_z12=Some (bz,curve_fe_type) -> e!_az=Some (baz,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None ->
 NoDup [bp;ba;baz;bu;bv;bs;bt;bz] ->
 (forall i,(i<5)%nat -> Int64.unsigned (x i)<=2^60) ->
 (forall i,(i<5)%nat -> Int64.unsigned (y i)<=2^60) ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds t -> square_input_bounds az ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bz 0 (words5 t) -> fe_at m baz 0 (words5 az) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m baz 0 40 Cur Freeable -> Mem.range_perm m bu 0 40 Cur Freeable -> Mem.range_perm m bv 0 40 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bt 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_preparation_statements Sskip) E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bz 0 (words5 t) /\ fe_at mf baz 0 (words5 az) /\
 fe_at mf bu 0 (words5 (weak_loose_words x)) /\ fe_at mf bv 0 (words5 (point_mul_words u t)) /\
 fe_at mf bs 0 (words5 (weak_loose_words y)) /\ fe_at mf bt 0 (words5 (zinv_s2_words v t az)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf baz 0 40 Cur Freeable /\ Mem.range_perm mf bu 0 40 Cur Freeable /\ Mem.range_perm mf bv 0 40 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 mul_small_input_bounds (weak_loose_words x) /\ mul_small_input_bounds (weak_loose_words y) /\
 mul_small_input_bounds (point_mul_words u t) /\ mul_small_input_bounds (zinv_s2_words v t az) /\
 radix_value (zinv_s2_words v t az) mod feP=(radix_value v*radix_value t*radix_value az) mod feP /\
 lframe (zinv_preparation_frame bu bv bs bt bz baz ba) m mf.
Proof.
 intros HA HB EU EV ES ET EZ EA EW EM Sep BX BY BU BV BT BAZ X Y U V T AZ PF AF AZF UF VF SF TF ZF.
 separate_blocks Sep.
 assert (SepP : NoDup [bp;ba;bu;bv;bs;bt;bz]) by
   (repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence).
 destruct (exec_zinv_shared_preparation x y u v t e le m bp ba bu bv bs bt bz
   HA HB EU EV ES ET EZ EW EM SepP BX BY BU BV BT X Y U V T PF AF UF VF SF TF ZF)
   as (mi & Prep & XI & YI & UI & VI & TI & U1 & U2 & S1 & S2 & PFI & AFI & UFI & VFI & SFI & TFI & ZFI & TX & TY & BOU & BOS & FI).
 assert (OutAZ : forall pos,zinv_shared_frame bu bv bs bt bz ba baz pos).
 { intro pos;unfold zinv_shared_frame;repeat split;try (left;congruence);congruence. }
 pose proof (field_at_lframe _ _ _ _ _ _ AZ FI OutAZ) as AZI.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) AZF FI OutAZ) as AZFI.
 destruct (exec_zinv_s2_az_from_owned (point_mul_words v t) az e le mi bt baz
   ET EA EM BOS BAZ ltac:(congruence) S2 AZI TFI AZFI)
   as (mf & Mul & SOut & AZOut & TFF & AZFF & Val & Tight & FM).
 assert (OutP : forall pos : Z,bp<>bt /\ bp<>baz) by (intros;split;congruence).
 assert (OutA : forall pos : Z,ba<>bt /\ ba<>baz) by (intros;split;congruence).
 assert (OutZ : forall pos : Z,bz<>bt /\ bz<>baz) by (intros;split;congruence).
 assert (OutU : forall pos : Z,bu<>bt /\ bu<>baz) by (intros;split;congruence).
 assert (OutV : forall pos : Z,bv<>bt /\ bv<>baz) by (intros;split;congruence).
 assert (OutS : forall pos : Z,bs<>bt /\ bs<>baz) by (intros;split;congruence).
 pose proof (field_at_lframe _ _ _ _ _ _ XI FM OutP) as XF.
 pose proof (field_at_lframe _ _ _ _ _ _ YI FM OutP) as YF.
 pose proof (field_at_lframe _ _ _ _ _ _ UI FM OutA) as UFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ VI FM OutA) as VFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ TI FM OutZ) as TFinal.
 pose proof (field_at_lframe _ _ _ _ _ _ U1 FM OutU) as U1F.
 pose proof (field_at_lframe _ _ _ _ _ _ U2 FM OutV) as U2F.
 pose proof (field_at_lframe _ _ _ _ _ _ S1 FM OutS) as S1F.
 pose proof (curve_keep_free _ _ _ _ 128 ltac:(lia) PFI FM OutP) as PFF.
 pose proof (curve_keep_free _ _ _ _ 88 ltac:(lia) AFI FM OutA) as AFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) ZFI FM OutZ) as ZFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) UFI FM OutU) as UFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) VFI FM OutV) as VFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) SFI FM OutS) as SFF.
 assert (UTight : mul_small_input_bounds (point_mul_words u t))
   by exact (proj2 (curve_mul_value_bounds u t (field_operand_from_bounds u BU) (field_operand_from_bounds t BT))).
 assert (SValue : radix_value (zinv_s2_words v t az) mod feP=(radix_value v*radix_value t*radix_value az) mod feP).
 { pose proof (proj1 (point_mul_value_and_bounds v t BV BT)) as ProductValue.
   rewrite field_prime_matches_normalizer in ProductValue.
   unfold zinv_s2_words;rewrite Val.
   rewrite (Z.mul_mod (radix_value (point_mul_words v t)) (radix_value az) feP),
     ProductValue,<-Z.mul_mod by (unfold feP,feR;lia);reflexivity. }
 exists mf;split.
 - unfold zinv_preparation_statements.
   change (Clight2.exec_stmt secp_ge e le m (statement_sequence zinv_shared_preparation
     (Ssequence zinv_s2_az_statement Sskip)) E0 le mf Out_normal).
   eapply exec_statement_prefix_then_last;[exact Prep|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact Mul|constructor].
 - split;[exact XF|];split;[exact YF|];split;[exact UFinal|];split;[exact VFinal|];split;[exact TFinal|];split;[exact AZOut|];
   split;[exact U1F|];split;[exact U2F|];split;[exact S1F|];split;[exact SOut|];
   split;[exact PFF|];split;[exact AFF|];split;[exact AZFF|];split;[exact UFF|];split;[exact VFF|];
   split;[exact SFF|];split;[exact TFF|];split;[exact ZFF|];split;[exact TX|];split;[exact TY|];
   split;[exact UTight|];split;[exact Tight|];split;[exact SValue|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FI|].
     intros bx pos (NU & NV & NS & NT & NZ & NAZ & NA) Valid.
     unfold zinv_shared_frame;split;[exact NU|];split;[exact NV|];split;[exact NS|];split;[exact NT|];split;assumption.
   + eapply lframe_implies;[exact FM|].
     intros bx pos (NU & NV & NS & NT & NZ & NAZ & NA) Valid;split;assumption.
Qed.
