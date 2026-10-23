(** Entire original finite-input suffix, starting only from caller fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_field_weak_loose
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_statement_prefix C.jet_secp_zinv_initial_products C.jet_secp_zinv_start
 C.jet_secp_zinv_differences C.jet_secp_zinv_zero C.jet_secp_zinv_nonzero
 C.jet_secp_mixed_zero_return C.jet_secp_mixed_nonzero_tail C.jet_secp_double_all_calls C.jet_secp_double_coordinate_numeric
 C.jet_secp_double_flag C.jet_secp_mixed_finite_start.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words.
Definition zinv_finite_x x y z u v inv :=
 if Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0
 then mixed_zero_words (zinv_i_words y z v inv) (double_output_x_words x y)
 else mixed_nonzero_x_words (zinv_h_words x z u inv) (zinv_i_words y z v inv) (weak_loose_words x).
Definition zinv_finite_y x y z u v inv :=
 if Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0
 then mixed_zero_words (zinv_i_words y z v inv) (double_output_y_words x y)
 else mixed_nonzero_y_words (zinv_h_words x z u inv) (zinv_i_words y z v inv) (weak_loose_words x) (weak_loose_words y).
Definition zinv_finite_z x y z u v inv :=
 if Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0
 then mixed_zero_words (zinv_i_words y z v inv) (double_output_z_words y z)
 else point_mul_words z (zinv_h_words x z u inv).
Definition zinv_finite_flag x y z u v inv :=
 if Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0
 then mixed_zero_flag (zinv_i_words y z v inv) y z else Int.zero.
Definition zinv_finite_temps le x y z u v inv :=
 if Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0
 then mixed_zero_return_temps le (zinv_i_words y z v inv) else PTree.set _t'2 (Vint Int.zero) le.
Definition zinv_finite_out x z u inv :=
 if Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0 then Out_return None else Out_normal.
Definition zinv_finite_owned m bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk :=
 zinv_start_owned m bp ba bb baz bz bu bv bs bt /\
 Mem.range_perm m bh 0 40 Cur Freeable /\ Mem.range_perm m bi 0 40 Cur Freeable /\
 Mem.range_perm m b2 0 40 Cur Freeable /\ Mem.range_perm m b3 0 40 Cur Freeable /\ Mem.range_perm m bk 0 40 Cur Freeable.
Definition zinv_finite_frame (bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk bx : block) pos :=
 bx<>bp /\ (bx<>ba \/ pos<0 \/80<=pos) /\ bx<>bb /\
 bx<>baz /\ bx<>bz /\ bx<>bu /\ bx<>bv /\ bx<>bs /\ bx<>bt /\ bx<>bh /\ bx<>bi /\ bx<>b2 /\ bx<>b3 /\ bx<>bk.
Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Sep" in let HQ:=fresh "Sep" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.
Local Ltac keep_owned HF Frame :=
 eapply curve_keep_free;[clear;lia|exact HF|exact Frame|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac outside_preparation := unfold zinv_difference_frame,zinv_start_frame;
 repeat split;try (left;congruence);congruence.

Theorem exec_zinv_finite_suffix x y z u v inv e le m bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 le!_bzinv=Some (Vptr bb Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
 e!_z12=Some (bz,curve_fe_type) -> e!_az=Some (baz,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
 NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 zinv_finite_owned m bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_finite_suffix E0 (zinv_finite_temps le x y z u v inv) mf (zinv_finite_out x z u inv) /\
 fe_at mf bp 0 (words5 (zinv_finite_x x y z u v inv)) /\
 fe_at mf bp 40 (words5 (zinv_finite_y x y z u v inv)) /\
 fe_at mf bp 80 (words5 (zinv_finite_z x y z u v inv)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (zinv_finite_flag x y z u v inv)) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 zinv_finite_owned mf bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk /\
 square_input_bounds (zinv_finite_x x y z u v inv) /\
 square_input_bounds (zinv_finite_y x y z u v inv) /\
 square_input_bounds (zinv_finite_z x y z u v inv) /\
 lframe (zinv_finite_frame bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk) m mf.
Proof.
 intros HA HB HInv HR EU EV ES ET EZ EAZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF Sep
   BX BY BZ BU BV BInv Flag X Y ZAt U V Inv (Owned & HF & IF & F2 & F3 & FK).
 pose proof Sep as SepAll;separate_blocks Sep.
 assert (SepP : NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi]) by
   exact (@NoDup_app_remove_r block [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi] [b2;b3;bk] SepAll).
 assert (SepN : NoDup [bp;bh;b2;b3;bk;bu;bi;bs]) by
   (clear -SepAll;repeat rewrite NoDup_cons_iff in *;cbn [In] in *;intuition congruence).
 destruct (exec_zinv_difference_prefix x y z u v inv e le m bp ba bb baz bz bu bv bs bt bh bi
   HA HB HInv EU EV ES ET EZ EAZ EH EI EW EM EQ EN EA SepP
   ltac:(intros j HJ;pose proof (square_input56 x BX j HJ);lia)
   ltac:(intros j HJ;pose proof (square_input56 y BY j HJ);lia)
   BZ BInv BU BV X Y ZAt U V Inv Owned HF IF)
   as (mp & Prep & Fields & OwnedP & H & I & HFP & IFP & VH & VI & BH & BI & FP).
 destruct Fields as (XP & YP & ZP & UP & VP & InvP & AZP & Z12P & U1P & U2P & S1P & S2P).
 destruct OwnedP as (PFP & AFP & InvFP & AZFP & ZFP & UFP & VFP & SFP & TFP).
 assert (F2P : Mem.range_perm mp b2 0 40 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact F2|exact FP|];intro pos;outside_preparation. }
 assert (F3P : Mem.range_perm mp b3 0 40 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact F3|exact FP|];intro pos;outside_preparation. }
 assert (FKP : Mem.range_perm mp bk 0 40 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact FK|exact FP|];intro pos;outside_preparation. }
 assert (FlagP : Mem.load Mint32 mp bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FP Mint32 bp 120);[exact Flag| |].
   - destruct Owned as (PF & Rest);eapply Mem.perm_valid_block;apply (PF 0);lia.
   - intros pos Range;unfold zinv_difference_frame,zinv_start_frame;
       repeat split;try (left;congruence);try congruence;right;right;clear - Range;change (120<=pos<124) in Range;lia. }
 assert (PrefixFrame : lframe (zinv_finite_frame bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk) m mp).
 { eapply lframe_implies;[exact FP|].
   intros bx pos (NP & NA & NB & NAZ & NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK) Valid.
   unfold zinv_difference_frame,zinv_start_frame;split;[|split;assumption].
   split;[exact NU|];split;[exact NV|];split;[exact NS|];split;[exact NT|];split;[exact NZ|];split;[exact NAZ|];
     split;[|split;assumption].
   left;exact NP. }
 unfold zinv_finite_temps,zinv_finite_out,zinv_finite_x,zinv_finite_y,zinv_finite_z,zinv_finite_flag.
 destruct (Z.eqb (radix_value (zinv_h_words x z u inv) mod feP) 0) eqn:HZ.
 - apply Z.eqb_eq in HZ.
   destruct (exec_zinv_zero_return e le mp bp bh bi x y z (zinv_h_words x z u inv) (zinv_i_words y z v inv)
     HA HR EH EI E0N ED EF ltac:(congruence) ltac:(congruence) ltac:(congruence)
     BX BY BZ BH BI HZ FlagP XP YP ZP H I PFP HFP IFP)
     as (mf & Tail & XO & YO & ZO & FlagO & HO & IO & PFO & HFO & IFO & BXO & BYO & BZO & FR).
   assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_owned AFP FR).
   assert (InvFO : Mem.range_perm mf bb 0 40 Cur Freeable) by (keep_owned InvFP FR).
   assert (AZFO : Mem.range_perm mf baz 0 40 Cur Freeable) by (keep_owned AZFP FR).
   assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_owned ZFP FR).
   assert (UFO : Mem.range_perm mf bu 0 40 Cur Freeable) by (keep_owned UFP FR).
   assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_owned VFP FR).
   assert (SFO : Mem.range_perm mf bs 0 40 Cur Freeable) by (keep_owned SFP FR).
   assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_owned TFP FR).
   assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_owned F2P FR).
   assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_owned F3P FR).
   assert (FKO : Mem.range_perm mf bk 0 40 Cur Freeable) by (keep_owned FKP FR).
   assert (UO : fe_at mf ba 0 (words5 u)).
   { eapply field_at_lframe;[exact UP|exact FR|];intro pos;repeat split;congruence. }
   assert (VO : fe_at mf ba 40 (words5 v)).
   { eapply field_at_lframe;[exact VP|exact FR|];intro pos;repeat split;congruence. }
   assert (InvO : fe_at mf bb 0 (words5 inv)).
   { eapply field_at_lframe;[exact InvP|exact FR|];intro pos;repeat split;congruence. }
   assert (Frame : lframe (zinv_finite_frame bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk) m mf).
   { eapply lframe_trans;[exact PrefixFrame|].
     eapply lframe_implies;[exact FR|].
     intros bx pos (NP & NA & NB & NAZ & NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK) Valid.
     repeat split;assumption. }
   exists mf;split.
   + rewrite zinv_difference_prefix_source;eapply exec_statement_prefix_then_last;[exact Prep|exact Tail].
   + split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
     split;[exact UO|];split;[exact VO|];split;[exact InvO|];split.
     * unfold zinv_finite_owned,zinv_start_owned;repeat first [assumption|split].
     * repeat first [assumption|split].
 - apply Z.eqb_neq in HZ.
   assert (TX : square_input_bounds (weak_loose_words x)).
   { apply double_tight_loose;apply (proj2 (weak_loose_numeric x ltac:(intros j HJ;pose proof (square_input56 x BX j HJ);lia))). }
   assert (TY : square_input_bounds (weak_loose_words y)).
   { apply double_tight_loose;apply (proj2 (weak_loose_numeric y ltac:(intros j HJ;pose proof (square_input56 y BY j HJ);lia))). }
   destruct (exec_zinv_nonzero_tail e le mp bp bh b2 b3 bk bu bi bs x y z
     (zinv_h_words x z u inv) (weak_loose_words x) (zinv_i_words y z v inv) (weak_loose_words y)
     HA HR EH E2 E3 EK EU EI ES E0N EM EQ EN EA SepN BZ BH TX BI TY HZ XP YP ZP H U1P I S1P
     PFP HFP F2P F3P FKP UFP IFP SFP)
     as (mf & Tail & XO & YO & ZO & FlagO & PFO & HFO & F2O & F3O & FKO & UFO & IFO & SFO & BXO & BYO & BZO & FR).
   assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_owned AFP FR).
   assert (InvFO : Mem.range_perm mf bb 0 40 Cur Freeable) by (keep_owned InvFP FR).
   assert (AZFO : Mem.range_perm mf baz 0 40 Cur Freeable) by (keep_owned AZFP FR).
   assert (ZFO : Mem.range_perm mf bz 0 40 Cur Freeable) by (keep_owned ZFP FR).
   assert (VFO : Mem.range_perm mf bv 0 40 Cur Freeable) by (keep_owned VFP FR).
   assert (TFO : Mem.range_perm mf bt 0 40 Cur Freeable) by (keep_owned TFP FR).
   assert (UO : fe_at mf ba 0 (words5 u)).
   { eapply field_at_lframe;[exact UP|exact FR|];intro pos;unfold mixed_nonzero_tail_frame;
       repeat split;try (left;congruence);congruence. }
   assert (VO : fe_at mf ba 40 (words5 v)).
   { eapply field_at_lframe;[exact VP|exact FR|];intro pos;unfold mixed_nonzero_tail_frame;
       repeat split;try (left;congruence);congruence. }
   assert (InvO : fe_at mf bb 0 (words5 inv)).
   { eapply field_at_lframe;[exact InvP|exact FR|];intro pos;unfold mixed_nonzero_tail_frame;
       repeat split;try (left;congruence);congruence. }
   assert (Frame : lframe (zinv_finite_frame bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk) m mf).
   { eapply lframe_trans;[exact PrefixFrame|].
     eapply lframe_implies;[exact FR|].
     intros bx pos (NP & NA & NB & NAZ & NZ & NU & NV & NS & NT & NH & NI & N2 & N3 & NK) Valid.
     unfold mixed_nonzero_tail_frame;repeat split;try assumption;left;exact NP. }
   exists mf;split.
   + rewrite zinv_difference_prefix_source;eapply exec_statement_prefix_then_last;[exact Prep|exact Tail].
   + split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
     split;[exact UO|];split;[exact VO|];split;[exact InvO|];split.
     * unfold zinv_finite_owned,zinv_start_owned;repeat first [assumption|split].
     * repeat first [assumption|split].
Qed.

Definition zinv_a_head := match fn_body f_secp256k1_gej_add_zinv_var with
 | Ssequence head _ => head | _ => Sskip end.
Definition zinv_b_head := match fn_body f_secp256k1_gej_add_zinv_var with
 | Ssequence _ (Ssequence head _) => head | _ => Sskip end.
Definition zinv_heads_temps le := PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le).
Lemma zinv_body_source : fn_body f_secp256k1_gej_add_zinv_var =
 Ssequence zinv_a_head (Ssequence zinv_b_head zinv_finite_suffix).
Proof. reflexivity. Qed.
Lemma exec_zinv_a_head_finite e le m bp :
 le!_a=Some (Vptr bp Ptrofs.zero) -> Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge e le m zinv_a_head E0 (PTree.set _t'4 (Vint Int.zero) le) m Out_normal.
Proof.
 intros HA Flag;unfold zinv_a_head.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_double_flag_field;exact HA.
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
     change (Mem.load Mint32 m bp 120=Some (Vint Int.zero));exact Flag.
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + apply eval_Etempvar;apply PTree.gss.
   + reflexivity.
   + apply exec_Sskip.
Qed.

Lemma exec_zinv_b_head_finite e le m ba :
 le!_b=Some (Vptr ba Ptrofs.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge e le m zinv_b_head E0 (PTree.set _t'3 (Vint Int.zero) le) m Out_normal.
Proof.
 intros HB Flag;unfold zinv_b_head.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'3 (Vint Int.zero) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_mixed_b_field;[cbn [In];tauto|exact HB].
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
     change (Mem.load Mint32 m ba 80=Some (Vint Int.zero));exact Flag.
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + apply eval_Etempvar;apply PTree.gss.
   + reflexivity.
   + apply exec_Sskip.
Qed.

Theorem exec_zinv_finite_body x y z u v inv e le m bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 le!_bzinv=Some (Vptr bb Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 e!_u1=Some (bu,curve_fe_type) -> e!_u2=Some (bv,curve_fe_type) ->
 e!_s1=Some (bs,curve_fe_type) -> e!_s2=Some (bt,curve_fe_type) ->
 e!_z12=Some (bz,curve_fe_type) -> e!_az=Some (baz,curve_fe_type) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_h2=Some (b2,curve_fe_type) -> e!_h3=Some (b3,curve_fe_type) -> e!_t=Some (bk,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_sqr=None ->
 e!_secp256k1_fe_negate=None -> e!_secp256k1_fe_add=None ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
 NoDup [bp;ba;bb;baz;bz;bu;bv;bs;bt;bh;bi;b2;b3;bk] ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) -> Mem.load Mint32 m ba 80=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 zinv_finite_owned m bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_zinv_var) E0 (zinv_finite_temps (zinv_heads_temps le) x y z u v inv) mf (zinv_finite_out x z u inv) /\
 fe_at mf bp 0 (words5 (zinv_finite_x x y z u v inv)) /\
 fe_at mf bp 40 (words5 (zinv_finite_y x y z u v inv)) /\
 fe_at mf bp 80 (words5 (zinv_finite_z x y z u v inv)) /\
 Mem.load Mint32 mf bp 120=Some (Vint (zinv_finite_flag x y z u v inv)) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 zinv_finite_owned mf bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk /\
 square_input_bounds (zinv_finite_x x y z u v inv) /\
 square_input_bounds (zinv_finite_y x y z u v inv) /\
 square_input_bounds (zinv_finite_z x y z u v inv) /\
 lframe (zinv_finite_frame bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk) m mf.
Proof.
 intros HA HB HInv HR EU EV ES ET EZ EAZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF Sep
   BX BY BZ BU BV BInv Flag FlagB X Y ZAt U V Inv Owned.
 set (lh := zinv_heads_temps le).
 assert (HAH : lh!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lh,zinv_heads_temps;rewrite !PTree.gso by discriminate;exact HA).
 assert (HBH : lh!_b=Some (Vptr ba Ptrofs.zero)) by (unfold lh,zinv_heads_temps;rewrite !PTree.gso by discriminate;exact HB).
 assert (HIH : lh!_bzinv=Some (Vptr bb Ptrofs.zero)) by (unfold lh,zinv_heads_temps;rewrite !PTree.gso by discriminate;exact HInv).
 assert (HRH : lh!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lh,zinv_heads_temps;rewrite !PTree.gso by discriminate;exact HR).
 destruct (exec_zinv_finite_suffix x y z u v inv e lh m bp ba bb baz bz bu bv bs bt bh bi b2 b3 bk
   HAH HBH HIH HRH EU EV ES ET EZ EAZ EH EI E2 E3 EK EW EM EQ EN EA E0N ED EF Sep
   BX BY BZ BU BV BInv Flag X Y ZAt U V Inv Owned) as (mf & Suffix & Post).
 exists mf;split;[|exact Post].
 rewrite zinv_body_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
 - exact (exec_zinv_a_head_finite e le m bp HA Flag).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lh).
   + apply exec_zinv_b_head_finite with (ba:=ba);[rewrite PTree.gso by discriminate;exact HB|exact FlagB].
   + exact Suffix.
Qed.
