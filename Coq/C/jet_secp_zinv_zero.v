(** Exact zinv early-return control, including the literal NULL argument. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_mixed_zero C.jet_secp_mixed_zero_return C.jet_secp_field_zero_owned
 C.jet_secp_double_var_owned C.jet_secp_double_all_calls C.jet_secp_gej_infinity_owned
 C.jet_secp_zinv_differences C.jet_secp_local_regions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.
Definition zinv_zero_head := match zinv_after_difference with Ssequence h _ => h | _ => Sskip end.
Definition zinv_after_zero := match zinv_after_difference with Ssequence _ t => t | _ => Sskip end.
Definition zinv_zero_branch := match zinv_zero_head with
 | Ssequence _ (Sifthenelse _ b _) => b | _ => Sskip end.
Definition zinv_i_dispatch := match zinv_zero_branch with
 | Ssequence (Ssequence _ b) _ => b | _ => Sskip end.
Definition zinv_double_call := curve_call _secp256k1_gej_double_var f_secp256k1_gej_double_var None
 [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _a (tptr (Tstruct __6123 noattr));
 Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Definition zinv_infinity_call := curve_call _secp256k1_gej_set_infinity f_secp256k1_gej_set_infinity None
 [Etempvar _r (tptr (Tstruct __6123 noattr))].
Lemma zinv_zero_source : zinv_after_difference =
 Ssequence (Ssequence (mixed_zero_call false) (Sifthenelse (Etempvar _t'2 tint) zinv_zero_branch Sskip)) zinv_after_zero.
Proof. reflexivity. Qed.
Lemma zinv_i_zero_source : zinv_zero_branch =
 Ssequence (Ssequence (mixed_zero_call true) zinv_i_dispatch) (Sreturn None).
Proof. reflexivity. Qed.
Lemma zinv_i_dispatch_source : zinv_i_dispatch =
 Sifthenelse (Etempvar _t'1 tint) zinv_double_call zinv_infinity_call.
Proof. reflexivity. Qed.
Local Ltac pure_call := unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
Local Ltac keep_field HF Frame :=
 eapply field_at_lframe;[exact HF|exact Frame|];intro pos;congruence.
Local Ltac keep_free HF Frame :=
 eapply curve_keep_free;[lia|exact HF|exact Frame|];intro pos;congruence.

Theorem exec_zinv_i_dispatch e le m bp x y z i :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 le!_t'1=Some (Vint (field_zero_result i)) ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_i_dispatch E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
 fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
 fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
 Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\
 square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
 lframe (fun bx _=>bx<>bp) m mf.
Proof.
 intros HA HR HI ED EF BX BY BZ Flag X Y ZAt PF.
 unfold mixed_zero_words,mixed_zero_flag,field_zero_result in *.
 destruct (Z.eqb (radix_value i mod feP) 0) eqn:IZ.
 - destruct (eval_double_var_finite x y z m bp BX BY BZ Flag X Y ZAt PF)
     as (mf & CD & XO & YO & ZO & FO & PFO & BXO & BYO & BZO & Frame).
   exists mf;split;[|repeat first [assumption|split]].
   rewrite zinv_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + apply eval_Etempvar;exact HI.
   + reflexivity.
   + unfold zinv_double_call;eapply exec_curve_call with
       (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
     * pure_call.
     * exact ED.
     * eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact HA|reflexivity|].
       eapply eval_Econs;[eapply eval_Ecast;[apply eval_Econst_int|reflexivity]|reflexivity|constructor].
     * exact CD.
 - destruct (eval_gej_infinity_initializer_owned m bp 0 ltac:(lia) ltac:(exists 0;reflexivity)
     ltac:(change (128<=18446744073709551615);lia) (freeable_range_writable _ _ _ _ PF))
     as (mf & CF & XO & YO & ZO & FO & LF & Perm & Valid).
   assert (PFO : Mem.range_perm mf bp 0 128 Cur Freeable).
   { intros pos HP;apply (proj2 (Perm bp pos Cur Freeable));apply PF;exact HP. }
   assert (Frame : lframe (fun bx _=>bx<>bp) m mf).
   { split.
     - intros ch bx pos HV HP;apply LF;left;apply (HP pos);pose proof (size_chunk_pos ch);lia.
     - split;[intros bx pos k p HV HP HQ;apply (proj2 (Perm bx pos k p));exact HQ|exact Valid]. }
   exists mf;split;[|repeat first [assumption|exact square_zero_bounds|split]].
   rewrite zinv_i_dispatch_source;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + apply eval_Etempvar;exact HI.
   + reflexivity.
   + unfold zinv_infinity_call;eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vundef).
     * pure_call.
     * exact EF.
     * eapply eval_Econs;[apply eval_Etempvar;exact HR|reflexivity|constructor].
     * exact CF.
Qed.

Theorem exec_zinv_i_branch e le m bp bi x y z i :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 e!_i=Some (bi,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
 e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None -> bp<>bi ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds i ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) -> fe_at m bi 0 (words5 i) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_zero_branch E0 (PTree.set _t'1 (Vint (field_zero_result i)) le) mf (Out_return None) /\
 fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
 fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
 fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
 Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\ fe_at mf bi 0 (words5 i) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
 lframe (fun bx _=>bx<>bp /\ bx<>bi) m mf.
Proof.
 intros HA HR EI EN ED EF Sep BX BY BZ BI Flag X Y ZAt I PF IF.
 destruct (exec_mixed_zero_call true i e le m bi EI EN BI I IF) as (mi & CI & II & IFI & FI).
 assert (XI : fe_at mi bp 0 (words5 x)) by (keep_field X FI).
 assert (YI : fe_at mi bp 40 (words5 y)) by (keep_field Y FI).
 assert (ZI : fe_at mi bp 80 (words5 z)) by (keep_field ZAt FI).
 assert (PFI : Mem.range_perm mi bp 0 128 Cur Freeable) by (keep_free PF FI).
 assert (FlagI : Mem.load Mint32 mi bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FI Mint32 bp 120);[exact Flag| |intros pos HP;exact Sep].
   eapply Mem.perm_valid_block;apply (PF 0);lia. }
 set (li := PTree.set _t'1 (Vint (field_zero_result i)) le).
 assert (HAI : li!_a=Some (Vptr bp Ptrofs.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact HA).
 assert (HRI : li!_r=Some (Vptr bp Ptrofs.zero)) by (unfold li;rewrite PTree.gso by discriminate;exact HR).
 destruct (exec_zinv_i_dispatch e li mi bp x y z i HAI HRI ltac:(unfold li;apply PTree.gss)
   ED EF BX BY BZ FlagI XI YI ZI PFI) as (mf & Dispatch & XO & YO & ZO & FO & PFO & BXO & BYO & BZO & FD).
 assert (IO : fe_at mf bi 0 (words5 i)) by (keep_field II FD).
 assert (IFO : Mem.range_perm mf bi 0 40 Cur Freeable) by (keep_free IFI FD).
 assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bi) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FI|];intros bx pos [NP NI] Valid;exact NI.
   - eapply lframe_implies;[exact FD|];intros bx pos [NP NI] Valid;exact NP. }
 exists mf;split.
 - rewrite zinv_i_zero_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=li).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi) (le1:=li);[exact CI|exact Dispatch].
   + apply exec_Sreturn_none.
 - repeat first [assumption|split].
Qed.

Theorem exec_zinv_nonzero_guard h e le m bh :
 e!_h=Some (bh,curve_fe_type) -> e!_secp256k1_fe_normalizes_to_zero_var=None ->
 square_input_bounds h -> radix_value h mod feP<>0 ->
 fe_at m bh 0 (words5 h) -> Mem.range_perm m bh 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_zero_head E0 (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal /\
 fe_at mf bh 0 (words5 h) /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ lframe (fun bx _=>bx<>bh) m mf.
Proof.
 intros EH EN BH HNZ HF HP.
 destruct (exec_mixed_zero_call false h e le m bh EH EN BH HF HP) as (mf & Call & HO & Free & Frame).
 assert (Value : field_zero_result h=Int.zero).
 { unfold field_zero_result;apply Z.eqb_neq in HNZ;rewrite HNZ;reflexivity. }
 rewrite Value in Call;exists mf;split;[|repeat first [assumption|split]].
 change (Clight2.exec_stmt secp_ge e le m
   (Ssequence (mixed_zero_call false) (Sifthenelse (Etempvar _t'2 tint) zinv_zero_branch Sskip)) E0
   (PTree.set _t'2 (Vint Int.zero) le) mf Out_normal).
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'2 (Vint Int.zero) le).
 - exact Call.
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
   + apply eval_Etempvar;apply PTree.gss.
   + reflexivity.
   + apply exec_Sskip.
Qed.

Theorem exec_zinv_zero_return e le m bp bh bi x y z h i :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 e!_h=Some (bh,curve_fe_type) -> e!_i=Some (bi,curve_fe_type) ->
 e!_secp256k1_fe_normalizes_to_zero_var=None -> e!_secp256k1_gej_double_var=None -> e!_secp256k1_gej_set_infinity=None ->
 bp<>bh -> bp<>bi -> bh<>bi ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 square_input_bounds h -> square_input_bounds i -> radix_value h mod feP=0 ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bh 0 (words5 h) -> fe_at m bi 0 (words5 i) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bh 0 40 Cur Freeable -> Mem.range_perm m bi 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_after_difference E0 (mixed_zero_return_temps le i) mf (Out_return None) /\
 fe_at mf bp 0 (words5 (mixed_zero_words i (double_output_x_words x y))) /\
 fe_at mf bp 40 (words5 (mixed_zero_words i (double_output_y_words x y))) /\
 fe_at mf bp 80 (words5 (mixed_zero_words i (double_output_z_words y z))) /\
 Mem.load Mint32 mf bp 120=Some (Vint (mixed_zero_flag i y z)) /\
 fe_at mf bh 0 (words5 h) /\ fe_at mf bi 0 (words5 i) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bh 0 40 Cur Freeable /\ Mem.range_perm mf bi 0 40 Cur Freeable /\
 square_input_bounds (mixed_zero_words i (double_output_x_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_y_words x y)) /\
 square_input_bounds (mixed_zero_words i (double_output_z_words y z)) /\
 lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi) m mf.
Proof.
 intros HA HR EH EI EN ED EF SPH SPI SHI BX BY BZ BH BI HZ Flag X Y ZAt H I PF HF IF.
 destruct (exec_mixed_zero_call false h e le m bh EH EN BH H HF) as (mh & CH & HH & HFH & FH).
 assert (VH : field_zero_result h=Int.one) by (unfold field_zero_result;rewrite HZ;reflexivity).
 rewrite VH in CH.
 set (lh := PTree.set _t'2 (Vint Int.one) le).
 assert (HAH : lh!_a=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HA).
 assert (HRH : lh!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lh;rewrite PTree.gso by discriminate;exact HR).
 assert (XH : fe_at mh bp 0 (words5 x)) by (keep_field X FH).
 assert (YH : fe_at mh bp 40 (words5 y)) by (keep_field Y FH).
 assert (ZH : fe_at mh bp 80 (words5 z)) by (keep_field ZAt FH).
 assert (IH : fe_at mh bi 0 (words5 i)) by (keep_field I FH).
 assert (PFH : Mem.range_perm mh bp 0 128 Cur Freeable) by (keep_free PF FH).
 assert (IFH : Mem.range_perm mh bi 0 40 Cur Freeable) by (keep_free IF FH).
 assert (FlagH : Mem.load Mint32 mh bp 120=Some (Vint Int.zero)).
 { rewrite (proj1 FH Mint32 bp 120);[exact Flag| |intros pos HP;exact SPH].
   eapply Mem.perm_valid_block;apply (PF 0);lia. }
 destruct (exec_zinv_i_branch e lh mh bp bi x y z i HAH HRH EI EN ED EF SPI BX BY BZ BI FlagH XH YH ZH IH PFH IFH)
   as (mf & Branch & XO & YO & ZO & FO & IO & PFO & IFO & BXO & BYO & BZO & FB).
 assert (HO : fe_at mf bh 0 (words5 h)).
 { eapply field_at_lframe;[exact HH|exact FB|];intro pos;split;congruence. }
 assert (HFO : Mem.range_perm mf bh 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact HFH|exact FB|];intro pos;split;congruence. }
 assert (Frame : lframe (fun bx _=>bx<>bp /\ bx<>bh /\ bx<>bi) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FH|];intros bx pos (NP & NH & NI) Valid;exact NH.
   - eapply lframe_implies;[exact FB|];intros bx pos (NP & NH & NI) Valid;split;assumption. }
 exists mf;split.
 - rewrite zinv_zero_source;eapply exec_Sseq_2;[|discriminate].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mh) (le1:=lh);[exact CH|].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
   + apply eval_Etempvar;unfold lh;apply PTree.gss.
   + reflexivity.
   + exact Branch.
 - repeat first [assumption|split].
Qed.
