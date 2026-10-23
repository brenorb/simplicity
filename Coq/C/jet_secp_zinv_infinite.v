(** Original A-infinity branch, including flag copies, arithmetic and return. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_square_numeric C.jet_secp_point_set_bit C.jet_secp_point_write_run
 C.jet_secp_double_flag C.jet_secp_double_statements C.jet_secp_mixed_finite_start
 C.jet_secp_statement_prefix C.jet_secp_zinv_finite C.jet_secp_zinv_infinite_products
 C.jet_secp_local_regions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words square_words.
Definition zinv_infinite_flag_stmt := match zinv_infinite_branch with Ssequence s _=>s | _=>Sskip end.
Definition zinv_infinite_z_stmt := match zinv_infinite_after_products with Ssequence s _=>s | _=>Sskip end.
Lemma zinv_infinite_branch_source : zinv_infinite_branch =
 Ssequence zinv_infinite_flag_stmt zinv_infinite_after_flag.
Proof. reflexivity. Qed.
Lemma zinv_infinite_z_source : zinv_infinite_after_products = Ssequence zinv_infinite_z_stmt (Sreturn None).
Proof. reflexivity. Qed.
Lemma zinv_infinite_head_source : zinv_a_head =
 Ssequence (Sset _t'4 (double_point_field _a _infinity tint))
 (Sifthenelse (Etempvar _t'4 tint) zinv_infinite_branch Sskip).
Proof. reflexivity. Qed.

Theorem exec_zinv_infinite_flag e le m bp ba flag :
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 Mem.load Mint32 m ba 80=Some (Vint flag) -> Mem.range_perm m bp 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_infinite_flag_stmt E0 (PTree.set _t'6 (Vint flag) le) mf Out_normal /\
 Mem.load Mint32 mf bp 120=Some (Vint flag) /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
 lframe (fun bx pos=>bx<>bp \/pos<120 \/124<=pos) m mf.
Proof.
 intros HR HB Flag PF.
 assert (Access : Mem.valid_access m Mint32 bp 120 Writable).
 { split;[intros pos Range;apply (freeable_range_writable _ _ _ _ PF);change (120<=pos<124) in Range;lia|exists 30;reflexivity]. }
 destruct (Mem.valid_access_store m Mint32 bp 120 (Vint flag) Access) as (mf & Store).
 assert (Frame : lframe (fun bx pos=>bx<>bp \/pos<120 \/124<=pos) m mf).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range;change (120<=pos<124) in Range;intros [NE|[Lo|Hi]];[contradiction|lia|lia]. }
 exists mf;split.
 - unfold zinv_infinite_flag_stmt.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'6 (Vint flag) le).
   + apply exec_Sset;eapply eval_Elvalue.
     * apply eval_mixed_b_field;[cbn [In];tauto|exact HB].
     * eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Flag].
   + eapply exec_Sassign with (loc:=bp) (ofs:=Ptrofs.repr 120) (bf:=Full) (v2:=Vint flag) (v:=Vint flag).
     * apply eval_double_flag_field;rewrite PTree.gso by discriminate;exact HR.
     * apply eval_Etempvar;apply PTree.gss.
     * reflexivity.
     * eapply assign_loc_value with (chunk:=Mint32);[reflexivity|exact Store].
 - split;[exact (Mem.load_store_same _ _ _ _ _ _ Store)|];split;[|exact Frame].
   intros pos Range;eapply Mem.perm_store_1;[exact Store|apply PF;exact Range].
Qed.

Lemma zinv_set_bit_bounds bit : square_input_bounds (point_set_bit_words bit).
Proof.
 intros i HI;unfold point_set_bit_words;
 destruct bit,(Nat.eqb i 0),(Nat.eqb i 4);vm_compute;split;discriminate.
Qed.

Theorem exec_zinv_infinite_z e le m bp flag :
 le!_r=Some (Vptr bp Ptrofs.zero) -> e!_secp256k1_fe_set_int=None ->
 Mem.load Mint32 m bp 120=Some (Vint flag) -> Mem.range_perm m bp 0 128 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m zinv_infinite_z_stmt E0 (PTree.set _t'5 (Vint flag) le) mf Out_normal /\
 fe_at mf bp 80 (words5 (point_set_bit_words (Int.eq flag Int.zero))) /\
 Mem.load Mint32 mf bp 120=Some (Vint flag) /\ Mem.range_perm mf bp 0 128 Cur Freeable /\
 lframe (fun bx pos=>bx<>bp \/pos<80 \/120<=pos) m mf.
Proof.
 intros HR EI Flag PF.
 destruct (eval_point_set_bit PointZ (Int.eq flag Int.zero) m bp PF) as (mf & SetZ & ZO & PFO & Frame).
 assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint flag)).
 { rewrite (proj1 Frame Mint32 bp 120);[exact Flag| |intros pos Range;right;right;
     change (120<=pos);change (120<=pos<124) in Range;lia].
   eapply Mem.perm_valid_block;apply (PF 0);lia. }
 exists mf;split;[|repeat first [assumption|split]].
 unfold zinv_infinite_z_stmt.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'5 (Vint flag) le).
 - apply exec_Sset;eapply eval_Elvalue.
   + apply eval_double_flag_field;exact HR.
   + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Flag].
 - change (Clight2.exec_stmt secp_ge e (PTree.set _t'5 (Vint flag) le) m
     (curve_call _secp256k1_fe_set_int f_secp256k1_fe_set_int None
       [double_point_address _r _z;Eunop Cop.Onotbool (Etempvar _t'5 tint) tint]) E0
     (PTree.set _t'5 (Vint flag) le) mf Out_normal).
   eapply exec_curve_call with
     (vargs:=[Vptr bp (Ptrofs.repr 80);Vint (if Int.eq flag Int.zero then Int.one else Int.zero)]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact EI.
   + eapply eval_Econs.
     * apply eval_double_point_address;[cbn [In];tauto|rewrite PTree.gso by discriminate;exact HR].
     * reflexivity.
     * eapply eval_Econs.
       -- eapply eval_Eunop with (v1:=Vint flag) (v:=Vint (if Int.eq flag Int.zero then Int.one else Int.zero)).
          ++ apply eval_Etempvar;apply PTree.gss.
          ++ change (option_map (fun b=>Val.of_bool (negb b)) (Some (negb (Int.eq flag Int.zero))) =
                Some (Vint (if Int.eq flag Int.zero then Int.one else Int.zero))).
             destruct (Int.eq flag Int.zero);reflexivity.
       -- reflexivity.
       -- constructor.
   + exact SetZ.
Qed.

Definition zinv_infinite_temps le aflag flag :=
 PTree.set _t'5 (Vint flag) (PTree.set _t'6 (Vint flag) (PTree.set _t'4 (Vint aflag) le)).
Local Ltac separate_blocks Sep :=
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep;
 repeat match goal with HC : _ /\ _ |- _ => destruct HC end;
 repeat match goal with HC : ~(?P \/ ?Q) |- _ =>
   let HP:=fresh "Different" in let HQ:=fresh "Different" in
   assert (HP:~P) by (intro;apply HC;left;assumption);
   assert (HQ:~Q) by (intro;apply HC;right;assumption);clear HC end.
Local Ltac keep_field H F := eapply field_at_lframe;[exact H|exact F|];intro pos;repeat split;try (left;congruence);congruence.
Local Ltac keep_free H F := eapply curve_keep_free;[lia|exact H|exact F|];intro pos;repeat split;try (left;congruence);congruence.

Theorem exec_zinv_infinite_body u v inv aflag flag e le m bp ba bb b2 b3 :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_r=Some (Vptr bp Ptrofs.zero) ->
 le!_b=Some (Vptr ba Ptrofs.zero) -> le!_bzinv=Some (Vptr bb Ptrofs.zero) ->
 e!_bzinv2=Some (b2,curve_fe_type) -> e!_bzinv3=Some (b3,curve_fe_type) ->
 e!_secp256k1_fe_sqr=None -> e!_secp256k1_fe_mul=None -> e!_secp256k1_fe_set_int=None ->
 NoDup [bp;ba;bb;b2;b3] -> aflag<>Int.zero ->
 Mem.load Mint32 m bp 120=Some (Vint aflag) -> Mem.load Mint32 m ba 80=Some (Vint flag) ->
 square_input_bounds u -> square_input_bounds v -> square_input_bounds inv ->
 fe_at m ba 0 (words5 u) -> fe_at m ba 40 (words5 v) -> fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (fn_body f_secp256k1_gej_add_zinv_var) E0
   (zinv_infinite_temps le aflag flag) mf (Out_return None) /\
 fe_at mf bp 0 (words5 (point_mul_words u (square_words inv))) /\
 fe_at mf bp 40 (words5 (point_mul_words v (zinv_inverse_cube inv))) /\
 fe_at mf bp 80 (words5 (point_set_bit_words (Int.eq flag Int.zero))) /\
 Mem.load Mint32 mf bp 120=Some (Vint flag) /\
 fe_at mf ba 0 (words5 u) /\ fe_at mf ba 40 (words5 v) /\ fe_at mf bb 0 (words5 inv) /\
 fe_at mf b2 0 (words5 (square_words inv)) /\ fe_at mf b3 0 (words5 (zinv_inverse_cube inv)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\ Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
 square_input_bounds (point_mul_words u (square_words inv)) /\
 square_input_bounds (point_mul_words v (zinv_inverse_cube inv)) /\
 square_input_bounds (point_set_bit_words (Int.eq flag Int.zero)) /\
 lframe (fun bx _=>bx<>bp /\bx<>ba /\bx<>bb /\bx<>b2 /\bx<>b3) m mf.
Proof.
 intros HA HR HB HI E2 E3 EQ EM EI Sep ANZ FlagA FlagB BU BV BI U V Inv PF AF InvF F2 F3.
 pose proof Sep as SepAll;separate_blocks Sep.
 set (la := PTree.set _t'4 (Vint aflag) le).
 set (lb := PTree.set _t'6 (Vint flag) la).
 assert (HRA : la!_r=Some (Vptr bp Ptrofs.zero)) by (unfold la;rewrite PTree.gso by discriminate;exact HR).
 assert (HBA : la!_b=Some (Vptr ba Ptrofs.zero)) by (unfold la;rewrite PTree.gso by discriminate;exact HB).
 destruct (exec_zinv_infinite_flag e la m bp ba flag HRA HBA FlagB PF) as (ms & Copy & FlagS & PFS & FS).
 assert (US : fe_at ms ba 0 (words5 u)) by (keep_field U FS).
 assert (VS : fe_at ms ba 40 (words5 v)) by (keep_field V FS).
 assert (InvS : fe_at ms bb 0 (words5 inv)) by (keep_field Inv FS).
 assert (AFS : Mem.range_perm ms ba 0 88 Cur Freeable) by (keep_free AF FS).
 assert (InvFS : Mem.range_perm ms bb 0 40 Cur Freeable) by (keep_free InvF FS).
 assert (F2S : Mem.range_perm ms b2 0 40 Cur Freeable) by (keep_free F2 FS).
 assert (F3S : Mem.range_perm ms b3 0 40 Cur Freeable) by (keep_free F3 FS).
 assert (HRB : lb!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lb,la;rewrite !PTree.gso by discriminate;exact HR).
 assert (HBB : lb!_b=Some (Vptr ba Ptrofs.zero)) by (unfold lb,la;rewrite !PTree.gso by discriminate;exact HB).
 assert (HIB : lb!_bzinv=Some (Vptr bb Ptrofs.zero)) by (unfold lb,la;rewrite !PTree.gso by discriminate;exact HI).
 destruct (exec_zinv_infinite_products u v inv e lb ms bp ba bb b2 b3 HRB HBB HIB E2 E3 EQ EM SepAll
   BU BV BI US VS InvS PFS AFS InvFS F2S F3S)
   as (mp & Products & XP & YP & UP & VP & InvP & QP & CP & PFP & AFP & InvFP & F2P & F3P & BX & BY & FP).
 assert (FlagP : Mem.load Mint32 mp bp 120=Some (Vint flag)).
 { rewrite (proj1 FP Mint32 bp 120);[exact FlagS| |].
   - eapply Mem.perm_valid_block;apply (PFS 0);lia.
   - intros pos Range;unfold zinv_infinite_products_frame;split;[right;right;clear - Range;change (120<=pos<124) in Range;lia|].
     split;[left;congruence|];repeat split;congruence. }
 destruct (exec_zinv_infinite_z e lb mp bp flag HRB EI FlagP PFP) as (mf & SetZ & ZO & FlagO & PFO & FZ).
 assert (XO : fe_at mf bp 0 (words5 (point_mul_words u (square_words inv)))).
 { eapply curve_keep_field_range;[reflexivity|exact XP|exact FZ|];intros pos Range;right;left;clear - Range;lia. }
 assert (YO : fe_at mf bp 40 (words5 (point_mul_words v (zinv_inverse_cube inv)))).
 { eapply curve_keep_field_range;[reflexivity|exact YP|exact FZ|];intros pos Range;right;left;clear - Range;lia. }
 assert (UO : fe_at mf ba 0 (words5 u)) by (keep_field UP FZ).
 assert (VO : fe_at mf ba 40 (words5 v)) by (keep_field VP FZ).
 assert (InvO : fe_at mf bb 0 (words5 inv)) by (keep_field InvP FZ).
 assert (QO : fe_at mf b2 0 (words5 (square_words inv))) by (keep_field QP FZ).
 assert (CO : fe_at mf b3 0 (words5 (zinv_inverse_cube inv))) by (keep_field CP FZ).
 assert (AFO : Mem.range_perm mf ba 0 88 Cur Freeable) by (keep_free AFP FZ).
 assert (InvFO : Mem.range_perm mf bb 0 40 Cur Freeable) by (keep_free InvFP FZ).
 assert (F2O : Mem.range_perm mf b2 0 40 Cur Freeable) by (keep_free F2P FZ).
 assert (F3O : Mem.range_perm mf b3 0 40 Cur Freeable) by (keep_free F3P FZ).
 assert (BZ : square_input_bounds (point_set_bit_words (Int.eq flag Int.zero))) by apply zinv_set_bit_bounds.
 assert (Frame : lframe (fun bx _=>bx<>bp /\bx<>ba /\bx<>bb /\bx<>b2 /\bx<>b3) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact FS|];intros bx pos (NP & NA & NB & N2 & N3) Valid;left;exact NP.
   - eapply lframe_trans.
     + eapply lframe_implies;[exact FP|];intros bx pos (NP & NA & NB & N2 & N3) Valid.
       unfold zinv_infinite_products_frame;repeat split;try assumption;left;assumption.
     + eapply lframe_implies;[exact FZ|];intros bx pos (NP & NA & NB & N2 & N3) Valid;left;exact NP. }
 exists mf;split.
 - rewrite zinv_body_source;eapply exec_Sseq_2;[|discriminate].
   rewrite zinv_infinite_head_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=la).
   + apply exec_Sset;eapply eval_Elvalue.
     * apply eval_double_flag_field;exact HA.
     * eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact FlagA].
   + eapply exec_Sifthenelse with (v1:=Vint aflag) (b:=true).
     * apply eval_Etempvar;unfold la;apply PTree.gss.
     * change (Some (negb (Int.eq aflag Int.zero))=Some true);rewrite Int.eq_false by exact ANZ;reflexivity.
     * rewrite zinv_infinite_branch_source.
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=ms) (le1:=lb);[exact Copy|].
       rewrite zinv_infinite_products_source;eapply exec_statement_prefix_then_last;[exact Products|].
       rewrite zinv_infinite_z_source.
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _t'5 (Vint flag) lb);[exact SetZ|].
       apply exec_Sreturn_none.
 - repeat first [assumption|split].
Qed.
