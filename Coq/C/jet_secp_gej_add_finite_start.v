(** Actual finite projective-addition dispatch and both Z squares.
    The selected point-coordinate square execution and bounds are reused. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_double_statements
 C.jet_secp_double_flag C.jet_secp_fe_nv C.jet_secp_point_square_coordinate
 C.jet_secp_point_write_run C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_square_numeric C.jet_secp_statement_prefix C.jet_secp_gej_add_statements.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words.

Definition gej_add_flag_head (second : bool) := nth (if second then 1 else 0) gej_add_statements Sskip.
Definition gej_add_square_stmt (second : bool) := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
 [curve_local_address (if second then _z22 else _z12);double_point_address (if second then _b else _a) _z].
Definition gej_add_start := statement_sequence (firstn 4 gej_add_statements) Sskip.
Definition gej_add_squares_frame (ba bb b22 b12 b : block) (pos : Z) :=
 b<>b22 /\ b<>b12 /\ (b<>ba \/ pos<80 \/ 120<=pos) /\ (b<>bb \/ pos<80 \/ 120<=pos).
Lemma gej_add_start_source : gej_add_start=
 statement_sequence [gej_add_flag_head false;gej_add_flag_head true;
   gej_add_square_stmt true;gej_add_square_stmt false] Sskip.
Proof. reflexivity. Qed.

Lemma exec_gej_add_flag_finite (second : bool) e le m bp :
 le!(if second then _b else _a)=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mint32 m bp 120=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge e le m (gej_add_flag_head second) E0
  (PTree.set (if second then _t'3 else _t'4) (Vint Int.zero) le) m Out_normal.
Proof.
 intros Param Flag;destruct second;unfold gej_add_flag_head;
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
 all: try solve [apply exec_Sset;eapply eval_Elvalue;
   [apply eval_double_flag_field;exact Param|eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Flag]]].
 all: eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
   [apply eval_Etempvar;apply PTree.gss|reflexivity|apply exec_Sskip].
Qed.

Lemma exec_gej_add_square_call (second : bool) e le m mf bp bo :
 le!(if second then _b else _a)=Some (Vptr bp Ptrofs.zero) ->
 e!(if second then _z22 else _z12)=Some (bo,curve_fe_type) -> e!_secp256k1_fe_sqr=None ->
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
  [Vptr bo Ptrofs.zero;Vptr bp (Ptrofs.repr 80)] E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (gej_add_square_stmt second) E0 le mf Out_normal.
Proof.
 intros Param Local Global Call;unfold gej_add_square_stmt.
 eapply exec_curve_call with (vargs:=[Vptr bo Ptrofs.zero;Vptr bp (Ptrofs.repr 80)]) (v:=Vundef).
 - unfold secp_pure;repeat (first [left;reflexivity|right]).
 - exact Global.
 - eapply eval_Econs;[apply eval_curve_local;exact Local|reflexivity|].
   eapply eval_Econs.
   + apply eval_double_point_address;[cbn [In];tauto|exact Param].
   + reflexivity.
   + constructor.
 - exact Call.
Qed.

Theorem exec_gej_add_finite_start e le m ba bb b22 b12 za zb :
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_b=Some (Vptr bb Ptrofs.zero) ->
 e!_z22=Some (b22,curve_fe_type) -> e!_z12=Some (b12,curve_fe_type) -> e!_secp256k1_fe_sqr=None ->
 NoDup [ba;bb;b22;b12] ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) -> Mem.load Mint32 m bb 120=Some (Vint Int.zero) ->
 square_input_bounds za -> square_input_bounds zb -> fe_at m ba 80 (words5 za) -> fe_at m bb 80 (words5 zb) ->
 Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m bb 0 128 Cur Freeable ->
 Mem.range_perm m b22 0 40 Cur Freeable -> Mem.range_perm m b12 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m gej_add_start E0
  (PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le)) mf Out_normal /\
 fe_at mf b22 0 (words5 (square_words zb)) /\ fe_at mf b12 0 (words5 (square_words za)) /\
 fe_at mf ba 80 (words5 za) /\ fe_at mf bb 80 (words5 zb) /\
 Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 128 Cur Freeable /\
 Mem.range_perm mf b22 0 40 Cur Freeable /\ Mem.range_perm mf b12 0 40 Cur Freeable /\
 square_input_bounds (square_words za) /\ square_input_bounds (square_words zb) /\
 lframe (gej_add_squares_frame ba bb b22 b12) m mf.
Proof.
 intros A B E22 E12 EQ Sep FlagA FlagB BoundA BoundB ZA ZB FA FB F22 F12.
 assert (AB : ba<>bb) by (intro;subst bb;inversion Sep;cbn in *;tauto).
 assert (A22 : ba<>b22) by (intro;subst b22;inversion Sep;cbn in *;tauto).
 assert (A12 : ba<>b12) by (intro;subst b12;inversion Sep;cbn in *;tauto).
 assert (B22 : bb<>b22) by (intro;subst b22;repeat rewrite NoDup_cons_iff in Sep;cbn in Sep;tauto).
 assert (B12 : bb<>b12) by (intro;subst b12;repeat rewrite NoDup_cons_iff in Sep;cbn in Sep;tauto).
 assert (S2212 : b22<>b12) by (intro;subst b12;repeat rewrite NoDup_cons_iff in Sep;cbn in Sep;tauto).
 destruct (eval_point_square_coordinate PointZ zb m b22 bb BoundB F22 ZB FB ltac:(congruence))
   as (mi & C22 & Z22 & F22I & ZBI & FBI & ValB & Bound22 & Tight22 & Frame22).
 assert (ZAI : fe_at mi ba 80 (words5 za)).
 { eapply curve_keep_field_range;[reflexivity|exact ZA|exact Frame22|].
   intros pos Pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 assert (FAI : Mem.range_perm mi ba 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FA|exact Frame22|].
   intros pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 assert (F12I : Mem.range_perm mi b12 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F12|exact Frame22|].
   intros pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 destruct (eval_point_square_coordinate PointZ za mi b12 ba BoundA F12I ZAI FAI ltac:(congruence))
   as (mf & C12 & Z12 & F12F & ZAF & FAF & ValA & Bound12 & Tight12 & Frame12).
 assert (Z22F : fe_at mf b22 0 (words5 (square_words zb))).
 { eapply curve_keep_field_range;[reflexivity|exact Z22|exact Frame12|].
   intros pos Pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 assert (ZBF : fe_at mf bb 80 (words5 zb)).
 { eapply curve_keep_field_range;[reflexivity|exact ZBI|exact Frame12|].
   intros pos Pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 assert (FBF : Mem.range_perm mf bb 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact FBI|exact Frame12|].
   intros pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 assert (F22F : Mem.range_perm mf b22 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact F22I|exact Frame12|].
   intros pos;unfold point_square_coordinate_frame;intros [[HE _]|[HE _]];congruence. }
 exists mf;split.
 - rewrite gej_add_start_source;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'4 (Vint Int.zero) le).
   + apply exec_gej_add_flag_finite with (bp:=ba);assumption.
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _t'3 (Vint Int.zero) (PTree.set _t'4 (Vint Int.zero) le)).
     * apply exec_gej_add_flag_finite with (bp:=bb);[rewrite PTree.gso by discriminate;exact B|exact FlagB].
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mi).
       -- eapply exec_gej_add_square_call;[rewrite !PTree.gso by discriminate;exact B|exact E22|exact EQ|exact C22].
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf).
          ++ eapply exec_gej_add_square_call;[rewrite !PTree.gso by discriminate;exact A|exact E12|exact EQ|exact C12].
          ++ apply exec_Sskip.
 - split;[exact Z22F|];split;[exact Z12|];split;[exact ZAF|];split;[exact ZBF|].
   split;[exact FAF|];split;[exact FBF|];split;[exact F22F|];split;[exact F12F|].
   split;[exact Bound12|];split;[exact Bound22|];eapply lframe_trans.
   + eapply lframe_implies;[exact Frame22|];intros b pos (N22 & N12 & NA & NB) VB.
     unfold point_square_coordinate_frame;intros [[HE _]|[HE HP]];[congruence|].
     subst b;destruct NB as [NB|[NB|NB]];[contradiction|cbn [point_coordinate_offset] in HP;lia|cbn [point_coordinate_offset] in HP;lia].
   + eapply lframe_implies;[exact Frame12|];intros b pos (N22 & N12 & NA & NB) VB.
     unfold point_square_coordinate_frame;intros [[HE _]|[HE HP]];[congruence|].
     subst b;destruct NA as [NA|[NA|NA]];[contradiction|cbn [point_coordinate_offset] in HP;lia|cbn [point_coordinate_offset] in HP;lia].
Qed.
