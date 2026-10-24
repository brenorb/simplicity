(** The original ge_set_gej_var arithmetic after inversion.  The input Z
    here is the already-inverted field; establishing that earlier call is
    deliberately not assumed to be a completed public jet proof. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events Errors.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_sx_rep C.jet_sx_expr.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_point_write_run.
Require Import C.jet_secp_point_square_coordinate C.jet_secp_square_columns C.jet_secp_square_numeric.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product.
Require Import C.jet_secp_multiply_checkpoint_columns.
Require Import C.jet_secp_point_mul_numeric C.jet_secp_point_mul_storage C.jet_secp_point_mul_run.
Require Import C.jet_secp_gej_affine_cube C.jet_secp_local_regions.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge square_words point_mul_words.

Definition affine_point_type := Tstruct __6123 noattr.
Definition affine_point_field fid ty :=
  Efield (Ederef (Etempvar _a (tptr affine_point_type)) affine_point_type) fid ty.
Definition affine_point_address fid := Eaddrof (affine_point_field fid curve_fe_type) (tptr curve_fe_type).
Definition affine_local_env b2 b3 :=
  PTree.set _z3 (b3,curve_fe_type) (PTree.set _z2 (b2,curve_fe_type) empty_env).
Definition affine_square_statement := curve_call _secp256k1_fe_sqr f_secp256k1_fe_sqr None
  [curve_local_address _z2;affine_point_address _z].
Definition affine_cube_statement := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _z3;affine_point_address _z;curve_local_address _z2].
Definition affine_coordinate_statement (y : bool) := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [affine_point_address (if y then _y else _x);affine_point_address (if y then _y else _x);
   curve_local_address (if y then _z3 else _z2)].
Definition affine_arithmetic_context tail := Ssequence affine_square_statement
  (Ssequence affine_cube_statement (Ssequence (affine_coordinate_statement false)
    (Ssequence (affine_coordinate_statement true) tail))).
Definition affine_finish_statement :=
  match fn_body f_secp256k1_ge_set_gej_var with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ tail))))) => tail
  | _ => Sskip end.
Lemma affine_arithmetic_source : fn_body f_secp256k1_ge_set_gej_var =
  match fn_body f_secp256k1_ge_set_gej_var with
  | Ssequence flag (Ssequence inv _) => Ssequence flag (Ssequence inv (affine_arithmetic_context affine_finish_statement))
  | _ => Sskip end.
Proof. reflexivity. Qed.

Lemma affine_point_layout fid delta : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)] ->
  exists co, (genv_cenv secp_ge)!__6123 = Some co /\
  field_offset secp_ge fid (co_members co) = OK (delta,Full).
Proof.
  intro H.
  assert (HM : option_map co_members ((genv_cenv secp_ge)!__6123) =
    Some [Member_plain _x curve_fe_type;Member_plain _y curve_fe_type;
          Member_plain _z curve_fe_type;Member_plain _infinity tint]) by (vm_compute;reflexivity).
  destruct ((genv_cenv secp_ge)!__6123) as [co|] eqn:HC;[|discriminate].
  exists co;split;[reflexivity|]. inversion HM as [HMembers];rewrite HMembers.
  destruct H as [H|[H|[H|[H|H]]]];try contradiction;inversion H;subst;vm_compute;reflexivity.
Qed.
Lemma eval_affine_point_address e le m bp fid delta :
  In (fid,delta) [(_x,0);(_y,40);(_z,80)] -> le!_a=Some(Vptr bp Ptrofs.zero) ->
  eval_expr secp_ge e le m (affine_point_address fid) (Vptr bp (Ptrofs.repr delta)).
Proof.
  intros H HA. assert (HAll : In (fid,delta) [(_x,0);(_y,40);(_z,80);(_infinity,120)])
    by (cbn [In] in *;tauto).
  destruct (affine_point_layout fid delta HAll) as (co & HC & HO).
  apply eval_Eaddrof. unfold affine_point_field,affine_point_type.
  rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Efield_struct with (co:=co) (delta:=delta).
  - eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact HA|].
    apply deref_loc_copy;reflexivity.
  - reflexivity.
  - exact HC.
  - exact HO.
Qed.

Local Ltac affine_arguments HA :=
  first [apply eval_Enil | eapply eval_Econs;
    [first [apply eval_curve_local;reflexivity |
            apply eval_affine_point_address;[cbn [In];tauto|exact HA]]
    |reflexivity|affine_arguments HA]].
Local Ltac affine_symbol := unfold secp_pure;repeat (first [left;reflexivity|right]).

Lemma exec_affine_arithmetic_from_calls le m m1 m2 m3 mf bp b2 b3 :
  le!_a=Some(Vptr bp Ptrofs.zero) ->
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_sqr)
    [Vptr b2 Ptrofs.zero;Vptr bp (Ptrofs.repr 80)] E0 m1 Vundef ->
  Clight2.eval_funcall secp_ge m1 (Internal f_secp256k1_fe_mul)
    [Vptr b3 Ptrofs.zero;Vptr bp (Ptrofs.repr 80);Vptr b2 Ptrofs.zero] E0 m2 Vundef ->
  Clight2.eval_funcall secp_ge m2 (Internal f_secp256k1_fe_mul)
    [Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr b2 Ptrofs.zero] E0 m3 Vundef ->
  Clight2.eval_funcall secp_ge m3 (Internal f_secp256k1_fe_mul)
    [Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vptr b3 Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m (affine_arithmetic_context Sskip) E0 le mf Out_normal.
Proof.
  intros HA C1 C2 C3 C4;unfold affine_arithmetic_context.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
  - eapply exec_curve_call with (vargs:=[Vptr b2 Ptrofs.zero;Vptr bp (Ptrofs.repr 80)]) (v:=Vundef).
    + affine_symbol.
    + reflexivity.
    + affine_arguments HA.
    + exact C1.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le).
    + eapply exec_curve_call with (vargs:=[Vptr b3 Ptrofs.zero;Vptr bp (Ptrofs.repr 80);Vptr b2 Ptrofs.zero]) (v:=Vundef).
      * affine_symbol.
      * reflexivity.
      * affine_arguments HA.
      * exact C2.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m3) (le1:=le).
      * eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr b2 Ptrofs.zero]) (v:=Vundef).
        -- affine_symbol.
        -- reflexivity.
        -- affine_arguments HA.
        -- exact C3.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=le).
        -- eapply exec_curve_call with (vargs:=[Vptr bp (Ptrofs.repr 40);Vptr bp (Ptrofs.repr 40);Vptr b3 Ptrofs.zero]) (v:=Vundef).
           ++ affine_symbol.
           ++ reflexivity.
           ++ affine_arguments HA.
           ++ exact C4.
        -- apply exec_Sskip.
Qed.

Lemma affine_point_mul_foot k bp bs bx pos :
  foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos ->
  (bx=bp /\ point_coordinate_offset k<=pos<point_coordinate_offset k+40) \/ (bx=bs /\ 0<=pos<40).
Proof.
  intros (r & sh & d & ch & HN & HC & HB & HO).
  destruct r as [|[|r]].
  - left;split;[exact HB|].
    cbn [point_mul_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [rcells u64_cells vars5 rshape map cshape cofs cchunk fst] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]];try contradiction;
      inversion HC;subst d ch;cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO;lia.
  - right;split;[exact HB|].
    cbn [point_mul_regs map nth_error rshape rcells rw rfree] in HN;injection HN as <-.
    cbn [free_region fe_reg rcells u64_cells vars5 rshape map cshape cofs cchunk fst] in HC.
    destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]];try contradiction;
      inversion HC;subst d ch;cbn [bas lay nth snd] in HO;
      change (size_chunk Mint64) with 8 in HO;lia.
  - destruct r;discriminate HN.
Qed.

Definition affine_arithmetic_frame (bp b2 b3 bx : block) pos :=
  ~((bx=bp /\ 0<=pos<120) \/ (bx=b2 /\ 0<=pos<40) \/ (bx=b3 /\ 0<=pos<40)).

Definition affine_mul_frame k (bp bs bx : block) pos :=
  ~((bx=bp /\ point_coordinate_offset k<=pos<point_coordinate_offset k+40) \/ (bx=bs /\ 0<=pos<40)).
Definition affine_cube_frame (bo bp bs bx : block) pos :=
  ~((bx=bo /\ 0<=pos<40) \/ (bx=bp /\ 80<=pos<120) \/ (bx=bs /\ 0<=pos<40)).
Lemma affine_mul_frame_from_foot k bp bs m mf :
  lframe (fun bx pos=>~foot [(bp,0);(bs,0)] (map rshape (point_mul_regs k)) bx pos) m mf ->
  lframe (affine_mul_frame k bp bs) m mf.
Proof.
  intro HF;eapply lframe_implies;[exact HF|].
  intros bx pos Outside Valid Inside;apply Outside;exact (affine_point_mul_foot k bp bs bx pos Inside).
Qed.
Lemma affine_cube_frame_from_foot bo bp bs m mf :
  lframe (fun bx pos=>~foot [(bo,0);(bp,0);(bs,0)] (map rshape affine_cube_regs) bx pos) m mf ->
  lframe (affine_cube_frame bo bp bs) m mf.
Proof.
  intro HF;eapply lframe_implies;[exact HF|].
  intros bx pos Outside Valid Inside;apply Outside;exact (affine_cube_foot bo bp bs bx pos Inside).
Qed.

Local Ltac affine_range :=
  unfold affine_mul_frame,affine_cube_frame,point_square_coordinate_frame,point_coordinate_offset;
  intuition congruence.
Local Ltac affine_keep_field HF HL :=
  eapply curve_keep_field_range;[reflexivity|exact HF|exact HL|];
  intros pos HP;unfold affine_mul_frame,affine_cube_frame,point_square_coordinate_frame,point_coordinate_offset;
  intros Inside;destruct Inside as [[HE HR]|Inside];
  [first [congruence|lia]|repeat match type of Inside with
     | _ \/ _ => destruct Inside as [[HE HR]|Inside];[first [congruence|lia]|]
     end;destruct Inside as [HE HR];first [congruence|lia]].

Theorem exec_affine_arithmetic le m bp b2 b3 x y zi :
  le!_a=Some(Vptr bp Ptrofs.zero) ->
  bp<>b2 -> bp<>b3 -> b2<>b3 ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
  fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 zi) ->
  Mem.range_perm m bp 0 128 Cur Freeable ->
  Mem.range_perm m b2 0 40 Cur Freeable -> Mem.range_perm m b3 0 40 Cur Freeable -> exists mf,
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m (affine_arithmetic_context Sskip) E0 le mf Out_normal /\
  fe_at mf bp 0 (words5 (point_mul_words x (square_words zi))) /\
  fe_at mf bp 40 (words5 (point_mul_words y (point_mul_words zi (square_words zi)))) /\
  fe_at mf bp 80 (words5 zi) /\
  fe_at mf b2 0 (words5 (square_words zi)) /\
  fe_at mf b3 0 (words5 (point_mul_words zi (square_words zi))) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  square_input_bounds (point_mul_words x (square_words zi)) /\
  square_input_bounds (point_mul_words y (point_mul_words zi (square_words zi))) /\
  radix_value (point_mul_words x (square_words zi)) mod field_prime =
    (radix_value x * (radix_value zi * radix_value zi)) mod field_prime /\
  radix_value (point_mul_words y (point_mul_words zi (square_words zi))) mod field_prime =
    (radix_value y * (radix_value zi * (radix_value zi * radix_value zi))) mod field_prime /\
  lframe (affine_arithmetic_frame bp b2 b3) m mf.
Proof.
  intros HA P2 P3 N23 BX BY BZ X Y Z FP F2 F3.
  destruct (eval_point_square_coordinate PointZ zi m b2 bp BZ F2 Z FP ltac:(congruence))
    as (m1 & C1 & S1 & FS1 & Z1 & FP1 & VS & BS & Tight & L1).
  assert (X1 : fe_at m1 bp 0 (words5 x)) by (affine_keep_field X L1).
  assert (Y1 : fe_at m1 bp 40 (words5 y)) by (affine_keep_field Y L1).
  assert (F31 : Mem.range_perm m1 b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3|exact L1|];intro pos;affine_range. }
  destruct (eval_affine_cube_owned zi (square_words zi) m1 b3 bp b2 BZ BS
    ltac:(congruence) ltac:(congruence) P2 F31 Z1 FP1 S1 FS1)
    as (m2 & C2 & T2 & Z2 & S2 & FT2 & FP2 & FS2 & VT & BT & Raw2).
  pose proof (affine_cube_frame_from_foot b3 bp b2 m1 m2 Raw2) as L2.
  assert (X2 : fe_at m2 bp 0 (words5 x)) by (affine_keep_field X1 L2).
  assert (Y2 : fe_at m2 bp 40 (words5 y)) by (affine_keep_field Y1 L2).
  destruct (eval_point_mul_numeric PointX x (square_words zi) m2 bp b2 BX BS P2 X2 FP2 S2 FS2)
    as (m3 & C3 & X3 & FP3 & S3 & FS3 & VX & BXO & Raw3).
  pose proof (affine_mul_frame_from_foot PointX bp b2 m2 m3 Raw3) as L3.
  assert (Y3 : fe_at m3 bp 40 (words5 y)) by (affine_keep_field Y2 L3).
  assert (Z3 : fe_at m3 bp 80 (words5 zi)) by (affine_keep_field Z2 L3).
  assert (T3 : fe_at m3 b3 0 (words5 (point_mul_words zi (square_words zi)))) by (affine_keep_field T2 L3).
  assert (FT3 : Mem.range_perm m3 b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FT2|exact L3|];intro pos;affine_range. }
  destruct (eval_point_mul_numeric PointY y (point_mul_words zi (square_words zi)) m3 bp b3 BY BT P3 Y3 FP3 T3 FT3)
    as (mf & C4 & Y4 & FP4 & T4 & FT4 & VY & BYO & Raw4).
  pose proof (affine_mul_frame_from_foot PointY bp b3 m3 mf Raw4) as L4.
  assert (X4 : fe_at mf bp 0 (words5 (point_mul_words x (square_words zi)))) by (affine_keep_field X3 L4).
  assert (Z4 : fe_at mf bp 80 (words5 zi)) by (affine_keep_field Z3 L4).
  assert (S4 : fe_at mf b2 0 (words5 (square_words zi))) by (affine_keep_field S3 L4).
  assert (FS4 : Mem.range_perm mf b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FS3|exact L4|];intro pos;affine_range. }
  assert (PN : field_prime<>0) by (vm_compute;discriminate).
  change (radix_value (point_mul_words zi (square_words zi)) mod field_prime =
    (radix_value zi * radix_value (square_words zi)) mod field_prime) in VT.
  assert (FX : radix_value (point_mul_words x (square_words zi)) mod field_prime =
    (radix_value x * (radix_value zi * radix_value zi)) mod field_prime).
  { rewrite VX, <- (Z.mul_mod_idemp_r _ _ field_prime), VS, Z.mul_mod_idemp_r by exact PN;reflexivity. }
  assert (FY : radix_value (point_mul_words y (point_mul_words zi (square_words zi))) mod field_prime =
    (radix_value y * (radix_value zi * (radix_value zi * radix_value zi))) mod field_prime).
  { rewrite VY.
    rewrite (Z.mul_mod (radix_value y) (radix_value (point_mul_words zi (square_words zi))) field_prime),
      (Z.mul_mod (radix_value y) (radix_value zi * (radix_value zi * radix_value zi)) field_prime) by exact PN.
    rewrite VT.
    rewrite (Z.mul_mod (radix_value zi) (radix_value (square_words zi)) field_prime),
      (Z.mul_mod (radix_value zi) (radix_value zi * radix_value zi) field_prime) by exact PN.
    rewrite VS;reflexivity. }
  assert (Frame : lframe (affine_arithmetic_frame bp b2 b3) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact L1|].
      intros bx pos Outside Valid Inside;apply Outside.
      unfold point_square_coordinate_frame,point_coordinate_offset in Inside.
      unfold affine_arithmetic_frame;intuition lia.
    - eapply lframe_trans.
      + eapply lframe_implies;[exact L2|].
        intros bx pos Outside Valid Inside;apply Outside;unfold affine_cube_frame in Inside.
        unfold affine_arithmetic_frame;intuition lia.
      + eapply lframe_trans; eapply lframe_implies;[exact L3| |exact L4|];
          intros bx pos Outside Valid Inside;apply Outside;
          unfold affine_mul_frame,point_coordinate_offset in Inside;
          unfold affine_arithmetic_frame;intuition lia. }
  exists mf;split.
  - eapply exec_affine_arithmetic_from_calls;[exact HA|exact C1|exact C2|exact C3|exact C4].
  - repeat first [assumption|split].
Qed.
