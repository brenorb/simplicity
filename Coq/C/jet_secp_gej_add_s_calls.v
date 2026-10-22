(** The two original S1/S2 preparation multiplications, shared through the
    actual local/point identifiers and retaining both complete point owners. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_point_multiply C.jet_secp_point_write_run
 C.jet_secp_curve_statements C.jet_secp_double_statements C.jet_secp_curve_square
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_gej_fresh_product
 C.jet_secp_gej_add_statements C.jet_secp_field_mul_small.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Definition gej_add_s_first (second : bool) := gej_fresh_product_stmt true
 (if second then _s2 else _s1) (if second then _b else _a) (if second then _z12 else _z22).
Definition gej_add_s_second (second : bool) := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address (if second then _s2 else _s1);curve_local_address (if second then _s2 else _s1);
  double_point_address (if second then _a else _b) _z].
Definition gej_add_s_frame (py pz bs bz b : block) (pos : Z) :=
 b<>bs /\ b<>bz /\ (b<>py \/ pos<40 \/ 80<=pos) /\ (b<>pz \/ pos<80 \/ 120<=pos).

Lemma gej_add_s_source : gej_add_after 6=
 Ssequence (gej_add_s_first false) (Ssequence (gej_add_s_second false)
  (Ssequence (gej_add_s_first true) (Ssequence (gej_add_s_second true) (gej_add_after 10)))).
Proof. reflexivity. Qed.

Theorem exec_gej_add_s_calls (second : bool) e le m py pz bs bz y t z :
 le!(if second then _b else _a)=Some (Vptr py Ptrofs.zero) ->
 le!(if second then _a else _b)=Some (Vptr pz Ptrofs.zero) ->
 e!(if second then _s2 else _s1)=Some (bs,curve_fe_type) ->
 e!(if second then _z12 else _z22)=Some (bz,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 py<>pz -> py<>bs -> py<>bz -> bs<>pz -> bs<>bz -> pz<>bz ->
 square_input_bounds y -> square_input_bounds t -> square_input_bounds z ->
 fe_at m py 40 (words5 y) -> fe_at m bz 0 (words5 t) -> fe_at m pz 80 (words5 z) ->
 Mem.range_perm m py 0 128 Cur Freeable -> Mem.range_perm m pz 0 128 Cur Freeable ->
 Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable -> exists m1 mf,
 Clight2.exec_stmt secp_ge e le m (gej_add_s_first second) E0 le m1 Out_normal /\
 Clight2.exec_stmt secp_ge e le m1 (gej_add_s_second second) E0 le mf Out_normal /\
 fe_at mf bs 0 (words5 (point_mul_words (point_mul_words y t) z)) /\
 fe_at mf py 40 (words5 y) /\ fe_at mf bz 0 (words5 t) /\ fe_at mf pz 80 (words5 z) /\
 Mem.range_perm mf py 0 128 Cur Freeable /\ Mem.range_perm mf pz 0 128 Cur Freeable /\
 Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 radix_value (point_mul_words (point_mul_words y t) z) mod feP=
   (radix_value y*radix_value t*radix_value z) mod feP /\
 square_input_bounds (point_mul_words (point_mul_words y t) z) /\
 mul_small_input_bounds (point_mul_words (point_mul_words y t) z) /\
 lframe (gej_add_s_frame py pz bs bz) m mf.
Proof.
 intros PY PZ ES EZ EM YZ YS YT SZ ST ZT BY BT BZ Y T Z FY FZ FS FT.
 destruct (exec_gej_fresh_product true (if second then _s2 else _s1)
   (if second then _b else _a) (if second then _z12 else _z22) y t e le m bs py bz
   ES PY EZ EM BY BT ltac:(congruence) ST YT FS Y FY T FT)
   as (m1 & C1 & S1 & Y1 & T1 & FS1 & FY1 & FT1 & V1 & B1 & F1).
 assert (OutZ : forall pos, pz<>bs /\ pz<>bz /\ (pz<>py \/ pos<40 \/ 80<=pos)).
 { intro pos;split;[congruence|];split;[exact ZT|];left;congruence. }
 pose proof (field_at_lframe m m1 pz 80 _ _ Z F1 OutZ) as Z1.
 pose proof (curve_keep_free _ m m1 pz 128 ltac:(lia) FZ F1 OutZ) as FZ1.
 destruct (eval_field_point_mul_numeric PointZ (point_mul_words y t) z m1 bs pz B1 BZ SZ S1 FS1 Z1 FZ1)
   as (mf & C2 & S2 & FS2 & Z2 & FZ2 & V2 & B2 & Tight & F2).
 assert (OutY : forall pos, ~((py=bs /\ 0<=pos<40) \/ (py=pz /\ 80<=pos<120)))
   by (intros pos [[HE _]|[HE _]];congruence).
 assert (OutT : forall pos, ~((bz=bs /\ 0<=pos<40) \/ (bz=pz /\ 80<=pos<120)))
   by (intros pos [[HE _]|[HE _]];congruence).
 pose proof (field_at_lframe m1 mf py 40 _ _ Y1 F2 OutY) as Y2.
 pose proof (field_at_lframe m1 mf bz 0 _ _ T1 F2 OutT) as T2.
 pose proof (curve_keep_free _ m1 mf py 128 ltac:(lia) FY1 F2 OutY) as FY2.
 pose proof (curve_keep_free _ m1 mf bz 40 ltac:(lia) FT1 F2 OutT) as FT2.
 exists m1,mf;split;[exact C1|];split.
 - unfold gej_add_s_second;eapply exec_curve_call with
    (vargs:=[Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero;Vptr pz (Ptrofs.repr 80)]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact EM.
   + eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|].
     eapply eval_Econs with (v1:=Vptr pz (Ptrofs.repr 80));
       [apply eval_double_point_address;[cbn [In];tauto|exact PZ]|reflexivity|constructor].
   + exact C2.
 - split;[exact S2|];split;[exact Y2|];split;[exact T2|];split;[exact Z2|];
   split;[exact FY2|];split;[exact FZ2|];split;[exact FS2|];split;[exact FT2|];split.
   + rewrite V2,(Z.mul_mod (radix_value (point_mul_words y t)) (radix_value z) feP),V1,
       <-Z.mul_mod by (unfold feP,feR;lia);reflexivity.
   + split;[exact B2|];split;[exact Tight|];eapply lframe_trans.
     * eapply lframe_implies;[exact F1|];intros b pos (NS & NT & NY & NZ) VB;split;[exact NS|];split;assumption.
     * eapply lframe_implies;[exact F2|];intros b pos (NS & NT & NY & NZ) VB [[HE HP]|[HE HP]];
         [contradiction|subst b;change (80<=pos<120) in HP;destruct NZ as [NZ|[NZ|NZ]];[contradiction|lia|lia]].
Qed.
