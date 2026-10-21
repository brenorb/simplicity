(** The two consecutive original multiplications preparing S2 in mixed
    addition, with ownership and residues derived from the initial fields. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
  C.jet_secp_square_columns C.jet_secp_field_point_multiply C.jet_secp_point_write_run
  C.jet_secp_curve_statements C.jet_secp_double_statements C.jet_secp_mixed_affine_product
  C.jet_secp_curve_frame C.jet_secp_field_read_preservation.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words.

Definition mixed_s2_z_call := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
  [curve_local_address _s2;curve_local_address _s2;double_point_address _a _z].
Definition mixed_after_s2_z := match mixed_after_s2 with | Ssequence _ rest => rest | _ => Sskip end.
Definition mixed_s2_frame (bp ba bs bz bx : block) (pos : Z) :=
  bx<>bs /\ bx<>bz /\ (bx<>ba \/ pos<40 \/ 80<=pos) /\ (bx<>bp \/ pos<80 \/ 120<=pos).
Lemma mixed_s2_z_source : mixed_after_s2=Ssequence mixed_s2_z_call mixed_after_s2_z.
Proof. reflexivity. Qed.

Theorem exec_mixed_s2_calls e le m bp ba bs bz y t z :
  le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
  e!_s2=Some (bs,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
  bp<>ba -> bp<>bs -> bp<>bz -> bs<>ba -> bs<>bz -> ba<>bz ->
  square_input_bounds y -> square_input_bounds t -> square_input_bounds z ->
  fe_at m ba 40 (words5 y) -> fe_at m bz 0 (words5 t) -> fe_at m bp 80 (words5 z) ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
  Mem.range_perm m bs 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists m1 mf,
  Clight2.exec_stmt secp_ge e le m (mixed_affine_call true) E0 le m1 Out_normal /\
  Clight2.exec_stmt secp_ge e le m1 mixed_s2_z_call E0 le mf Out_normal /\
  fe_at mf bs 0 (words5 (point_mul_words (point_mul_words y t) z)) /\
  fe_at mf ba 40 (words5 y) /\ fe_at mf bz 0 (words5 t) /\ fe_at mf bp 80 (words5 z) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
  Mem.range_perm mf bs 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  radix_value (point_mul_words (point_mul_words y t) z) mod feP=
    (radix_value y*radix_value t*radix_value z) mod feP /\
  square_input_bounds (point_mul_words (point_mul_words y t) z) /\
  lframe (mixed_s2_frame bp ba bs bz) m mf.
Proof.
  intros HA HB ES EZ EF HPA HPS HPZ HSA HSZ HAZ BY BT BZ Y T Z PF AF SF ZF.
  destruct (exec_mixed_affine_call true y t e le m bs ba bz ES EZ HB EF BY BT HSA HSZ HAZ SF Y AF T ZF)
    as (m1 & C1 & S1 & Y1 & T1 & SF1 & AF1 & ZF1 & V1 & B1 & F1).
  assert (OutP : forall pos, bp<>bs /\ bp<>bz /\ (bp<>ba \/ pos<40 \/ 80<=pos)).
  { intro pos;split;[exact HPS|];split;[exact HPZ|];left;exact HPA. }
  pose proof (field_at_lframe m m1 bp 80 _ _ Z F1 OutP) as Z1.
  pose proof (curve_keep_free _ m m1 bp 128 ltac:(lia) PF F1 OutP) as PF1.
  destruct (eval_field_point_mul_numeric PointZ (point_mul_words y t) z m1 bs bp B1 BZ
    (not_eq_sym HPS) S1 SF1 Z1 PF1)
    as (mf & C2 & S2 & SF2 & Z2 & PF2 & V2 & B2 & Tight & F2).
  assert (OutA : forall pos, ~((ba=bs /\ 0<=pos<40) \/ (ba=bp /\ 80<=pos<120))).
  { intros pos [[HE _]|[HE _]];congruence. }
  assert (OutZ : forall pos, ~((bz=bs /\ 0<=pos<40) \/ (bz=bp /\ 80<=pos<120))).
  { intros pos [[HE _]|[HE _]];congruence. }
  pose proof (field_at_lframe m1 mf ba 40 _ _ Y1 F2 OutA) as Y2.
  pose proof (field_at_lframe m1 mf bz 0 _ _ T1 F2 OutZ) as T2.
  pose proof (curve_keep_free _ m1 mf ba 88 ltac:(lia) AF1 F2 OutA) as AF2.
  pose proof (curve_keep_free _ m1 mf bz 40 ltac:(lia) ZF1 F2 OutZ) as ZF2.
  exists m1,mf;split;[exact C1|];split.
  - unfold mixed_s2_z_call;eapply exec_curve_call with
      (vargs:=[Vptr bs Ptrofs.zero;Vptr bs Ptrofs.zero;Vptr bp (Ptrofs.repr 80)]) (v:=Vundef).
    + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
    + exact EF.
    + eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|].
      eapply eval_Econs;[apply eval_curve_local;exact ES|reflexivity|].
      eapply eval_Econs with (v1:=Vptr bp (Ptrofs.repr 80)).
      * apply eval_double_point_address;[cbn [In];tauto|exact HA].
      * reflexivity.
      * constructor.
    + exact C2.
  - split;[exact S2|];split;[exact Y2|];split;[exact T2|];split;[exact Z2|];
      split;[exact PF2|];split;[exact AF2|];split;[exact SF2|];split;[exact ZF2|];split.
    + rewrite V2,(Z.mul_mod (radix_value (point_mul_words y t)) (radix_value z) feP),V1,
        <-Z.mul_mod by (unfold feP,feR;lia);reflexivity.
    + split;[exact B2|];eapply lframe_trans.
      * eapply lframe_implies;[exact F1|];intros bx pos (NS & NZ & NA & NP) HV.
        split;[exact NS|];split;assumption.
      * eapply lframe_implies;[exact F2|];intros bx pos (NS & NZ & NA & NP) HV [[HE HP]|[HE HP]].
        -- contradiction.
        -- subst bx;change (80<=pos<120) in HP.
           destruct NP as [HN|[HN|HN]];[contradiction|lia|lia].
Qed.
