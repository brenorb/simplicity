(** The actual global-Z factor branch: skip the first iteration, then update
    zs in place from the indexed ratio. No external call behavior is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_statement_prefix C.jet_secp_curve_statements C.jet_secp_globalz_indexed_call
 C.jet_secp_field_slice_product C.jet_secp_field_slice_accumulate C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_multiply_finish_product C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_checkpoint_columns
 C.jet_secp_rescale_literal C.jet_secp_negate_literal_contract
 C.jet_secp_slice_permissions C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_closed_helpers.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output.

Definition globalz_factor_branch := match globalz_indexed_loop_body with
 | Ssequence branch _=>branch | _=>Sskip end.
Definition globalz_ratio_address := Ebinop Oadd (Etempvar _zr (tptr curve_fe_type))
 (Etempvar _i tulong) (tptr curve_fe_type).
Definition globalz_factor_statement := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [curve_local_address _zs;curve_local_address _zs;globalz_ratio_address].
Definition globalz_factor_guard := Ebinop One (Etempvar _i tulong)
 (Ebinop Osub (Etempvar _len tulong) (Econst_int Int.one tint) tulong) tint.
Definition globalz_factor_words i zs ratio :=
 if Z.eqb i 7 then zs else point_mul_words zs ratio.
Definition globalz_factor_frame (bf bz:block) i (bx:block) pos :=
 (bx<>bf \/ pos<0 \/ 40<=pos) /\ (bx<>bz \/ pos<40*i \/ 40*i+40<=pos).

Lemma globalz_factor_source : globalz_factor_branch=
 Sifthenelse globalz_factor_guard globalz_factor_statement Sskip.
Proof. reflexivity. Qed.

Lemma eval_globalz_ratio e le m bz i : 0<=i<8 ->
 le!_zr=Some (Vptr bz Ptrofs.zero) -> le!_i=Some (Vlong (Int64.repr i)) ->
 eval_expr secp_ge e le m globalz_ratio_address (Vptr bz (Ptrofs.repr (40*i))).
Proof.
 intros Index Ratios IndexTemp;unfold globalz_ratio_address.
 eapply eval_Ebinop with (v1:=Vptr bz Ptrofs.zero) (v2:=Vlong (Int64.repr i)).
 - apply eval_Etempvar;exact Ratios.
 - apply eval_Etempvar;exact IndexTemp.
 - change (Some (Vptr bz (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 40)
     (Ptrofs.repr (Int64.unsigned (Int64.repr i))))))=Some (Vptr bz (Ptrofs.repr (40*i)))).
   rewrite Int64.unsigned_repr by (change (0<=i<=18446744073709551615);lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Lemma eval_globalz_factor_guard e le m i : 0<=i<8 ->
 le!_i=Some (Vlong (Int64.repr i)) -> le!_len=Some (Vlong (Int64.repr 8)) ->
 eval_expr secp_ge e le m globalz_factor_guard
 (Vint (if Z.eqb i 7 then Int.zero else Int.one)).
Proof.
 intros Index IndexTemp Length;unfold globalz_factor_guard.
 eapply eval_Ebinop with (v1:=Vlong (Int64.repr i)) (v2:=Vlong (Int64.repr 7)).
 - apply eval_Etempvar;exact IndexTemp.
 - eapply eval_Ebinop;[apply eval_Etempvar;exact Length|constructor|reflexivity].
 - change (Some (Val.of_bool (negb (Int64.eq (Int64.repr i) (Int64.repr 7))))=
     Some (Vint (if Z.eqb i 7 then Int.zero else Int.one))).
   unfold Int64.eq;rewrite !Int64.unsigned_repr by
     (change Int64.max_unsigned with 18446744073709551615;lia).
   destruct (Coqlib.zeq i 7), (Z.eqb_spec i 7);first [congruence|reflexivity].
Qed.

Theorem exec_globalz_factor_call e le zs ratio m bf bz i :
 1<=i<8 -> bf<>bz -> e!_zs=Some (bf,curve_fe_type) -> e!_secp256k1_fe_mul=None ->
 le!_zr=Some (Vptr bz Ptrofs.zero) -> le!_i=Some (Vlong (Int64.repr i)) ->
 le!_len=Some (Vlong (Int64.repr 8)) ->
 square_input_bounds zs -> square_input_bounds ratio ->
 fe_at m bf 0 (words5 zs) -> fe_at m bz (40*i) (words5 ratio) ->
 Mem.range_perm m bf 0 40 Cur Freeable -> Mem.range_perm m bz 0 320 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m globalz_factor_branch E0 le mf Out_normal /\
 fe_at mf bf 0 (words5 (globalz_factor_words i zs ratio)) /\
 fe_at mf bz (40*i) (words5 ratio) /\ square_input_bounds (globalz_factor_words i zs ratio) /\
 rescale_field_output (globalz_factor_words i zs ratio)=
  (if Z.eqb i 7 then rescale_field_output zs else
    @literal_fe_multiply Alg.CoreFunSem (rescale_field_output zs,rescale_field_output ratio)) /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 320 Cur Freeable /\
 keeps_permissions m mf /\ lframe (globalz_factor_frame bf bz i) m mf /\ readonly_preserved m mf.
Proof.
 intros Index Separate Factor Global Ratios IndexTemp Length BZ BR Z R FreeZ FreeR.
 pose proof (eval_globalz_factor_guard e le m i ltac:(lia) IndexTemp Length) as Guard.
 destruct (Z.eqb i 7) eqn:First.
 - exists m;split.
   + rewrite globalz_factor_source;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
      [exact Guard|reflexivity|constructor].
   + unfold globalz_factor_words;rewrite First;split;[exact Z|];split;[exact R|];split;[exact BZ|];
      split;[reflexivity|];split;[exact FreeZ|];split;[exact FreeR|];split.
     * intros b pos k p Perm;exact Perm.
     * split;[apply lframe_refl|apply preserved_refl].
 - destruct (eval_field_slice_accumulate zs ratio m bf 0 bz (40*i) BZ BR
     ltac:(left;exact Separate) Z R) as (mf & Call & Out & RP & Numeric & Bound & Keep & Frame).
   assert (Literal:rescale_field_output (point_mul_words zs ratio)=
     @literal_fe_multiply Alg.CoreFunSem (rescale_field_output zs,rescale_field_output ratio)).
   { apply rescale_mul_writer;[exact BZ|exact BR| |];
      rewrite rescale_field_output_value,Z.mod_mod by (unfold field_prime,field_c;discriminate);reflexivity. }
   exists mf;split.
   + rewrite globalz_factor_source;eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
      [exact Guard|reflexivity|].
     unfold globalz_factor_statement;eapply exec_curve_call with
      (vargs:=[Vptr bf Ptrofs.zero;Vptr bf Ptrofs.zero;Vptr bz (Ptrofs.repr (40*i))]) (v:=Vundef).
     * unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
     * exact Global.
     * eapply eval_Econs;[apply eval_curve_local;exact Factor|reflexivity|].
       eapply eval_Econs;[apply eval_curve_local;exact Factor|reflexivity|].
       eapply eval_Econs;[apply eval_globalz_ratio with (bz:=bz) (i:=i);assumption || lia|reflexivity|constructor].
     * exact Call.
   + unfold globalz_factor_words;rewrite First;split;[exact Out|];split;[exact RP|];split;[exact Bound|];
      split;[exact Literal|];split.
     * eapply keeps_range_permissions;[exact Keep|exact FreeZ].
     * split.
       { eapply keeps_range_permissions;[exact Keep|exact FreeR]. }
       split;[exact Keep|];split;[exact Frame|].
       eapply (secp_closed_function_preserved f_secp256k1_fe_mul);[reflexivity|reflexivity|exact Call].
Qed.
