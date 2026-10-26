(** Actual indexed coordinate-scaling call in the original nonempty global-Z
    loop. The caller initializes tmpa.x/y/infinity only; no tmpa.z value is
    required here. The factor zs is arbitrary, including zero. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_generator_globalz_empty C.jet_secp_statement_prefix C.jet_secp_curve_statements
 C.jet_secp_ge_zinv_arithmetic C.jet_secp_ge_zinv_indexed_function C.jet_secp_ge_zinv_indexed_literal
 C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_rescale_literal
 C.jet_secp_multiply_checkpoint_columns C.jet_secp_slice_permissions C.jet_clight_internal_permissions
 C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.
Local Opaque secp_ge rescale_field_output.

Definition globalz_indexed_loop_body := match snd (split_statement_last globalz_nonempty_branch) with
 | Sloop (Ssequence _ body) _ => body | _ => Sskip end.
Definition globalz_indexed_scale_statement := snd (split_statement_last globalz_indexed_loop_body).
Definition globalz_indexed_entry_address := Ebinop Oadd (Etempvar _a (tptr curve_ge_type))
 (Etempvar _i tulong) (tptr curve_ge_type).
Definition globalz_indexed_point_address := Eaddrof (Evar _tmpa (Tstruct __6123 noattr))
 (tptr (Tstruct __6123 noattr)).

Lemma globalz_indexed_scale_source : globalz_indexed_scale_statement=
 curve_call _secp256k1_ge_set_gej_zinv f_secp256k1_ge_set_gej_zinv None
 [globalz_indexed_entry_address;globalz_indexed_point_address;curve_local_address _zs].
Proof. reflexivity. Qed.

Lemma eval_globalz_indexed_entry e le m br i : 0<=i<8 ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_i=Some (Vlong (Int64.repr i)) ->
 eval_expr secp_ge e le m globalz_indexed_entry_address (Vptr br (Ptrofs.repr (88*i))).
Proof.
 intros Index A IndexTemp;unfold globalz_indexed_entry_address.
 eapply eval_Ebinop with (v1:=Vptr br Ptrofs.zero) (v2:=Vlong (Int64.repr i)).
 - apply eval_Etempvar;exact A.
 - apply eval_Etempvar;exact IndexTemp.
 - change (Some (Vptr br (Ptrofs.add Ptrofs.zero (Ptrofs.mul (Ptrofs.repr 88)
     (Ptrofs.repr (Int64.unsigned (Int64.repr i))))))=Some (Vptr br (Ptrofs.repr (88*i)))).
   rewrite Int64.unsigned_repr by (change (0<=i<=18446744073709551615);lia).
   rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul.
   rewrite !Ptrofs.unsigned_repr by (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
Qed.

Theorem exec_globalz_indexed_scale e le x y zi m br ba bf i :
 0<=i<8 -> br<>ba -> br<>bf -> ba<>bf ->
 e!_tmpa=Some (ba,Tstruct __6123 noattr) -> e!_zs=Some (bf,curve_fe_type) ->
 e!_secp256k1_ge_set_gej_zinv=None ->
 le!_a=Some (Vptr br Ptrofs.zero) -> le!_i=Some (Vlong (Int64.repr i)) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds zi ->
 Mem.load Mint32 m ba 120=Some (Vint Int.zero) ->
 fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m bf 0 (words5 zi) ->
 Mem.range_perm m br 0 704 Cur Freeable -> Mem.range_perm m ba 0 128 Cur Freeable ->
 Mem.range_perm m bf 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m globalz_indexed_scale_statement E0 le mf Out_normal /\
 fe_at mf br (88*i+0) (words5 (ge_zinv_x_words x zi)) /\
 fe_at mf br (88*i+40) (words5 (ge_zinv_y_words y zi)) /\
 Mem.load Mint32 mf br (88*i+80)=Some (Vint Int.zero) /\
 (rescale_field_output (ge_zinv_x_words x zi),rescale_field_output (ge_zinv_y_words y zi))=
  @literal_gej_zinv Alg.CoreFunSem
   ((rescale_field_output x,rescale_field_output y),rescale_field_output zi) /\
 Mem.load Mint32 mf ba 120=Some (Vint Int.zero) /\
 fe_at mf ba 0 (words5 x) /\ fe_at mf ba 40 (words5 y) /\ fe_at mf bf 0 (words5 zi) /\
 Mem.range_perm mf br 0 704 Cur Freeable /\ Mem.range_perm mf ba 0 128 Cur Freeable /\
 Mem.range_perm mf bf 0 40 Cur Freeable /\
 square_input_bounds (ge_zinv_x_words x zi) /\ square_input_bounds (ge_zinv_y_words y zi) /\
 keeps_permissions m mf /\ lframe (ge_zinv_indexed_frame br (88*i) ba bf) m mf /\ readonly_preserved m mf.
Proof.
 intros Index RA RF AF Tmp Factor Global A IndexTemp BX BY BZI Flag X Y Z FreeR FreeA FreeF.
 assert (Residue:forall w, C.jet_secp_multiply_finish_product.radix_value w mod field_prime=
   @toZ (WordToZ 8) (rescale_field_output w) mod field_prime).
 { intro w;rewrite rescale_field_output_value,Z.mod_mod by (unfold field_prime,field_c;discriminate);reflexivity. }
 destruct (eval_ge_set_gej_zinv_indexed_literal false (88*i) 704 x y zi
   (rescale_field_output x) (rescale_field_output y) (rescale_field_output zi) m br ba bf Int.zero
   ltac:(lia) ltac:(exists (11*i);ring) ltac:(lia)
   ltac:(change (704<=18446744073709551615);lia) RA RF AF BX BY BZI
   (Residue x) (Residue y) (Residue zi) Flag X Y Z FreeR FreeA FreeF)
  as (mf & Call & RX & RY & Literal & RFlag & AFlag & AX & AY & ZF & RFF & AFF & FFF & BXO & BYO & Frame & Readonly).
 exists mf;split.
 - rewrite globalz_indexed_scale_source;eapply exec_curve_call with
    (vargs:=[Vptr br (Ptrofs.repr (88*i));Vptr ba Ptrofs.zero;Vptr bf Ptrofs.zero]) (v:=Vundef).
   + unfold C.jet_secp_fns.secp_pure;repeat (first [left;reflexivity|right]).
   + exact Global.
   + eapply eval_Econs;[apply eval_globalz_indexed_entry with (br:=br) (i:=i);assumption|reflexivity|].
     eapply eval_Econs;[unfold globalz_indexed_point_address;apply eval_Eaddrof;apply eval_Evar_local;exact Tmp|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact Factor|reflexivity|constructor].
   + exact Call.
 - split;[exact RX|];split;[exact RY|];split;[exact RFlag|];split;[exact Literal|];
   split;[exact AFlag|];split;[exact AX|];split;[exact AY|];split;[exact ZF|];split;[exact RFF|];
   split;[exact AFF|];split;[exact FFF|];split;[exact BXO|];split;[exact BYO|];split.
   + eapply (secp_internal_keeps_permissions f_secp256k1_ge_set_gej_zinv);
      [reflexivity|reflexivity|exact Call].
   + split;assumption.
Qed.
