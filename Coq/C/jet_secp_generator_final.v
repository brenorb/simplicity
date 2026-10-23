(** Execute the actual final Z correction of the Strauss helper at inverse
    denominator one. It preserves the literal normalized point, not merely
    its projective equivalence class. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_point_mul_storage C.jet_secp_point_mul_numeric C.jet_secp_point_mul_preservation
 C.jet_secp_point_write_run C.jet_secp_square_columns C.jet_secp_curve_statements C.jet_secp_curve_frame
 C.jet_secp_double_statements C.jet_secp_double_flag C.jet_secp_rescale_statements
 C.jet_secp_rescale_literal C.jet_secp_statement_prefix C.jet_secp_zinv_one_numeric C.jet_secp_zinv_start.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words rescale_field_output.

Definition generator_final_statement := statement_sequence
 (skipn 11 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))))
 (snd (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))).
Definition generator_final_multiply := curve_call _secp256k1_fe_mul f_secp256k1_fe_mul None
 [rescale_coordinate_address PointZ;rescale_coordinate_address PointZ;curve_local_address _Z].
Lemma generator_final_source : generator_final_statement=Ssequence
 (Sset _t'16 (double_point_field _r _infinity tint))
 (Sifthenelse (Eunop Onotbool (Etempvar _t'16 tint) tint) generator_final_multiply Sskip).
Proof. reflexivity. Qed.

Lemma generator_final_multiply_one z inv : square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=1 -> rescale_field_output (point_mul_words z inv)=rescale_field_output z.
Proof.
 intros BZ BI One;destruct (zinv_az_one z inv BZ BI One) as [Value Bound].
 unfold zinv_az_words in Value;apply (toZ_injective (WordToZ 8)).
 rewrite !rescale_field_output_value,field_prime_matches_normalizer;exact Value.
Qed.

Theorem exec_generator_final_one x y z inv e le m bp bb flag :
 le!_r=Some (Vptr bp Ptrofs.zero) -> e!_Z=Some (bb,curve_fe_type) -> e!_secp256k1_fe_mul=None -> bp<>bb ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=1 ->
 Mem.load Mint32 m bp 120=Some (Vint flag) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf oz,
 Clight2.exec_stmt secp_ge e le m generator_final_statement E0 (PTree.set _t'16 (Vint flag) le) mf Out_normal /\
 fe_at mf bp 0 (words5 x) /\ fe_at mf bp 40 (words5 y) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint flag) /\ fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds oz /\ rescale_field_output oz=rescale_field_output z /\
 lframe (fun b _=>b<>bp /\ b<>bb) m mf.
Proof.
 intros PR EZ EM Separate BX BY BZ BI One Flag X Y ZAt Inv PF IF.
 set (lf:=PTree.set _t'16 (Vint flag) le).
 assert (Read : Clight2.exec_stmt secp_ge e le m
   (Sset _t'16 (double_point_field _r _infinity tint)) E0 lf m Out_normal).
 { apply exec_Sset;eapply eval_Elvalue.
   - apply eval_double_flag_field;exact PR.
   - eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
     change (Mem.load Mint32 m bp 120=Some (Vint flag));exact Flag. }
 assert (PRF : lf!_r=Some (Vptr bp Ptrofs.zero)) by (unfold lf;rewrite PTree.gso by discriminate;exact PR).
 assert (Test : eval_expr secp_ge e lf m (Eunop Onotbool (Etempvar _t'16 tint) tint)
   (Vint (if Int.eq flag Int.zero then Int.one else Int.zero))).
 { eapply eval_Eunop;[apply eval_Etempvar;apply PTree.gss|].
   change (Some (Val.of_bool (negb (negb (Int.eq flag Int.zero))))=
     Some (Vint (if Int.eq flag Int.zero then Int.one else Int.zero))).
   rewrite Bool.negb_involutive;destruct (Int.eq flag Int.zero);reflexivity. }
 destruct (Int.eq flag Int.zero) eqn:Zero.
 - destruct (eval_point_mul_numeric PointZ z inv m bp bb BZ BI Separate ZAt PF Inv IF)
     as (mf & Multiply & ZO & PFO & InvO & IFO & Value & BZO & RawFrame).
   assert (XO : fe_at mf bp 0 (words5 x)) by
     (exact (point_mul_other_field PointZ PointX m mf bp bb x ltac:(discriminate) Separate X PFO RawFrame)).
   assert (YO : fe_at mf bp 40 (words5 y)) by
     (exact (point_mul_other_field PointZ PointY m mf bp bb y ltac:(discriminate) Separate Y PFO RawFrame)).
   assert (FlagO : Mem.load Mint32 mf bp 120=Some (Vint flag)).
   { eapply point_mul_flag;[exact Separate| |exact Flag|exact RawFrame].
     eapply Mem.perm_valid_block;apply (PF 0);lia. }
   pose proof (generator_final_multiply_one z inv BZ BI One) as Literal.
   pose proof (point_mul_external_frame PointZ m mf bp bb RawFrame) as Frame.
   exists mf,(point_mul_words z inv);split;[|repeat first [assumption|split]].
   rewrite generator_final_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=m);[exact Read|].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[exact Test|reflexivity|].
   unfold generator_final_multiply;eapply exec_curve_call with
     (vargs:=[Vptr bp (Ptrofs.repr 80);Vptr bp (Ptrofs.repr 80);Vptr bb Ptrofs.zero]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact EM.
   + eapply eval_Econs;[apply eval_rescale_coordinate;exact PRF|reflexivity|].
     eapply eval_Econs;[apply eval_rescale_coordinate;exact PRF|reflexivity|].
     eapply eval_Econs;[apply eval_curve_local;exact EZ|reflexivity|constructor].
   + exact Multiply.
 - exists m,z;split.
   + rewrite generator_final_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=m);[exact Read|].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[exact Test|reflexivity|constructor].
   + assert (Literal : rescale_field_output z=rescale_field_output z) by reflexivity.
     assert (Frame : lframe (fun b _=>b<>bp /\ b<>bb) m m) by apply lframe_refl.
     repeat first [assumption|split].
Qed.
