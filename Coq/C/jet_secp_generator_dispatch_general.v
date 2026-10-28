(** Original generator digit guard: short-circuiting, typed array read and
    assignment side effects for either of the two generator tables. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
 C.jet_secp_generator_digit_add C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array
 C.jet_secp_wnaf_literal_values C.jet_readBit_layout C.jet_sx_mem C.jet_secp_fe_nv
 C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
 C.jet_secp_square_columns C.jet_secp_square_execution C.jet_secp_curve_statements
 C.jet_secp_generator_globals C.jet_secp_rescale_literal C.jet_secp_canonical_zero
 C.jet_secp_generate_literal C.jet_secp_add_literal.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Require Import C.jet_secp_generator_digit_control C.jet_secp_generator_digit_general.

Theorem exec_generator_digit_dispatch_scaled (high : bool) digit x y z inv (ax ay az s : Ty.tySem (Word 8))
 e le m i bits b bp ba bb :
 0<=i<129 -> 0<=bits<=129 -> wnaf_literal_valid digit ->
 NoDup [bp;ba;bb] -> (forall h,generator_table_state h m) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr bits)) ->
 e!(if high then _wnaf_ng_128 else _wnaf_ng_1)=Some (b,tarray tint 129) ->
 e!_tmpa=Some (ba,curve_ge_type) -> e!_Z=Some (bb,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!(generator_table_id high)=None ->
 (i<bits -> Mem.load Mint32 m b (4*i)=Some (Vint (Int.repr (wnaf_literal_value digit)))) ->
 (bits<=i -> digit=inl tt) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=@toZ (WordToZ 8) s mod feP ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m (generator_digit_dispatch high) E0
   (generator_digit_temps high le i bits digit) mf Out_normal /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   (match digit with inl _=>((ax,ay),az)
    | inr word=>@literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),@literal_gej_zinv Alg.CoreFunSem (@literal_generate_small high Alg.CoreFunSem word,s)) end) /\
 (forall h,generator_table_state h mf) /\ lframe (fun block _=>block<>bp /\ block<>ba /\ block<>bb) m mf.
Proof.
 intros Index Length Valid Sep Tables PR PI PB Array EA EZ EL EAdd ET Load Absent
   BX BY BZ BI Scale Repr Flag X Y ZAt Inv PF AF IF.
 pose proof (exec_generator_digit_prefix high e le m i bits b digit Index Length Valid PI PB Array Load) as Prefix.
 pose proof (generator_digit_temps_condition high le i bits digit Absent) as Condition.
 destruct digit as [unit0|word].
 - destruct unit0;exists m,x,y,z;split.
   + unfold generator_digit_dispatch;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
       (le1:=generator_digit_temps high le i bits (inl tt));[exact Prefix|].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
       [apply eval_Etempvar;exact Condition|reflexivity|constructor].
   + assert (FlagO : Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool
       (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z)))))).
     { assert (AZ : rescale_field_output z=az) by congruence;rewrite AZ;exact Flag. }
     assert (Frame : lframe (fun block _=>block<>bp /\ block<>ba /\ block<>bb) m m) by apply lframe_refl.
     repeat first [assumption|split].
 - assert (InRange : i<bits).
   { destruct (Z_lt_dec i bits);[assumption|pose proof (Absent ltac:(lia));discriminate]. }
   assert (PN : (generator_digit_temps high le i bits (inr word))!_n=
     Some (Vint (Int.repr (jet_secp_wnaf_literal_mask.literal_wnaf_signed16 word)))).
   { unfold generator_digit_temps;rewrite (proj2 (Z.ltb_lt i bits) InRange).
     rewrite PTree.gso by (destruct high;discriminate);apply PTree.gss. }
   assert (PR' : (generator_digit_temps high le i bits (inr word))!_r=Some (Vptr bp Ptrofs.zero)).
   { rewrite generator_digit_temps_other by (destruct high;discriminate);exact PR. }
   assert (RX : radix_value x mod feP=@toZ (WordToZ 8) ax mod feP).
   { assert (AX : rescale_field_output x=ax) by congruence;rewrite <-AX,rescale_field_output_value,
       field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
   assert (RY : radix_value y mod feP=@toZ (WordToZ 8) ay mod feP).
   { assert (AY : rescale_field_output y=ay) by congruence;rewrite <-AY,rescale_field_output_value,
       field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
   assert (RZ : radix_value z mod feP=@toZ (WordToZ 8) az mod feP).
   { assert (AZ : rescale_field_output z=az) by congruence;rewrite <-AZ,rescale_field_output_value,
       field_prime_matches_normalizer,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
   destruct Valid as [Odd Range].
   destruct (exec_generator_digit_add_scaled high word x y z inv ax ay az s e
     (generator_digit_temps high le i bits (inr word)) m bp ba bb
     Odd Range Sep Tables PR' PN EA EZ EL EAdd ET BX BY BZ BI Scale RX RY RZ Flag X Y ZAt Inv PF AF IF)
     as (mf & ox & oy & oz & Add & Post).
   exists mf,ox,oy,oz;split;[|exact Post].
   unfold generator_digit_dispatch;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
     (le1:=generator_digit_temps high le i bits (inr word));[exact Prefix|].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
     [apply eval_Etempvar;exact Condition|reflexivity|exact Add].
Qed.
