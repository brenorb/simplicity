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

Definition generator_digit_prefix (high : bool) := Sifthenelse
 (Ebinop Olt (Etempvar _i tint) (Etempvar (if high then _bits_ng_128 else _bits_ng_1) tint) tint)
 (Ssequence
   (Ssequence
     (Ssequence
       (Sset (if high then _t'17 else _t'18)
         (Ederef (Ebinop Oadd (Evar (if high then _wnaf_ng_128 else _wnaf_ng_1) (tarray tint 129))
           (Etempvar _i tint) (tptr tint)) tint))
       (Sset (if high then _t'15 else _t'13) (Ecast (Etempvar (if high then _t'17 else _t'18) tint) tint)))
     (Sset _n (Etempvar (if high then _t'15 else _t'13) tint)))
   (Sset (if high then _t'14 else _t'12) (Ecast (Etempvar (if high then _t'15 else _t'13) tint) tbool)))
 (Sset (if high then _t'14 else _t'12) (Econst_int Int.zero tint)).

Definition generator_digit_dispatch high := Ssequence (generator_digit_prefix high)
 (Sifthenelse (Etempvar (if high then _t'14 else _t'12) tint) (generator_digit_add_statement high) Sskip).

Lemma generator_digit_dispatch_source (high : bool) :
 match nth 10 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip with
 | Ssequence _ (Sloop (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence lo hi)))) _) => if high then hi else lo
 | _=>Sskip end = generator_digit_dispatch high.
Proof. destruct high;reflexivity. Qed.

Definition generator_digit_temps (high : bool) le i bits (digit : Ty.tySem literal_wnaf_digit) :=
 if i <? bits then
 let value:=Vint (Int.repr (wnaf_literal_value digit)) in
 PTree.set (if high then _t'14 else _t'12) (Vint (match digit with inl _=>Int.zero|inr _=>Int.one end))
   (PTree.set _n value (PTree.set (if high then _t'15 else _t'13) value
     (PTree.set (if high then _t'17 else _t'18) value le)))
 else PTree.set (if high then _t'14 else _t'12) (Vint Int.zero) le.

Lemma eval_generator_digit_guard (high : bool) e le m i bits :
 0<=i<129 -> 0<=bits<=129 -> le!_i=Some (Vint (Int.repr i)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr bits)) ->
 eval_expr secp_ge e le m
   (Ebinop Olt (Etempvar _i tint) (Etempvar (if high then _bits_ng_128 else _bits_ng_1) tint) tint)
   (Vint (if i <? bits then Int.one else Int.zero)).
Proof.
 intros Index Length PI PB;eapply eval_Ebinop;
   [apply eval_Etempvar;exact PI|apply eval_Etempvar;exact PB|].
 change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr bits)))=
   Some (Vint (if i <? bits then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by
   (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 destruct (Coqlib.zlt i bits),(Z.ltb_spec i bits);try lia;reflexivity.
Qed.

Lemma generator_digit_temps_other (high : bool) le i bits digit id :
 id<>(if high then _t'14 else _t'12) -> id<>_n ->
 id<>(if high then _t'15 else _t'13) -> id<>(if high then _t'17 else _t'18) ->
 (generator_digit_temps high le i bits digit)!id=le!id.
Proof.
 intros C N V R;unfold generator_digit_temps;destruct (i <? bits);
 repeat rewrite PTree.gso by assumption;reflexivity.
Qed.

Lemma generator_digit_temps_condition (high : bool) le i bits digit :
 (bits<=i -> digit=inl tt) ->
 (generator_digit_temps high le i bits digit)!(if high then _t'14 else _t'12)=
 Some (Vint (match digit with inl _=>Int.zero|inr _=>Int.one end)).
Proof.
 intro Absent;unfold generator_digit_temps;destruct (i <? bits) eqn:Index;rewrite PTree.gss.
 - reflexivity.
 - apply Z.ltb_ge in Index;rewrite (Absent Index);reflexivity.
Qed.

Lemma eval_generator_digit_read (high : bool) e le m i b value :
 0<=i<129 -> le!_i=Some (Vint (Int.repr i)) ->
 e!(if high then _wnaf_ng_128 else _wnaf_ng_1)=Some (b,tarray tint 129) ->
 Mem.load Mint32 m b (4*i)=Some (Vint value) ->
 eval_expr secp_ge e le m
   (Ederef (Ebinop Oadd (Evar (if high then _wnaf_ng_128 else _wnaf_ng_1) (tarray tint 129))
     (Etempvar _i tint) (tptr tint)) tint) (Vint value).
Proof.
 intros Index PI Array Load;eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.repr (4*i)) (bf:=Full).
 - apply eval_Ederef;eapply eval_Ebinop.
   + eapply eval_Elvalue;[apply eval_Evar_local;exact Array|apply deref_loc_reference;reflexivity].
   + apply eval_Etempvar;exact PI.
   + change (Some (Vptr b (Ptrofs.add Ptrofs.zero
       (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr i))))))=
       Some (Vptr b (Ptrofs.repr (4*i)))).
     rewrite Int.signed_repr by
       (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
     rewrite Ptrofs.add_zero_l;unfold Ptrofs.mul;rewrite !Ptrofs.unsigned_repr by
       (change Ptrofs.max_unsigned with 18446744073709551615;lia);reflexivity.
 - eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
   cbn [Mem.loadv];rewrite Ptrofs.unsigned_repr;[exact Load|change Ptrofs.max_unsigned with 18446744073709551615;lia].
Qed.

Theorem exec_generator_digit_prefix (high : bool) e le m i bits b (digit : Ty.tySem literal_wnaf_digit) :
 0<=i<129 -> 0<=bits<=129 -> wnaf_literal_valid digit ->
 le!_i=Some (Vint (Int.repr i)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr bits)) ->
 e!(if high then _wnaf_ng_128 else _wnaf_ng_1)=Some (b,tarray tint 129) ->
 (i<bits -> Mem.load Mint32 m b (4*i)=Some (Vint (Int.repr (wnaf_literal_value digit)))) ->
 Clight2.exec_stmt secp_ge e le m (generator_digit_prefix high) E0
   (generator_digit_temps high le i bits digit) m Out_normal.
Proof.
 intros Index Length Valid PI PB Array Load.
 pose proof (eval_generator_digit_guard high e le m i bits Index Length PI PB) as Guard.
 unfold generator_digit_prefix,generator_digit_temps.
 destruct (i <? bits) eqn:InRange.
 - apply Z.ltb_lt in InRange.
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[exact Guard|reflexivity|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
     (le1:=PTree.set _n (Vint (Int.repr (wnaf_literal_value digit)))
       (PTree.set (if high then _t'15 else _t'13) (Vint (Int.repr (wnaf_literal_value digit)))
         (PTree.set (if high then _t'17 else _t'18) (Vint (Int.repr (wnaf_literal_value digit))) le))).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
       (le1:=PTree.set (if high then _t'15 else _t'13) (Vint (Int.repr (wnaf_literal_value digit)))
         (PTree.set (if high then _t'17 else _t'18) (Vint (Int.repr (wnaf_literal_value digit))) le)).
     * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
         (le1:=PTree.set (if high then _t'17 else _t'18) (Vint (Int.repr (wnaf_literal_value digit))) le).
       -- apply exec_Sset;exact (eval_generator_digit_read high e le m i b _ Index PI Array (Load InRange)).
       -- apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;apply PTree.gss|reflexivity].
     * apply exec_Sset;apply eval_Etempvar;apply PTree.gss.
   + apply exec_Sset;eapply eval_Ecast.
     * apply eval_Etempvar;rewrite PTree.gso by (destruct high;discriminate);apply PTree.gss.
     * change (Some (Vint (if Int.eq (Int.repr (wnaf_literal_value digit)) Int.zero then Int.zero else Int.one))=
         Some (Vint (match digit with inl _=>Int.zero|inr _=>Int.one end))).
       destruct digit as [unit0|word];[destruct unit0;reflexivity|].
       assert (Nonzero : Int.repr (wnaf_literal_value (inr word))<>Int.zero).
       { intro Zero;apply (proj1 (wnaf_literal_int_zero_iff _ Valid)) in Zero;discriminate. }
       cbn [wnaf_literal_value] in Nonzero|-*.
       rewrite (Int.eq_false _ _ Nonzero);reflexivity.
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[exact Guard|reflexivity|].
   apply exec_Sset;constructor.
Qed.

Theorem exec_generator_digit_dispatch (high : bool) digit x y z inv (ax ay az : Ty.tySem (Word 8))
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
 radix_value inv mod feP=1 ->
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
    | inr word=>@literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),@literal_generate_small high Alg.CoreFunSem word) end) /\
 (forall h,generator_table_state h mf) /\ lframe (fun block _=>block<>bp /\ block<>ba /\ block<>bb) m mf.
Proof.
 intros Index Length Valid Sep Tables PR PI PB Array EA EZ EL EAdd ET Load Absent
   BX BY BZ BI One Repr Flag X Y ZAt Inv PF AF IF.
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
   destruct (exec_generator_digit_add high word x y z inv ax ay az e
     (generator_digit_temps high le i bits (inr word)) m bp ba bb
     Odd Range Sep Tables PR' PN EA EZ EL EAdd ET BX BY BZ BI One RX RY RZ Flag X Y ZAt Inv PF AF IF)
     as (mf & ox & oy & oz & Add & Post).
   exists mf,ox,oy,oz;split;[|exact Post].
   unfold generator_digit_dispatch;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
     (le1:=generator_digit_temps high le i bits (inr word));[exact Prefix|].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
     [apply eval_Etempvar;exact Condition|reflexivity|exact Add].
Qed.
