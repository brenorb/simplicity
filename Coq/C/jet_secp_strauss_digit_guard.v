(** Original short-circuit window-5 guard, including both PS reloads, the
    stored count, the positioned array read and the n/bool assignments.
    The complete dispatch derives the lookup/addition execution as well. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_generator_loop_control
 C.jet_secp_strauss_wnaf_calls C.jet_secp_strauss_digit_add
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_literal_next C.jet_secp_wnaf5_signed_array
 C.jet_secp_lookup5_literal.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge C.jet_secp_square_columns
 C.jet_secp_field_mul_small C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero C.jet_secp_add_literal
 C.jet_secp_strauss_program C.jet_secp_double_literal
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition strauss_digit_point_from_temp tmp := Ederef
 (Ebinop Oadd (Etempvar tmp (tptr strauss_point_type)) (Etempvar _np tulong) (tptr strauss_point_type)) strauss_point_type.
Definition strauss_digit_count_expr (high:bool) tmp := Efield
 (strauss_digit_point_from_temp tmp) (if high then _bits_na_lam else _bits_na_1) tint.
Definition strauss_digit_read_expr (high:bool) tmp := Ederef
 (Ebinop Oadd (Efield (strauss_digit_point_from_temp tmp)
  (if high then _wnaf_na_lam else _wnaf_na_1) (tarray tint 129)) (Etempvar _i tint) (tptr tint)) tint.
Definition strauss_digit_prefix (high:bool) :=
 let ptr:=if high then _t'21 else _t'26 in
 let count:=if high then _t'22 else _t'27 in
 let reload:=if high then _t'23 else _t'28 in
 let read:=if high then _t'24 else _t'29 in
 let value:=if high then _t'11 else _t'9 in
 let cond:=if high then _t'10 else _t'8 in
 Ssequence (Sset ptr strauss_ps_pointer)
 (Ssequence (Sset count (strauss_digit_count_expr high ptr))
  (Sifthenelse (Ebinop Olt (Etempvar _i tint) (Etempvar count tint) tint)
   (Ssequence
    (Ssequence
     (Ssequence (Sset reload strauss_ps_pointer)
      (Ssequence (Sset read (strauss_digit_read_expr high reload))
       (Sset value (Ecast (Etempvar read tint) tint))))
     (Sset _n (Etempvar value tint)))
    (Sset cond (Ecast (Etempvar value tint) tbool)))
   (Sset cond (Econst_int Int.zero tint)))).
Definition strauss_digit_dispatch (high:bool) := Ssequence (strauss_digit_prefix high)
 (Sifthenelse (Etempvar (if high then _t'10 else _t'8) tint) (strauss_digit_add_statement high) Sskip).
Lemma strauss_digit_dispatch_source (high:bool) :
 match generator_nongenerator_statement with
 | Ssequence _ (Sloop (Ssequence _ (Ssequence lo hi)) _) => if high then hi else lo
 | _=>Sskip end=strauss_digit_dispatch high.
Proof. destruct high;reflexivity. Qed.

Definition strauss_digit_loaded (high:bool) le bp bits :=
 PTree.set (if high then _t'22 else _t'27) (Vint (Int.repr bits))
  (PTree.set (if high then _t'21 else _t'26) (Vptr bp Ptrofs.zero) le).
Definition strauss_digit_prefix_temps (high:bool) le bp i bits (digit:Ty.tySem literal_wnaf5_digit) :=
 let lc:=strauss_digit_loaded high le bp bits in
 if i <? bits then
 let value:=Vint (Int.repr (wnaf5_literal_value digit)) in
 PTree.set (if high then _t'10 else _t'8) (Vint (match digit with inl _=>Int.zero|inr _=>Int.one end))
 (PTree.set _n value (PTree.set (if high then _t'11 else _t'9) value
 (PTree.set (if high then _t'24 else _t'29) value
 (PTree.set (if high then _t'23 else _t'28) (Vptr bp Ptrofs.zero) lc))))
 else PTree.set (if high then _t'10 else _t'8) (Vint Int.zero) lc.

Lemma strauss_digit_loaded_other (high:bool) le bp bits id :
 id<>(if high then _t'22 else _t'27) -> id<>(if high then _t'21 else _t'26) ->
 (strauss_digit_loaded high le bp bits)!id=le!id.
Proof. intros C P;unfold strauss_digit_loaded;rewrite !PTree.gso by assumption;reflexivity. Qed.
Lemma strauss_digit_prefix_other (high:bool) le bp i bits digit id :
 ~In id [_n;(if high then _t'21 else _t'26);(if high then _t'22 else _t'27);
 (if high then _t'23 else _t'28);(if high then _t'24 else _t'29);
 (if high then _t'11 else _t'9);(if high then _t'10 else _t'8)] ->
 (strauss_digit_prefix_temps high le bp i bits digit)!id=le!id.
Proof.
 intro Outside;unfold strauss_digit_prefix_temps,strauss_digit_loaded;destruct (i <? bits);
 rewrite !PTree.gso by (intro Eq;apply Outside;subst id;cbn [In];tauto);reflexivity.
Qed.

Definition strauss_digit_dispatch_temps (high:bool) le bp bt bx i bits (digit:Ty.tySem literal_wnaf5_digit) :=
 let lp:=strauss_digit_prefix_temps high le bp i bits digit in
 match digit with inl _=>lp | inr _=>strauss_digit_lookup_temps high lp bt bx end.
Definition strauss_digit_action (high:bool) (digit:Ty.tySem literal_wnaf5_digit) xs ys
 (point:Ty.tySem literal_table_gej) :=
 match digit with inl _=>point | inr nib=>@literal_gej_ge_add Alg.CoreFunSem (point,strauss_digit_point high nib xs ys) end.

Lemma strauss_digit_dispatch_other (high:bool) le bp bt bx i bits digit id :
 ~In id [_n;_t'8;_t'9;_t'10;_t'11;_t'19;_t'20;_t'21;_t'22;_t'23;_t'24;_t'25;_t'26;_t'27;_t'28;_t'29] ->
 (strauss_digit_dispatch_temps high le bp bt bx i bits digit)!id=le!id.
Proof.
 intro Outside;unfold strauss_digit_dispatch_temps;destruct digit as [u|nib].
 - apply strauss_digit_prefix_other;destruct high;cbn [In] in Outside|-*;tauto.
 - rewrite strauss_digit_lookup_other by (cbn [In] in Outside|-*;tauto).
   apply strauss_digit_prefix_other;destruct high;cbn [In] in Outside|-*;tauto.
Qed.

Lemma strauss_digit_actions_literal (point:Ty.tySem literal_table_gej) (z:Ty.tySem (Word 8))
 xs ys (d1 dlam:Ty.tySem literal_wnaf5_digit) :
 strauss_digit_action true dlam xs ys
  (strauss_digit_action false d1 xs ys (@literal_gej_double Alg.CoreFunSem point))=
 @literal_strauss_step Alg.CoreFunSem
  (point,((z,globalz_word_vector (globalz_decoded_points xs ys)),((d1,dlam),(inl tt,inl tt)))).
Proof. rewrite literal_strauss_step_value;destruct d1,dlam;reflexivity. Qed.

Lemma strauss_digit_prefix_condition (high:bool) le bp i bits digit :
 (bits<=i -> digit=inl tt) ->
 (strauss_digit_prefix_temps high le bp i bits digit)!(if high then _t'10 else _t'8)=
 Some (Vint (match digit with inl _=>Int.zero|inr _=>Int.one end)).
Proof.
 intro Absent;unfold strauss_digit_prefix_temps;destruct (i <? bits) eqn:InRange;rewrite PTree.gss;
 [reflexivity|apply Z.ltb_ge in InRange;rewrite (Absent InRange);reflexivity].
Qed.

Lemma strauss_wnaf5_int_nonzero (nib:Ty.tySem (Word 2)) : Int.repr (lookup5_digit nib)<>Int.zero.
Proof.
 destruct nib as [[b3 b2] [b1 b0]];
 destruct b3 as [u3|u3];destruct u3;destruct b2 as [u2|u2];destruct u2;
 destruct b1 as [u1|u1];destruct u1;destruct b0 as [u0|u0];destruct u0;
 vm_compute;discriminate.
Qed.

Lemma eval_strauss_digit_point_field e le m bp tmp field delta ty :
 In (field,delta) [(_wnaf_na_1,0);(_wnaf_na_lam,516);(_bits_na_1,1032);(_bits_na_lam,1036)] ->
 le!tmp=Some (Vptr bp Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 eval_lvalue secp_ge e le m (Efield (strauss_digit_point_from_temp tmp) field ty) bp (Ptrofs.repr delta) Full.
Proof.
 intros Field Pointer NP;destruct (strauss_point_layout field delta Field) as (co & Lookup & Offset).
 unfold strauss_digit_point_from_temp;rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
 eapply eval_Efield_struct with (co:=co) (delta:=delta).
 - eapply eval_Elvalue;[apply eval_Ederef|apply deref_loc_copy;reflexivity].
   eapply eval_Ebinop with (v1:=Vptr bp Ptrofs.zero) (v2:=Vlong Int64.zero).
   + apply eval_Etempvar;exact Pointer.
   + apply eval_Etempvar;exact NP.
   + unfold sem_binary_operation,sem_add,sem_add_ptr_long.
     change (Some (Vptr bp (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv secp_ge) strauss_point_type))
       (Ptrofs.of_int64 Int64.zero))))=Some (Vptr bp Ptrofs.zero)).
     rewrite strauss_point_size;reflexivity.
 - reflexivity.
 - exact Lookup.
 - exact Offset.
Qed.

Lemma eval_strauss_digit_count (high:bool) e le m bp tmp bits :
 le!tmp=Some (Vptr bp Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 Mem.load Mint32 m bp (strauss_wnaf_count_offset high)=Some (Vint (Int.repr bits)) ->
 eval_expr secp_ge e le m (strauss_digit_count_expr high tmp) (Vint (Int.repr bits)).
Proof.
 intros Pointer NP Count;unfold strauss_digit_count_expr.
 eapply eval_Elvalue with (loc:=bp) (ofs:=Ptrofs.repr (strauss_wnaf_count_offset high)) (bf:=Full).
 - eapply eval_strauss_digit_point_field;[destruct high;cbn [strauss_wnaf_count_offset In];tauto|exact Pointer|exact NP].
 - eapply deref_loc_value with (chunk:=Mint32);[reflexivity|];destruct high;exact Count.
Qed.

Lemma eval_strauss_digit_read (high:bool) e le m bp tmp i value :
 0<=i<129 -> le!tmp=Some (Vptr bp Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_i=Some (Vint (Int.repr i)) ->
 Mem.load Mint32 m bp (strauss_wnaf_base high+4*i)=Some (Vint value) ->
 eval_expr secp_ge e le m (strauss_digit_read_expr high tmp) (Vint value).
Proof.
 intros Index Pointer NP I Load;unfold strauss_digit_read_expr.
 eapply eval_Elvalue with (loc:=bp) (ofs:=Ptrofs.repr (strauss_wnaf_base high+4*i)) (bf:=Full).
 - apply eval_Ederef;eapply eval_Ebinop with
    (v1:=Vptr bp (Ptrofs.repr (strauss_wnaf_base high))) (v2:=Vint (Int.repr i)).
   + eapply eval_Elvalue with (loc:=bp) (ofs:=Ptrofs.repr (strauss_wnaf_base high)) (bf:=Full).
     * eapply eval_strauss_digit_point_field with (delta:=strauss_wnaf_base high);
        [destruct high;cbn [strauss_wnaf_base In];tauto|exact Pointer|exact NP].
     * apply deref_loc_reference;reflexivity.
   + apply eval_Etempvar;exact I.
   + change (Some (Vptr bp (Ptrofs.add (Ptrofs.repr (strauss_wnaf_base high))
      (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr i))))))=
       Some (Vptr bp (Ptrofs.repr (strauss_wnaf_base high+4*i)))).
     rewrite Int.signed_repr by
      (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
     unfold Ptrofs.mul;rewrite !Ptrofs.unsigned_repr by
      (change Ptrofs.max_unsigned with 18446744073709551615;lia).
     rewrite Ptrofs.add_unsigned,!Ptrofs.unsigned_repr by
      (destruct high;cbn [strauss_wnaf_base];change Ptrofs.max_unsigned with 18446744073709551615;lia).
     reflexivity.
 - eapply deref_loc_value with (chunk:=Mint32);[reflexivity|].
   cbn [Mem.loadv];rewrite Ptrofs.unsigned_repr;
    [exact Load|destruct high;cbn [strauss_wnaf_base];change Ptrofs.max_unsigned with 18446744073709551615;lia].
Qed.

Theorem exec_strauss_digit_prefix (high:bool) e le m bs bp i bits (digit:Ty.tySem literal_wnaf5_digit) :
 0<=i<129 -> 0<=bits<=129 -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mint32 m bp (strauss_wnaf_count_offset high)=Some (Vint (Int.repr bits)) ->
 (i<bits -> Mem.load Mint32 m bp (strauss_wnaf_base high+4*i)=Some (Vint (Int.repr (wnaf5_literal_value digit)))) ->
 Clight2.exec_stmt secp_ge e le m (strauss_digit_prefix high) E0
  (strauss_digit_prefix_temps high le bp i bits digit) m Out_normal.
Proof.
 intros Index Length State NP I PS Count Load.
 pose (lp:=PTree.set (if high then _t'21 else _t'26) (Vptr bp Ptrofs.zero) le).
 pose (lc:=strauss_digit_loaded high le bp bits).
 assert (NPlp:lp!_np=Some (Vlong Int64.zero)) by (unfold lp;rewrite PTree.gso by (destruct high;discriminate);exact NP).
 assert (NPlc:lc!_np=Some (Vlong Int64.zero)) by (unfold lc;rewrite strauss_digit_loaded_other by (destruct high;discriminate);exact NP).
 assert (Ilc:lc!_i=Some (Vint (Int.repr i))) by (unfold lc;rewrite strauss_digit_loaded_other by (destruct high;discriminate);exact I).
 assert (StateLc:lc!_state=Some (Vptr bs Ptrofs.zero)) by (unfold lc;rewrite strauss_digit_loaded_other by (destruct high;discriminate);exact State).
 assert (Guard:eval_expr secp_ge e lc m
  (Ebinop Olt (Etempvar _i tint) (Etempvar (if high then _t'22 else _t'27) tint) tint)
  (Vint (if i <? bits then Int.one else Int.zero))).
 { eapply eval_Ebinop;[apply eval_Etempvar;exact Ilc|apply eval_Etempvar;unfold lc,strauss_digit_loaded;apply PTree.gss|].
   change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr bits)))=Some (Vint (if i <? bits then Int.one else Int.zero))).
   unfold Int.lt;rewrite !Int.signed_repr by
    (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
   destruct (Coqlib.zlt i bits),(Z.ltb_spec i bits);try lia;reflexivity. }
 unfold strauss_digit_prefix,strauss_digit_prefix_temps.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lp) (m1:=m).
 - apply exec_Sset;apply (eval_strauss_ps_pointer e le m bs bp State PS).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lc) (m1:=m).
   + apply exec_Sset;apply (eval_strauss_digit_count high e lp m bp _ bits);
      [unfold lp;apply PTree.gss|exact NPlp|exact Count].
   + destruct (i <? bits) eqn:InRange.
     * apply Z.ltb_lt in InRange.
       eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[exact Guard|reflexivity|].
       pose (lr:=PTree.set (if high then _t'23 else _t'28) (Vptr bp Ptrofs.zero) lc).
       pose (ld:=PTree.set (if high then _t'24 else _t'29) (Vint (Int.repr (wnaf5_literal_value digit))) lr).
       pose (lv:=PTree.set (if high then _t'11 else _t'9) (Vint (Int.repr (wnaf5_literal_value digit))) ld).
       pose (ln:=PTree.set _n (Vint (Int.repr (wnaf5_literal_value digit))) lv).
       eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ln) (m1:=m).
       -- eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lv) (m1:=m).
          ++ eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lr) (m1:=m).
             ** apply exec_Sset;apply (eval_strauss_ps_pointer e lc m bs bp StateLc PS).
             ** eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ld) (m1:=m).
                --- apply exec_Sset;apply (eval_strauss_digit_read high e lr m bp _ i _ Index);
                     [unfold lr;apply PTree.gss|
                      unfold lr;rewrite PTree.gso by (destruct high;discriminate);exact NPlc|
                      unfold lr;rewrite PTree.gso by (destruct high;discriminate);exact Ilc|apply Load;exact InRange].
                --- apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;unfold ld;apply PTree.gss|reflexivity].
          ++ apply exec_Sset;apply eval_Etempvar;unfold lv;apply PTree.gss.
       -- apply exec_Sset;eapply eval_Ecast.
          ++ apply eval_Etempvar;unfold ln;rewrite PTree.gso by (destruct high;discriminate);unfold lv;apply PTree.gss.
          ++ change (Some (Vint (if Int.eq (Int.repr (wnaf5_literal_value digit)) Int.zero then Int.zero else Int.one))=
              Some (Vint (match digit with inl _=>Int.zero|inr _=>Int.one end))).
             destruct digit as [u|nib];[destruct u;reflexivity|].
             change (Some (Vint (if Int.eq (Int.repr (lookup5_digit nib)) Int.zero then Int.zero else Int.one))=Some (Vint Int.one)).
             rewrite (Int.eq_false _ _ (strauss_wnaf5_int_nonzero nib));reflexivity.
     * eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[exact Guard|reflexivity|].
       apply exec_Sset;constructor.
Qed.

Theorem exec_strauss_digit_dispatch (high:bool) (digit:Ty.tySem literal_wnaf5_digit) xs ys aux x y z
 (ax ay az:Ty.tySem (Word 8)) e le m br bs bp bd bt bx i bits :
 0<=i<129 -> 0<=bits<=129 -> NoDup [br;bd;bt;bx] ->
 e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!(if high then _secp256k1_ecmult_table_get_ge_lambda else _secp256k1_ecmult_table_get_ge)=None ->
 e!_secp256k1_gej_add_ge_var=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> le!_i=Some (Vint (Int.repr i)) ->
 Mem.load Mptr m bs 16=Some (Vptr bp Ptrofs.zero) ->
 Mem.load Mint32 m bp (strauss_wnaf_count_offset high)=Some (Vint (Int.repr bits)) ->
 (i<bits -> Mem.load Mint32 m bp (strauss_wnaf_base high+4*i)=Some (Vint (Int.repr (wnaf5_literal_value digit)))) ->
 (bits<=i -> digit=inl tt) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 fe_at m br 0 (words5 x) -> fe_at m br 40 (words5 y) -> fe_at m br 80 (words5 z) ->
 Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 Mem.range_perm m br 0 128 Cur Freeable -> Mem.range_perm m bd 0 88 Cur Freeable ->
 Mem.range_perm m bt 0 704 Cur Freeable -> Mem.range_perm m bx 0 320 Cur Freeable ->
 exists mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m (strauss_digit_dispatch high) E0
  (strauss_digit_dispatch_temps high le bp bt bx i bits digit) mf Out_normal /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  strauss_digit_action high digit xs ys ((ax,ay),az) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd) m mf.
Proof.
 intros Index Length Separate Local LookupSymbol AddSymbol R State NP I PS Count Load Absent
  PT PX Table Bounds Tight Aux AuxBounds AuxLiteral BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 pose proof (exec_strauss_digit_prefix high e le m bs bp i bits digit Index Length State NP I PS Count Load) as Prefix.
 pose proof (strauss_digit_prefix_condition high le bp i bits digit Absent) as Condition.
 destruct digit as [u|nib].
 - destruct u;exists m,x,y,z;split.
   + unfold strauss_digit_dispatch,strauss_digit_dispatch_temps.
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prefix|].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);
      [apply eval_Etempvar;exact Condition|reflexivity|constructor].
   + assert (FlagO:Mem.load Mint32 m br 120=Some (Vint (bit_int (Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z)))))).
     { assert (Eq:rescale_field_output z=az) by congruence;rewrite Eq;exact Flag. }
     split;[exact X|];split;[exact Y|];split;[exact Z|];split;[exact FlagO|];
     split;[exact BX|];split;[exact BY|];split;[exact BZ|];split;[exact Repr|];
     split;[exact FreeR|];split;[exact FreeD|];split;[exact FreeT|];split;[exact FreeX|];
     split;[apply keeps_permissions_refl|];split;[apply preserved_refl|apply lframe_refl].
 - assert (InRange:i<bits) by (destruct (Z_lt_dec i bits);[assumption|pose proof (Absent ltac:(lia));discriminate]).
   pose (lp:=strauss_digit_prefix_temps high le bp i bits (inr nib)).
   assert (Nlp:lp!_n=Some (Vint (Int.repr (lookup5_digit nib)))).
   { unfold lp,strauss_digit_prefix_temps;rewrite (proj2 (Z.ltb_lt i bits) InRange).
     rewrite PTree.gso by (destruct high;discriminate);apply PTree.gss. }
   assert (Rlp:lp!_r=Some (Vptr br Ptrofs.zero)).
   { unfold lp;rewrite strauss_digit_prefix_other by (destruct high;cbn [In];intuition discriminate);exact R. }
   assert (Slp:lp!_state=Some (Vptr bs Ptrofs.zero)).
   { unfold lp;rewrite strauss_digit_prefix_other by (destruct high;cbn [In];intuition discriminate);exact State. }
   assert (NPlp:lp!_np=Some (Vlong Int64.zero)).
   { unfold lp;rewrite strauss_digit_prefix_other by (destruct high;cbn [In];intuition discriminate);exact NP. }
   destruct (exec_strauss_digit_add high nib xs ys aux x y z ax ay az e lp m br bs bd bt bx
    Separate Local LookupSymbol AddSymbol Rlp Slp NPlp Nlp PT PX Table Bounds Tight Aux AuxBounds AuxLiteral
    BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX)
    as (mf & ox & oy & oz & Add & Post).
   exists mf,ox,oy,oz;split;[|exact Post].
   unfold strauss_digit_dispatch,strauss_digit_dispatch_temps.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Prefix|].
   eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
    [apply eval_Etempvar;exact Condition|reflexivity|exact Add].
Qed.
