(** Both original window-5 lookup/addition bodies in the single-point
    descending loop, including state-pointer loads and the actual calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_generator_loop_control C.jet_secp_generator_globalz_call C.jet_secp_strauss_table_call
 C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_multiply_finish_product C.jet_secp_multiply_normalize_bridge
 C.jet_secp_square_columns C.jet_secp_field_negate_separate C.jet_secp_field_mul_small
 C.jet_secp_globalz_loop C.jet_secp_globalz_pass2 C.jet_secp_globalz_word_walk
 C.jet_secp_scalar_table_literal C.jet_secp_lookup5_literal C.jet_secp_table_get_literal
 C.jet_secp_table_get_lambda_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero
 C.jet_secp_add_literal C.jet_secp_mixed_xy_literal C.jet_secp_mixed_xy_framed
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge rescale_field_output literal_gej_ge_add literal_lookup5 literal_ge_scale_lambda.
Set Default Timeout 10.

Definition strauss_digit_table_arg tmp ty := Ebinop Oadd (Etempvar tmp (tptr ty))
 (Ebinop Omul (Etempvar _np tulong) strauss_table_width tulong) (tptr ty).
Definition strauss_digit_lookup_statement (high:bool) :=
 if high then
  Ssequence (Sset _t'19 (generator_state_pointer _pre_a (Tstruct __6121 noattr)))
   (Ssequence (Sset _t'20 (generator_state_pointer _aux (Tstruct __5467 noattr)))
    (curve_call _secp256k1_ecmult_table_get_ge_lambda f_secp256k1_ecmult_table_get_ge_lambda None
     [Eaddrof (Evar _tmpa (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
      strauss_digit_table_arg _t'19 (Tstruct __6121 noattr);
      strauss_digit_table_arg _t'20 (Tstruct __5467 noattr);Etempvar _n tint;Econst_int (Int.repr 5) tint]))
 else
  Ssequence (Sset _t'25 (generator_state_pointer _pre_a (Tstruct __6121 noattr)))
   (curve_call _secp256k1_ecmult_table_get_ge f_secp256k1_ecmult_table_get_ge None
    [Eaddrof (Evar _tmpa (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
     strauss_digit_table_arg _t'25 (Tstruct __6121 noattr);Etempvar _n tint;Econst_int (Int.repr 5) tint]).
Definition strauss_digit_mixed_call := curve_call _secp256k1_gej_add_ge_var f_secp256k1_gej_add_ge_var None
 [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _r (tptr (Tstruct __6123 noattr));
  Eaddrof (Evar _tmpa (Tstruct __6121 noattr)) (tptr (Tstruct __6121 noattr));
  Ecast (Econst_int Int.zero tint) (tptr tvoid)].
Definition strauss_digit_add_statement high := Ssequence (strauss_digit_lookup_statement high) strauss_digit_mixed_call.
Definition strauss_digit_lookup_temps (high:bool) le bt bx :=
 if high then PTree.set _t'20 (Vptr bx Ptrofs.zero) (PTree.set _t'19 (Vptr bt Ptrofs.zero) le)
 else PTree.set _t'25 (Vptr bt Ptrofs.zero) le.
Definition strauss_digit_point (high:bool) (nib:Ty.tySem (Word 2)) (xs ys:nat->nat->int64)
 : Ty.tySem literal_table_ge :=
 let point:=@literal_lookup5 Alg.CoreFunSem (nib,globalz_word_vector (globalz_decoded_points xs ys)) in
 if high then @literal_ge_scale_lambda Alg.CoreFunSem point else point.

Lemma strauss_digit_add_source (high:bool) :
 match generator_nongenerator_statement with
 | Ssequence _ (Sloop (Ssequence _ (Ssequence lo hi)) _) =>
   match (if high then hi else lo) with Ssequence _ (Sifthenelse _ body _) => body | _=>Sskip end
 | _=>Sskip end=strauss_digit_add_statement high.
Proof. destruct high;reflexivity. Qed.

Lemma strauss_digit_lookup_other (high:bool) le bt bx id :
 ~In id [_t'19;_t'20;_t'25] -> (strauss_digit_lookup_temps high le bt bx)!id=le!id.
Proof.
 intro Outside;unfold strauss_digit_lookup_temps;destruct high;
 rewrite !PTree.gso;cbn [In] in Outside;intuition congruence.
Qed.

Lemma eval_strauss_digit_table_arg e le m tmp ty b :
 le!tmp=Some (Vptr b Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 eval_expr secp_ge e le m (strauss_digit_table_arg tmp ty) (Vptr b Ptrofs.zero).
Proof.
 intros Pointer NP;unfold strauss_digit_table_arg;eapply eval_Ebinop with
  (v1:=Vptr b Ptrofs.zero) (v2:=Vlong Int64.zero).
 - apply eval_Etempvar;exact Pointer.
 - eapply eval_Ebinop with (v1:=Vlong Int64.zero) (v2:=Vlong (Int64.repr 8));
    [apply eval_Etempvar;exact NP|apply eval_strauss_table_width|reflexivity].
 - unfold sem_binary_operation,sem_add,sem_add_ptr_long.
   change (Some (Vptr b (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr (sizeof (genv_cenv secp_ge) ty)) Ptrofs.zero)))=Some (Vptr b Ptrofs.zero)).
   rewrite Ptrofs.mul_zero,Ptrofs.add_zero;reflexivity.
Qed.

(** Internal call adapter; the following theorem discharges its call premise. *)
Lemma exec_strauss_lookup_from_call (high:bool) e le m mf bs bd bt bx n :
 e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!(if high then _secp256k1_ecmult_table_get_ge_lambda else _secp256k1_ecmult_table_get_ge)=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) -> le!_n=Some (Vint n) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 Clight2.eval_funcall secp_ge m
  (Internal (if high then f_secp256k1_ecmult_table_get_ge_lambda else f_secp256k1_ecmult_table_get_ge))
  ([Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero]++(if high then [Vptr bx Ptrofs.zero] else [])++
   [Vint n;Vint (Int.repr 5)]) E0 mf Vundef ->
 Clight2.exec_stmt secp_ge e le m (strauss_digit_lookup_statement high) E0
  (strauss_digit_lookup_temps high le bt bx) mf Out_normal.
Proof.
 intros Local Symbol State NP N Table Aux;destruct high;intro Call;
  unfold strauss_digit_lookup_statement,strauss_digit_lookup_temps.
 - pose (lt:=PTree.set _t'19 (Vptr bt Ptrofs.zero) le).
   pose (lx:=PTree.set _t'20 (Vptr bx Ptrofs.zero) lt).
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lt) (m1:=m).
   + apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=8);
      [left;reflexivity|exact State|clear;lia|change Ptrofs.max_unsigned with 18446744073709551615;clear;lia|exact Table].
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lx) (m1:=m).
     * apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=0).
       -- right;left;reflexivity.
       -- unfold lt;rewrite PTree.gso by discriminate;exact State.
       -- clear;lia.
       -- change Ptrofs.max_unsigned with 18446744073709551615;clear;lia.
       -- exact Aux.
     * eapply exec_curve_call with (vargs:=[Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vptr bx Ptrofs.zero;Vint n;Vint (Int.repr 5)]) (v:=Vundef).
       -- unfold secp_pure;repeat first [left;reflexivity|right].
       -- exact Symbol.
       -- eapply eval_Econs with (v1:=Vptr bd Ptrofs.zero);
           [apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|].
          eapply eval_Econs with (v1:=Vptr bt Ptrofs.zero).
          ++ apply eval_strauss_digit_table_arg;
              [unfold lx,lt;rewrite PTree.gso by discriminate;apply PTree.gss|
               unfold lx,lt;rewrite !PTree.gso by discriminate;exact NP].
          ++ reflexivity.
          ++ eapply eval_Econs with (v1:=Vptr bx Ptrofs.zero).
             ** apply eval_strauss_digit_table_arg;
                 [unfold lx;apply PTree.gss|unfold lx,lt;rewrite !PTree.gso by discriminate;exact NP].
             ** reflexivity.
             ** eapply eval_Econs;
                 [apply eval_Etempvar;unfold lx,lt;rewrite !PTree.gso by discriminate;exact N|reflexivity|].
                eapply eval_Econs;[constructor|reflexivity|constructor].
       -- exact Call.
 - pose (lt:=PTree.set _t'25 (Vptr bt Ptrofs.zero) le).
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lt) (m1:=m).
   + apply exec_Sset;eapply eval_generator_state_pointer with (base:=0) (delta:=8);
      [left;reflexivity|exact State|clear;lia|change Ptrofs.max_unsigned with 18446744073709551615;clear;lia|exact Table].
   + eapply exec_curve_call with (vargs:=[Vptr bd Ptrofs.zero;Vptr bt Ptrofs.zero;Vint n;Vint (Int.repr 5)]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vptr bd Ptrofs.zero);
        [apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|].
       eapply eval_Econs with (v1:=Vptr bt Ptrofs.zero).
       -- apply eval_strauss_digit_table_arg;
           [unfold lt;apply PTree.gss|unfold lt;rewrite PTree.gso by discriminate;exact NP].
       -- reflexivity.
       -- eapply eval_Econs;
           [apply eval_Etempvar;unfold lt;rewrite PTree.gso by discriminate;exact N|reflexivity|].
          eapply eval_Econs;[constructor|reflexivity|constructor].
     * exact Call.
Qed.

Theorem exec_strauss_digit_lookup (high:bool) (nib:Ty.tySem (Word 2)) xs ys aux e le m bs bd bt bx :
 bd<>bt -> bd<>bx -> e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!(if high then _secp256k1_ecmult_table_get_ge_lambda else _secp256k1_ecmult_table_get_ge)=None ->
 le!_state=Some (Vptr bs Ptrofs.zero) -> le!_np=Some (Vlong Int64.zero) ->
 le!_n=Some (Vint (Int.repr (lookup5_digit nib))) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 globalz_table_rep m bt xs ys -> globalz_table_bounds xs ys ->
 (forall k,(k<8)%nat -> mul_small_input_bounds (ys k)) ->
 (forall k,(k<8)%nat -> fe_at m bx (40*Z.of_nat k) (words5 (aux k))) ->
 (forall k,(k<8)%nat -> square_input_bounds (aux k)) ->
 (forall k,(k<8)%nat -> rescale_field_output (aux k)=
  @C.jet_secp_beta_spec.literal_fe_multiply_beta Alg.CoreFunSem (rescale_field_output (xs k))) ->
 Mem.range_perm m bd 0 88 Cur Freeable -> Mem.range_perm m bt 0 704 Cur Freeable ->
 Mem.range_perm m bx 0 320 Cur Freeable -> exists mf u v,
 Clight2.exec_stmt secp_ge e le m (strauss_digit_lookup_statement high) E0
  (strauss_digit_lookup_temps high le bt bx) mf Out_normal /\
 fe_at mf bd 0 (words5 u) /\ fe_at mf bd 40 (words5 v) /\
 (rescale_field_output u,rescale_field_output v)=strauss_digit_point high nib xs ys /\
 square_input_bounds u /\ square_input_bounds v /\ Mem.load Mint32 mf bd 80=Some (Vint Int.zero) /\
 Mem.range_perm mf bd 0 88 Cur Freeable /\ keeps_permissions m mf /\ readonly_preserved m mf /\
 lframe (fun b _=>b<>bd) m mf.
Proof.
 intros DT DX Local Symbol State NP N PT PX Table Bounds Tight Aux AuxBounds AuxLiteral FreeD FreeT FreeX.
 destruct high.
 - destruct (eval_table_get_lambda_lookup5 nib xs ys aux m bd bt bx DT DX Table Aux AuxBounds Tight AuxLiteral FreeT FreeX FreeD)
    as (mf & Call & X & Y & Literal & BU & BV & Flag & FD & FT & FX & Keep & Frame & Readonly).
   exists mf;do 2 eexists;split.
   + apply (exec_strauss_lookup_from_call true e le m mf bs bd bt bx _ Local Symbol State NP N PT PX);exact Call.
   + split;[exact X|];split;[exact Y|];split;[exact Literal|];split;[exact BU|];split;[exact BV|];
      split;[exact Flag|];split;[exact FD|];split;[exact Keep|];split;assumption.
 - destruct (eval_table_get_lookup5 nib xs ys m bd bt DT Table Bounds Tight FreeT FreeD)
    as (mf & Call & X & Y & Literal & BU & BV & Flag & FD & FT & Keep & Frame & Readonly).
   exists mf;do 2 eexists;split.
   + apply (exec_strauss_lookup_from_call false e le m mf bs bd bt bx _ Local Symbol State NP N PT PX);exact Call.
   + split;[exact X|];split;[exact Y|];split;[exact Literal|];split;[exact BU|];split;[exact BV|];
      split;[exact Flag|];split;[exact FD|];split;[exact Keep|];split;assumption.
Qed.

Theorem exec_strauss_digit_add (high:bool) (nib:Ty.tySem (Word 2)) xs ys aux x y z
 (ax ay az:Ty.tySem (Word 8)) e le m br bs bd bt bx :
 NoDup [br;bd;bt;bx] -> e!_tmpa=Some (bd,Tstruct __6121 noattr) ->
 e!(if high then _secp256k1_ecmult_table_get_ge_lambda else _secp256k1_ecmult_table_get_ge)=None ->
 e!_secp256k1_gej_add_ge_var=None ->
 le!_r=Some (Vptr br Ptrofs.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> le!_n=Some (Vint (Int.repr (lookup5_digit nib))) ->
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
 Clight2.exec_stmt secp_ge e le m (strauss_digit_add_statement high) E0
  (strauss_digit_lookup_temps high le bt bx) mf Out_normal /\
 fe_at mf br 0 (words5 ox) /\ fe_at mf br 40 (words5 oy) /\ fe_at mf br 80 (words5 oz) /\
 Mem.load Mint32 mf br 120=Some (Vint (bit_int (Bit.toBool
  (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
  @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),strauss_digit_point high nib xs ys) /\
 Mem.range_perm mf br 0 128 Cur Freeable /\ Mem.range_perm mf bd 0 88 Cur Freeable /\
 Mem.range_perm mf bt 0 704 Cur Freeable /\ Mem.range_perm mf bx 0 320 Cur Freeable /\
 keeps_permissions m mf /\ readonly_preserved m mf /\ lframe (fun b _=>b<>br /\ b<>bd) m mf.
Proof.
 intros Separate Local LookupSymbol AddSymbol R State NP N PT PX Table Bounds Tight Aux AuxBounds AuxLiteral
  BX BY BZ Repr X Y Z Flag FreeR FreeD FreeT FreeX.
 assert (RD:br<>bd) by (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 assert (DT:bd<>bt) by (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 assert (DX:bd<>bx) by (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 destruct (exec_strauss_digit_lookup high nib xs ys aux e le m bs bd bt bx DT DX Local LookupSymbol State NP N PT PX
  Table Bounds Tight Aux AuxBounds AuxLiteral FreeD FreeT FreeX)
  as (mi & u & v & Lookup & U & V & LiteralL & BU & BV & FlagB & FDI & KeepL & ReadonlyL & FrameL).
 assert (XI:fe_at mi br 0 (words5 x)) by (eapply field_at_lframe;[exact X|exact FrameL|intros;exact RD]).
 assert (YI:fe_at mi br 40 (words5 y)) by (eapply field_at_lframe;[exact Y|exact FrameL|intros;exact RD]).
 assert (ZI:fe_at mi br 80 (words5 z)) by (eapply field_at_lframe;[exact Z|exact FrameL|intros;exact RD]).
 assert (FRI:Mem.range_perm mi br 0 128 Cur Freeable) by (intros pos Range;apply KeepL,FreeR;exact Range).
 assert (FlagI:Mem.load Mint32 mi br 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))))).
 { rewrite (proj1 FrameL Mint32 br 120);[exact Flag|eapply Mem.perm_valid_block;apply (FreeR 0);clear;lia|intros;exact RD]. }
 assert (RX:radix_value x mod feP=@toZ (WordToZ 8) ax mod feP).
 { assert (Eq:rescale_field_output x=ax) by congruence;rewrite <-Eq;apply mixed_xy_output_residue. }
 assert (RY:radix_value y mod feP=@toZ (WordToZ 8) ay mod feP).
 { assert (Eq:rescale_field_output y=ay) by congruence;rewrite <-Eq;apply mixed_xy_output_residue. }
 assert (RZ:radix_value z mod feP=@toZ (WordToZ 8) az mod feP).
 { assert (Eq:rescale_field_output z=az) by congruence;rewrite <-Eq;apply mixed_xy_output_residue. }
 destruct (eval_mixed_xy_literal_framed x y z u v ax ay az (rescale_field_output u) (rescale_field_output v)
  mi br bd RD BX BY BZ BU BV RX RY RZ (mixed_xy_output_residue u) (mixed_xy_output_residue v)
  FlagI FlagB XI YI ZI U V FRI FDI)
  as (mf & ox & oy & oz & Call & XO & YO & ZO & FlagO & FRF & FDF & BXO & BYO & BZO & LiteralM & KeepM & ReadonlyM & FrameM).
 assert (Keep:keeps_permissions m mf) by (eapply keeps_permissions_trans;[exact KeepL|exact KeepM]).
 exists mf,ox,oy,oz;split.
 - unfold strauss_digit_add_statement;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Lookup|].
   unfold strauss_digit_mixed_call;eapply exec_curve_call with
    (vargs:=[Vptr br Ptrofs.zero;Vptr br Ptrofs.zero;Vptr bd Ptrofs.zero;Vlong Int64.zero]) (v:=Vundef).
   + unfold secp_pure;repeat first [left;reflexivity|right].
   + exact AddSymbol.
   + eapply eval_Econs with (v1:=Vptr br Ptrofs.zero).
     * apply eval_Etempvar;rewrite strauss_digit_lookup_other by (clear;cbn [In];intuition discriminate);exact R.
     * reflexivity.
     * eapply eval_Econs with (v1:=Vptr br Ptrofs.zero).
       -- apply eval_Etempvar;rewrite strauss_digit_lookup_other by (clear;cbn [In];intuition discriminate);exact R.
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr bd Ptrofs.zero);
           [apply eval_Eaddrof;apply eval_Evar_local;exact Local|reflexivity|].
          eapply eval_Econs with (v1:=Vlong Int64.zero);[eapply eval_Ecast;[constructor|reflexivity]|reflexivity|constructor].
   + exact Call.
 - split;[exact XO|];split;[exact YO|];split;[exact ZO|];split;[exact FlagO|];
   split;[exact BXO|];split;[exact BYO|];split;[exact BZO|];split.
   + rewrite LiteralL in LiteralM;exact LiteralM.
   + split;[exact FRF|];split;[exact FDF|];split.
     * intros pos Range;apply Keep,FreeT;exact Range.
     * split;[intros pos Range;apply Keep,FreeX;exact Range|];split;[exact Keep|];split.
       -- eapply preserved_trans;[exact ReadonlyL|exact ReadonlyM].
       -- eapply lframe_trans;[|exact FrameM];eapply lframe_implies;[exact FrameL|intros b pos [_ D] _;exact D].
Qed.
