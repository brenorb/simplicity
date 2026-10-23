(** The original generator nonzero-digit lookup/addition pair. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_clight_forward C.jet_clight_readonly_frame C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
 C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_generator_globals C.jet_secp_generator_lookup_words C.jet_secp_generator_lookup_literal
 C.jet_secp_generate_literal C.jet_secp_wnaf_literal_mask C.jet_secp_table_index
 C.jet_secp_zinv_literal_call C.jet_secp_rescale_literal C.jet_secp_canonical_zero
 C.jet_secp_add_literal C.jet_secp_statement_prefix.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge generator_table_block generator_lookup_words rescale_field_output literal_gej_ge_add literal_generate_small.

Definition generator_digit_add_statement high := Ssequence
 (curve_call _secp256k1_ecmult_table_get_ge_storage f_secp256k1_ecmult_table_get_ge_storage None
   [Eaddrof (Evar _tmpa curve_ge_type) (tptr curve_ge_type);
    Evar (generator_table_id high) (tarray (Tstruct __6125 noattr) 8192);
    Etempvar _n tint;Econst_int (Int.repr 15) tint])
 (curve_call _secp256k1_gej_add_zinv_var f_secp256k1_gej_add_zinv_var None
   [Etempvar _r (tptr (Tstruct __6123 noattr));Etempvar _r (tptr (Tstruct __6123 noattr));
    Eaddrof (Evar _tmpa curve_ge_type) (tptr curve_ge_type);curve_local_address _Z]).

Lemma generator_digit_add_source (high : bool) :
 match nth 10 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip with
 | Ssequence _ (Sloop (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence lo hi)))) _) =>
     match (if high then hi else lo) with Ssequence _ (Sifthenelse _ body _) => body | _=>Sskip end
 | _=>Sskip end = generator_digit_add_statement high.
Proof. destruct high;reflexivity. Qed.

Theorem exec_generator_digit_add high (word : Ty.tySem (Word 4))
 x y z inv (ax ay az : Ty.tySem (Word 8)) e le m bp ba bb :
 literal_wnaf_signed16 word mod 2=1 -> -16384<literal_wnaf_signed16 word<16384 ->
 NoDup [bp;ba;bb] -> (forall h,generator_table_state h m) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_n=Some (Vint (Int.repr (literal_wnaf_signed16 word))) ->
 e!_tmpa=Some (ba,curve_ge_type) -> e!_Z=Some (bb,curve_fe_type) ->
 e!_secp256k1_ecmult_table_get_ge_storage=None -> e!_secp256k1_gej_add_zinv_var=None ->
 e!(generator_table_id high)=None ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z -> square_input_bounds inv ->
 radix_value inv mod feP=1 ->
 radix_value x mod feP=@toZ (WordToZ 8) ax mod feP ->
 radix_value y mod feP=@toZ (WordToZ 8) ay mod feP ->
 radix_value z mod feP=@toZ (WordToZ 8) az mod feP ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m (generator_digit_add_statement high) E0 le mf Out_normal /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   @literal_gej_ge_add Alg.CoreFunSem (((ax,ay),az),@literal_generate_small high Alg.CoreFunSem word) /\
 (forall h,generator_table_state h mf) /\
 lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 intros Odd Range Sep Tables PR PN EA EZ EL EAdd ET BX BY BZ BI One HX HY HZ Flag X Y ZAt Inv PF AF IF.
 pose proof Sep as Sep0;repeat rewrite NoDup_cons_iff in Sep0;cbn [In] in Sep0.
 assert (PA : bp<>ba) by intuition congruence.
 assert (BA : bb<>ba) by intuition congruence.
 destruct (eval_generator_lookup_literal_caller high word 88 m ba Odd Range ltac:(lia) Tables AF)
   as (mi & Lookup & AFi & Fields & Values & Bounds & Square & FlagB & TablesI & FrameI).
 set (coords:=generator_lookup_words high (Z.to_nat (table_storage_index (literal_wnaf_signed16 word)))
   (negb (0<?literal_wnaf_signed16 word))) in *.
 assert (XI : fe_at mi bp 0 (words5 x)).
 { eapply field_at_lframe;[exact X|exact FrameI|];intros;left;exact PA. }
 assert (YI : fe_at mi bp 40 (words5 y)).
 { eapply field_at_lframe;[exact Y|exact FrameI|];intros;left;exact PA. }
 assert (ZI : fe_at mi bp 80 (words5 z)).
 { eapply field_at_lframe;[exact ZAt|exact FrameI|];intros;left;exact PA. }
 assert (InvI : fe_at mi bb 0 (words5 inv)).
 { eapply field_at_lframe;[exact Inv|exact FrameI|];intros;left;exact BA. }
 assert (PFI : Mem.range_perm mi bp 0 128 Cur Freeable).
 { eapply curve_keep_free;[lia|exact PF|exact FrameI|];intros;left;exact PA. }
 assert (IFI : Mem.range_perm mi bb 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact IF|exact FrameI|];intros;left;exact BA. }
 assert (FlagI : Mem.load Mint32 mi bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az))))).
 { rewrite (proj1 FrameI Mint32 bp 120);[exact Flag| |].
   - eapply Mem.perm_valid_block;apply (PF 0);lia.
   - intros;left;exact PA. }
 assert (RX : radix_value (coords false) mod feP=
   @toZ (WordToZ 8) (fst (@literal_generate_small high Alg.CoreFunSem word)) mod feP).
 { pose proof (Values false) as R.
   change (radix_value (coords false) mod feP=@toZ (WordToZ 8) (fst (@literal_generate_small high Alg.CoreFunSem word))) in R.
   rewrite <-R,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 assert (RY : radix_value (coords true) mod feP=
   @toZ (WordToZ 8) (snd (@literal_generate_small high Alg.CoreFunSem word)) mod feP).
 { pose proof (Values true) as R.
   change (radix_value (coords true) mod feP=@toZ (WordToZ 8) (snd (@literal_generate_small high Alg.CoreFunSem word))) in R.
   rewrite <-R,Z.mod_mod by (unfold feP,feR;lia);reflexivity. }
 destruct (eval_zinv_literal x y z (coords false) (coords true) inv ax ay az
   (fst (@literal_generate_small high Alg.CoreFunSem word)) (snd (@literal_generate_small high Alg.CoreFunSem word))
   mi bp ba bb Sep BX BY BZ (Square false) (Square true) BI One HX HY HZ RX RY FlagI FlagB
   XI YI ZI (Fields false) (Fields true) InvI PFI AFi IFI)
   as (mf & ox & oy & oz & Add & XO & YO & ZO & RawFlag & FlagO & UO & VO & InvO & PFO & AFO & IFO &
     BXO & BYO & BZO & Literal & FrameO).
 assert (FinalTables : forall h,generator_table_state h mf).
 { intro h;pose proof (TablesI h) as [Table Readonly];pose proof Table as [Valid _].
   assert (Outside : generator_table_block h<>bp /\ generator_table_block h<>ba /\ generator_table_block h<>bb).
   { repeat split;intro Equal;rewrite Equal in Readonly;
     match goal with F:Mem.range_perm mi ?b 0 ?size Cur Freeable |- _ =>
       match type of Readonly with readonly_region_bounds _ b _ _ =>
         destruct (proj1 (Readonly 0 Cur Freeable) (F 0 ltac:(lia))) as [_ Order];inversion Order end end. }
   pose proof (generator_table_rep_lframe h mi mf _ Table FrameO ltac:(intro;exact Outside)) as TF.
   split;[exact TF|].
   eapply readonly_bounds_transport;[exact Valid|exact Readonly| |exact (proj1 (proj2 TF))].
   exact (proj2 (clight_exec_forward secp_ge) _ _ _ _ _ _ Add). }
 assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf).
 { eapply lframe_trans;[|exact FrameO].
   eapply lframe_implies;[exact FrameI|];intros b pos Outside Valid;left;tauto. }
 exists mf,ox,oy,oz;split.
 - unfold generator_digit_add_statement.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mi).
   + eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero;Vptr (generator_table_block high) Ptrofs.zero;
       Vint (Int.repr (literal_wnaf_signed16 word));Vint (Int.repr 15)]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact EL.
     * eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact EA|reflexivity|].
       eapply eval_Econs.
       -- eapply eval_Elvalue.
          { eapply eval_Evar_global;[exact ET|apply generator_table_symbol]. }
          { apply deref_loc_reference;reflexivity. }
       -- reflexivity.
       -- eapply eval_Econs;[apply eval_Etempvar;exact PN|reflexivity|].
          eapply eval_Econs;[constructor|reflexivity|constructor].
     * exact Lookup.
   + eapply exec_curve_call with
       (vargs:=[Vptr bp Ptrofs.zero;Vptr bp Ptrofs.zero;Vptr ba Ptrofs.zero;Vptr bb Ptrofs.zero]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact EAdd.
     * eapply eval_Econs;[apply eval_Etempvar;exact PR|reflexivity|].
       eapply eval_Econs;[apply eval_Etempvar;exact PR|reflexivity|].
       eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;exact EA|reflexivity|].
       eapply eval_Econs;[apply eval_curve_local;exact EZ|reflexivity|constructor].
     * exact Add.
 - destruct (@literal_generate_small high Alg.CoreFunSem word) as [sx sy];cbn [fst snd] in Literal.
   repeat first [assumption|split].
Qed.
