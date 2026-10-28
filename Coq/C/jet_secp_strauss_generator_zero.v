(** Zero generator wNAF, preserving the existing point-path bit count. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_toZ C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_memset_model
 C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_zeros C.jet_secp_wnaf_literal_array
 C.jet_secp_wnaf_loop C.jet_secp_wnaf_memset C.jet_secp_generator_wnaf_setup
 C.jet_secp_generator_bits_max C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.

Lemma strauss_wnaf15_zero_digits (word:Ty.tySem (Word 7)) :
 @toZ (WordToZ 7) word=0 -> literal_wnaf15_digits (inl tt,word)=repeat (inl tt) 129.
Proof.
 intro Zero;destruct (literal_wnaf_zero_power 129 word 0 ltac:(rewrite Z.mul_0_r;exact Zero))
  as (final & Run & Value).
 rewrite <-literal_wnaf15_digits_order,Run;reflexivity.
Qed.

Lemma strauss_wnaf_last_zero digits last :
 wnaf_last digits 129 last ->
 rev (map (fun i=>digits (Z.of_nat i)) (seq 0 129))=repeat 0 129 -> last= -1.
Proof.
 intros Last Values;destruct Last as (Bound & Highest & Present).
 destruct (Z.eq_dec last (-1)) as [Eq|Other];[exact Eq|].
 assert (Range:0<=last<129) by lia.
 apply (f_equal (@rev Z)) in Values;rewrite rev_involutive,rev_repeat in Values.
 assert (Member:In (digits last) (map (fun i=>digits (Z.of_nat i)) (seq 0 129))).
 { apply in_map_iff;exists (Z.to_nat last);split;[rewrite Z2Nat.id by lia;reflexivity|apply in_seq;lia]. }
 rewrite Values in Member;apply repeat_spec in Member;destruct Present;congruence.
Qed.

Theorem exec_strauss_generator_wnaf_zero (Model:memset_model) (high:bool) e le m ba b :
 e!(if high then _wnaf_ng_128 else _wnaf_ng_1)=Some (b,tarray tint 129) ->
 e!(if high then _ng_128 else _ng_1)=Some (ba,Tstruct __5826 noattr) ->
 e!_secp256k1_ecmult_wnaf=None -> ba<>b ->
 scalar_at m ba 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 Mem.range_perm m b 0 516 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (generator_wnaf_half high) E0
  (generator_wnaf_half_temps high le 0) mf Out_normal /\
 Mem.range_perm mf b 0 516 Cur Freeable /\ lframe (fun old _=>old<>b) m mf /\
 (forall old pos k p,Mem.valid_block m old -> (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
Proof.
 intros Array Scalar Symbol Separate Input Owned.
 pose (word:=@Word.zero 7 Alg.CoreFunSem tt).
 assert (Value:@toZ (WordToZ 7) word=0) by (unfold word;apply Word.zero_correct).
 assert (InputWord:scalar_at m ba 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word)))).
 { rewrite Value;exact Input. }
 destruct (exec_generator_wnaf_half high e le m word ba b Array Scalar Symbol Separate InputWord Owned
  ltac:(intros mi local Alloc;exact (generate_memset_steps Model m mi local ba b Alloc Owned)))
  as (mf & last & digits & Call & Memory & Bound & Free & Frame & Literal & Perms).
 assert (Last:last= -1).
 { apply (strauss_wnaf_last_zero digits last).
   - exact (wnaf_array_last _ _ _ _ _ _ _ _ _ Memory).
   - pose proof (f_equal (fun ds:list (Ty.tySem literal_wnaf_digit)=>map wnaf_literal_value ds)
      (strauss_wnaf15_zero_digits word Value)) as ZeroValues.
     rewrite map_repeat in ZeroValues;exact (eq_trans (eq_sym Literal) ZeroValues). }
 subst last;exists mf;split;[exact Call|];split;[exact Free|];split;assumption.
Qed.

Lemma exec_strauss_generator_max_zero e le m bits :
 0<=bits<=129 -> le!_bits=Some (Vint (Int.repr bits)) ->
 le!_bits_ng_1=Some (Vint Int.zero) -> le!_bits_ng_128=Some (Vint Int.zero) ->
 Clight2.exec_stmt secp_ge e le m generator_bits_max E0 le m Out_normal.
Proof.
 intros Bound Bits Low High.
 pose proof (exec_generator_raise_bits false e le m bits 0 Bound ltac:(clear;lia) Bits Low) as First.
 pose proof (exec_generator_raise_bits true e le m bits 0 Bound ltac:(clear;lia) Bits High) as Last.
 unfold generator_raise_temps in First,Last;rewrite (proj2 (Z.ltb_ge bits 0) ltac:(lia)) in First,Last.
 rewrite generator_bits_max_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact First|exact Last].
Qed.

Require Import C.jet_secp_generator_split_call C.jet_secp_scalar_add_reader_support C.jet_secp_curve_frame C.jet_secp_field_read_preservation.

Definition strauss_zero_wnaf_temps le :=
 generator_wnaf_half_temps true (generator_wnaf_half_temps false le 0) 0.
Theorem exec_strauss_zero_wnaf_setup (Model:memset_model) e le m b0 b128 bw0 bw128 bits :
 NoDup [b0;b128;bw0;bw128] ->
 e!_ng_1=Some (b0,Tstruct __5826 noattr) -> e!_ng_128=Some (b128,Tstruct __5826 noattr) ->
 e!_wnaf_ng_1=Some (bw0,tarray tint 129) -> e!_wnaf_ng_128=Some (bw128,tarray tint 129) ->
 e!_secp256k1_ecmult_wnaf=None -> 0<=bits<=129 -> le!_bits=Some (Vint (Int.repr bits)) ->
 scalar_at m b0 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 scalar_at m b128 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 Mem.range_perm m bw0 0 516 Cur Freeable -> Mem.range_perm m bw128 0 516 Cur Freeable ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m generator_wnaf_setup E0 (strauss_zero_wnaf_temps le) mf Out_normal /\
 (strauss_zero_wnaf_temps le)!_bits=Some (Vint (Int.repr bits)) /\
 (strauss_zero_wnaf_temps le)!_bits_ng_1=Some (Vint Int.zero) /\
 (strauss_zero_wnaf_temps le)!_bits_ng_128=Some (Vint Int.zero) /\
 Mem.range_perm mf bw0 0 516 Cur Freeable /\ Mem.range_perm mf bw128 0 516 Cur Freeable /\
 lframe (fun b _=>b<>bw0 /\ b<>bw128) m mf /\
 (forall old pos k p,Mem.valid_block m old -> (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
Proof.
 intros Separate S0 S128 W0 W128 Symbol Bound Bits Low High Free0 Free128.
 assert (S0W0:b0<>bw0) by
  (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 assert (S128W0:b128<>bw0) by
  (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 assert (S128W128:b128<>bw128) by
  (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 assert (W0W128:bw0<>bw128) by
  (clear -Separate;repeat rewrite NoDup_cons_iff in Separate;cbn [In] in Separate;intuition congruence).
 destruct (exec_strauss_generator_wnaf_zero Model false e le m b0 bw0 W0 S0 Symbol S0W0 Low Free0)
  as (ml & Call0 & F0 & Frame0 & Perm0).
 pose (ll:=generator_wnaf_half_temps false le 0).
 assert (HighL:scalar_at ml b128 0 [Int64.zero;Int64.zero;Int64.zero;Int64.zero]).
 { eapply scalar_at_lframe;[exact High|exact Frame0|intros;exact S128W0]. }
 assert (F128L:Mem.range_perm ml bw128 0 516 Cur Freeable).
 { eapply curve_keep_free;[clear;lia|exact Free128|exact Frame0|intros;congruence]. }
 destruct (exec_strauss_generator_wnaf_zero Model true e ll ml b128 bw128 W128 S128 Symbol S128W128 HighL F128L)
  as (mf & Call128 & F128 & Frame128 & Perm128).
 pose (lh:=strauss_zero_wnaf_temps le).
 assert (BitsH:lh!_bits=Some (Vint (Int.repr bits))).
 { unfold lh,strauss_zero_wnaf_temps;rewrite !generator_wnaf_half_other by discriminate;exact Bits. }
 assert (C0:lh!_bits_ng_1=Some (Vint Int.zero)).
 { unfold lh,strauss_zero_wnaf_temps;rewrite generator_wnaf_half_other by discriminate;apply PTree.gss. }
 assert (C128:lh!_bits_ng_128=Some (Vint Int.zero)).
 { unfold lh,strauss_zero_wnaf_temps;apply PTree.gss. }
 exists mf;split.
 - rewrite generator_wnaf_setup_source.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call0|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call128|].
   exact (exec_strauss_generator_max_zero e lh mf bits Bound BitsH C0 C128).
 - split;[exact BitsH|];split;[exact C0|];split;[exact C128|];split.
   + eapply curve_keep_free;[clear;lia|exact F0|exact Frame128|intros;exact W0W128].
   + split;[exact F128|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact Frame0|intros b p [W _] _;exact W].
       -- eapply lframe_implies;[exact Frame128|intros b p [_ W] _;exact W].
     * intros old pos k p Valid;rewrite (Perm128 old pos k p (proj2 (proj2 Frame0) old Valid));apply Perm0;exact Valid.
Qed.

Lemma strauss_zero_wnaf_other le id :
 ~In id [_bits_ng_1;_bits_ng_128;_t'6;_t'7] -> (strauss_zero_wnaf_temps le)!id=le!id.
Proof.
 intro Outside;unfold strauss_zero_wnaf_temps;rewrite !generator_wnaf_half_other;
 cbn [In] in Outside;intuition congruence.
Qed.

