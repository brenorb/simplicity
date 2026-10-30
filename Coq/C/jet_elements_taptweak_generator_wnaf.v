(** Both actual linked generator wNAF calls and maximum-length updates.
    The existing memset model derives both real clears; there is no desired
    callee execution or result premise. This is an internal component. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_generator_split_call
  C.jet_secp_generator_bits_max C.jet_secp_generator_globals C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_get_b32_numeric C.jet_secp_scalar_add_reader_support
  C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop
  C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_function15.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Require Import C.jet_secp_generator_wnaf_setup C.jet_secp_generator_bits_max
 C.jet_memset_model C.jet_clight_internal_preserve C.jet_elements_taptweak_pure C.jet_elements_taptweak_generator_globals.
Require Import C.jet_elements_taptweak_wnaf15 C.jet_elements_taptweak_wnaf_call.
Local Opaque elements_taptweak_ge elements_taptweak_generator_table_block.
Lemma eval_elements_taptweak_generator_raise_guard (high : bool) e le m current candidate :
 0<=current<=129 -> 0<=candidate<=129 -> le!_bits=Some (Vint (Int.repr current)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr candidate)) ->
 eval_expr elements_taptweak_ge e le m
 (Ebinop Ogt (Etempvar (if high then _bits_ng_128 else _bits_ng_1) tint) (Etempvar _bits tint) tint)
 (Vint (if current <? candidate then Int.one else Int.zero)).
Proof.
 intros Current Candidate Bits Count;eapply eval_Ebinop;
  [apply eval_Etempvar;exact Count|apply eval_Etempvar;exact Bits|].
 change (Some (Val.of_bool (Int.lt (Int.repr current) (Int.repr candidate)))=
  Some (Vint (if current <? candidate then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by
  (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
 destruct (Coqlib.zlt current candidate),(Z.ltb_spec current candidate);try lia;reflexivity.
Qed.
Theorem exec_elements_taptweak_generator_raise_bits (high : bool) e le m current candidate :
 0<=current<=129 -> 0<=candidate<=129 -> le!_bits=Some (Vint (Int.repr current)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr candidate)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m (generator_raise_bits high) E0
  (generator_raise_temps le current candidate) m Out_normal.
Proof.
 intros Current Candidate Bits Count.
 pose proof (eval_elements_taptweak_generator_raise_guard high e le m current candidate Current Candidate Bits Count) as Guard.
 unfold generator_raise_bits,generator_raise_temps.
 destruct (current <? candidate) eqn:Choose.
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=Datatypes.true);
    [exact Guard|reflexivity|apply exec_Sset;apply eval_Etempvar;exact Count].
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=Datatypes.false);[exact Guard|reflexivity|constructor].
Qed.
Theorem exec_elements_taptweak_generator_bits_max e le m low high :
 0<=low<=129 -> 0<=high<=129 -> le!_bits=Some (Vint Int.zero) ->
 le!_bits_ng_1=Some (Vint (Int.repr low)) -> le!_bits_ng_128=Some (Vint (Int.repr high)) ->
 Clight2.exec_stmt elements_taptweak_ge e le m generator_bits_max E0 (generator_bits_max_temps le low high) m Out_normal /\
 (generator_bits_max_temps le low high)!_bits=Some (Vint (Int.repr (Z.max low high))) /\
 forall id,id<>_bits -> (generator_bits_max_temps le low high)!id=le!id.
Proof.
 intros Low High Bits CountLow CountHigh.
 pose proof (generator_raise_bits_value le 0 low Bits) as AfterLow.
 rewrite Z.max_r in AfterLow by lia.
 assert (AfterHigh:(generator_raise_temps le 0 low)!_bits_ng_128=Some (Vint (Int.repr high))).
 { rewrite generator_raise_bits_other by discriminate;exact CountHigh. }
 split.
 - rewrite generator_bits_max_source;unfold generator_bits_max_temps.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=generator_raise_temps le 0 low).
   + apply (exec_elements_taptweak_generator_raise_bits Datatypes.false e le m 0 low);try assumption;lia.
   + exact (exec_elements_taptweak_generator_raise_bits Datatypes.true e _ m low high Low High AfterLow AfterHigh).
 - split.
   + unfold generator_bits_max_temps;apply generator_raise_bits_value;exact AfterLow.
   + intros id Other;unfold generator_bits_max_temps;rewrite !generator_raise_bits_other by exact Other;reflexivity.
Qed.
Theorem exec_elements_taptweak_generator_wnaf_half (Model:memset_model) (high : bool) e le m word ba b :
  e!(if high then _wnaf_ng_128 else _wnaf_ng_1)=Some (b,tarray tint 129) ->
  e!(if high then _ng_128 else _ng_1)=Some (ba,Tstruct __5826 noattr) ->
  e!_secp256k1_ecmult_wnaf=None -> ba<>b ->
  scalar_at m ba 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word))) ->
  Mem.range_perm m b 0 516 Cur Freeable ->
  exists mf last digits,
    Clight2.exec_stmt elements_taptweak_ge e le m (generator_wnaf_half high) E0
      (generator_wnaf_half_temps high le (last+1)) mf Out_normal /\
    wnaf_array_state mf b 0 129 15 1 129 last digits /\
    0<=last+1<=129 /\ Mem.range_perm mf b 0 516 Cur Freeable /\
    lframe (fun old _=>old<>b) m mf /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
      rev (map (fun i=>digits (Z.of_nat i)) (seq 0 129)) /\
    (forall old pos k p,Mem.valid_block m old ->
      (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)) /\readonly_preserved m mf.
Proof.
  intros ArrayLocal ScalarLocal Symbol Separate Input Owned.
  destruct(eval_elements_taptweak_wnaf15 Model word m ba 0 b Input Separate Owned)
   as(mf & last & digits & Call & Array & Bound & Free & Blocks & Frame & Source & Literal & Trim & Perms & Readonly & Keep).
  exists mf,last,digits;split;[|repeat first [assumption|split]].
  unfold generator_wnaf_half,generator_wnaf_half_temps.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0)
    (le1:=PTree.set (if high then _t'7 else _t'6) (Vint (Int.repr (last+1))) le) (m1:=mf).
  - eapply exec_elements_taptweak_wnaf_call with
      (vargs:=[Vptr b Ptrofs.zero;Vint (Int.repr 129);Vptr ba Ptrofs.zero;Vint (Int.repr 15)])
      (v:=Vint (Int.repr (last+1))).
    + exact Symbol.
    + eapply eval_Econs with (v1:=Vptr b Ptrofs.zero).
      * eapply eval_Elvalue;[apply eval_Evar_local;exact ArrayLocal|apply deref_loc_reference;reflexivity].
      * reflexivity.
      * eapply eval_Econs;[constructor|reflexivity|].
        eapply eval_Econs with (v1:=Vptr ba Ptrofs.zero).
        -- apply eval_Eaddrof;apply eval_Evar_local;exact ScalarLocal.
        -- reflexivity.
        -- eapply eval_Econs;[constructor|reflexivity|constructor].
    + exact Call.
  - apply exec_Sset;apply eval_Etempvar;apply PTree.gss.
Qed.

Theorem exec_elements_taptweak_generator_wnaf_setup (Model:memset_model) e le m word0 word128 b0 b128 bw0 bw128 :
  NoDup [b0;b128;bw0;bw128] ->
  e!_wnaf_ng_1=Some (bw0,tarray tint 129) -> e!_wnaf_ng_128=Some (bw128,tarray tint 129) ->
  e!_ng_1=Some (b0,Tstruct __5826 noattr) -> e!_ng_128=Some (b128,Tstruct __5826 noattr) ->
  e!_secp256k1_ecmult_wnaf=None -> le!_bits=Some (Vint Int.zero) ->
  scalar_at m b0 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word0))) ->
  scalar_at m b128 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word128))) ->
  Mem.range_perm m bw0 0 516 Cur Freeable -> Mem.range_perm m bw128 0 516 Cur Freeable ->
  exists mf last0 last128 digits0 digits128,
    let lef:=generator_wnaf_setup_temps le (last0+1) (last128+1) in
    Clight2.exec_stmt elements_taptweak_ge e le m generator_wnaf_setup E0 lef mf Out_normal /\
    lef!_bits=Some (Vint (Int.repr (Z.max (last0+1) (last128+1)))) /\
    lef!_bits_ng_1=Some (Vint (Int.repr (last0+1))) /\
    lef!_bits_ng_128=Some (Vint (Int.repr (last128+1))) /\
    (forall id,id<>_bits -> id<>_bits_ng_1 -> id<>_bits_ng_128 -> id<>_t'6 -> id<>_t'7 -> lef!id=le!id) /\
    wnaf_array_state mf bw0 0 129 15 1 129 last0 digits0 /\
    wnaf_array_state mf bw128 0 129 15 1 129 last128 digits128 /\
    Mem.range_perm mf bw0 0 516 Cur Freeable /\ Mem.range_perm mf bw128 0 516 Cur Freeable /\
    lframe (fun b _=>b<>bw0 /\ b<>bw128) m mf /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word0))=
      rev (map (fun i=>digits0 (Z.of_nat i)) (seq 0 129)) /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word128))=
      rev (map (fun i=>digits128 (Z.of_nat i)) (seq 0 129)) /\
    (forall old pos k p,Mem.valid_block m old ->
      (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)) /\
    (forall h,elements_taptweak_generator_table_state h m -> elements_taptweak_generator_table_state h mf) /\readonly_preserved m mf.
Proof.
  intros Sep W0 W128 S0 S128 Symbol Bits Low High Owned0 Owned128.
  pose proof Sep as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
  assert (S0W0:b0<>bw0) by intuition congruence.
  assert (S128W0:b128<>bw0) by intuition congruence.
  assert (S128W128:b128<>bw128) by intuition congruence.
  assert (W0W128:bw0<>bw128) by intuition congruence.
  destruct (exec_elements_taptweak_generator_wnaf_half Model Datatypes.false e le m word0 b0 bw0
    W0 S0 Symbol S0W0 Low Owned0)
    as (ml & last0 & digits0 & LowCall & Array0 & Bound0 & Free0 & Frame0 & Literal0 & Perm0 & Read0).
  set (ll:=generator_wnaf_half_temps Datatypes.false le (last0+1)) in *.
  assert (HighL:scalar_at ml b128 0 (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word128)))).
  { eapply scalar_at_lframe;[exact High|exact Frame0|intros;exact S128W0]. }
  assert (Owned128L:Mem.range_perm ml bw128 0 516 Cur Freeable).
  { eapply curve_keep_free;[lia|exact Owned128|exact Frame0|intros;congruence]. }
  destruct (exec_elements_taptweak_generator_wnaf_half Model Datatypes.true e ll ml word128 b128 bw128
    W128 S128 Symbol S128W128 HighL Owned128L)
    as (mf & last128 & digits128 & HighCall & Array128 & Bound128 & Free128 & Frame128 & Literal128 & Perm128 & Read128).
  set (lh:=generator_wnaf_half_temps Datatypes.true ll (last128+1)) in *.
  assert (Array0F:wnaf_array_state mf bw0 0 129 15 1 129 last0 digits0).
  { eapply wnaf_array_lframe;[exact Array0|exact Frame128|intros;exact W0W128]. }
  assert (Free0F:Mem.range_perm mf bw0 0 516 Cur Freeable).
  { eapply curve_keep_free;[lia|exact Free0|exact Frame128|intros;exact W0W128]. }
  assert (Counts:lh!_bits_ng_1=Some (Vint (Int.repr (last0+1))) /\
    lh!_bits_ng_128=Some (Vint (Int.repr (last128+1))) /\ lh!_bits=Some (Vint Int.zero)).
  { unfold lh,ll;split.
    - rewrite generator_wnaf_half_other by discriminate;apply PTree.gss.
    - split;[apply PTree.gss|].
      rewrite !generator_wnaf_half_other by discriminate;exact Bits. }
  destruct Counts as (Count0 & Count128 & BitsH).
  destruct (exec_elements_taptweak_generator_bits_max e lh mf (last0+1) (last128+1) Bound0 Bound128 BitsH Count0 Count128)
    as (Maximum & MaxBits & Keep).
  assert (Frame:lframe (fun b _=>b<>bw0 /\ b<>bw128) m mf).
  { eapply lframe_trans.
    - eapply lframe_implies;[exact Frame0|intros b pos [Other0 Other128] Valid;exact Other0].
    - eapply lframe_implies;[exact Frame128|intros b pos [Other0 Other128] Valid;exact Other128]. }
  assert (Perms:forall old pos k p,Mem.valid_block m old ->
    (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
  { intros old pos k p Valid.
    rewrite (Perm128 old pos k p (proj2 (proj2 Frame0) old Valid));apply Perm0;exact Valid. }
  assert (Tables:forall h,elements_taptweak_generator_table_state h m -> elements_taptweak_generator_table_state h mf).
  { intros h [Table Readonly];pose proof Table as [Valid _].
    assert (Outside:elements_taptweak_generator_table_block h<>bw0 /\ elements_taptweak_generator_table_block h<>bw128).
    { split;intro Same;rewrite Same in Readonly.
      - destruct (proj1 (Readonly 0 Cur Freeable) (Owned0 0 ltac:(lia))) as [_ Order];inversion Order.
      - destruct (proj1 (Readonly 0 Cur Freeable) (Owned128 0 ltac:(lia))) as [_ Order];inversion Order. }
    split.
    - eapply elements_taptweak_generator_table_rep_lframe;[exact Table|exact Frame|intros;exact Outside].
    - intros pos k p;rewrite (Perms _ pos k p Valid);apply Readonly. }
  exists mf,last0,last128,digits0,digits128;cbn zeta;split.
  - rewrite generator_wnaf_setup_source.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ll) (m1:=ml);[exact LowCall|].
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lh) (m1:=mf);[exact HighCall|exact Maximum].
  - split;[exact MaxBits|];split.
    + unfold generator_wnaf_setup_temps;rewrite Keep by discriminate;exact Count0.
    + split.
      * unfold generator_wnaf_setup_temps;rewrite Keep by discriminate;exact Count128.
      * split.
        -- intros id NotBits Not0 Not128 Not6 Not7;unfold generator_wnaf_setup_temps.
           rewrite Keep by exact NotBits;unfold lh,ll.
           rewrite !generator_wnaf_half_other by assumption;reflexivity.
        -- split;[exact Array0F|];split;[exact Array128|];split;[exact Free0F|];
           split;[exact Free128|];split;[exact Frame|];split;[exact Literal0|];split;[exact Literal128|];
           split;[exact Perms|];split;[exact Tables|eapply preserved_trans;[exact Read0|exact Read128]].
Qed.
