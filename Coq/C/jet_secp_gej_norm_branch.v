(** Original gej_normalize caller test/tag and infinity branch. The finite
    branch still needs the complete inversion call; it is not assumed here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine.
Require Simplicity.Alg Simplicity.Bit Simplicity.Translate.
Require Import C.jet_exec C.jet_readBit_layout C.jet_output_layout C.jet_frame_inv C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_curve_statements C.jet_secp_gej_public_entry C.jet_secp_gej_predicate_body.
Require Import C.jet_secp_gej_flag_read C.jet_secp_odd_body C.jet_secp_bit_writer C.jet_secp_affine_skip.
Require Import C.jet_secp_gej_norm_literal C.jet_secp_canonical_zero C.jet_secp_literal_gej_predicate.
Require C.jets.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge canonical_fe_is_zero literal_gej_norm Simplicity.Translate.encode.

(** Literal translation of LibSecp256k1.hs lines 554--555, not a new target. *)
Definition literal_gej_normalize {term:Alg.Core.Algebra} :
  Alg.Core.domain term (Ty.Prod (Ty.Prod Word256 Word256) Word256) (Ty.Sum Ty.Unit (Ty.Prod Word256 Word256)) :=
  Alg.Core.Combinators.comp
    (Alg.Core.Combinators.pair (Alg.Core.Combinators.drop (@canonical_fe_is_zero term)) Alg.Core.Combinators.iden)
    (Bit.cond (Alg.Core.Combinators.injl Alg.Core.Combinators.unit)
      (Alg.Core.Combinators.injr (@literal_gej_norm term))).
Lemma literal_gej_normalize_value (x y z:Ty.tySem Word256) :
  @literal_gej_normalize Alg.CoreFunSem ((x,y),z)=
    if Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z)
    then inl tt else inr(@literal_gej_norm Alg.CoreFunSem ((x,y),z)).
Proof.
  unfold literal_gej_normalize.
  change ((match @canonical_fe_is_zero Alg.CoreFunSem z with
    | inl _=>inr(@literal_gej_norm Alg.CoreFunSem ((x,y),z)) | inr _=>inl tt end)=
    if Bit.toBool(@canonical_fe_is_zero Alg.CoreFunSem z) then inl tt
    else inr(@literal_gej_norm Alg.CoreFunSem ((x,y),z))).
  destruct (@canonical_fe_is_zero Alg.CoreFunSem z) as [[]|[]];reflexivity.
Qed.
Lemma literal_gej_normalize_parametric : Alg.Core.Parametric (@literal_gej_normalize).
Proof.
  intros t1 t2 R;unfold literal_gej_normalize;apply Alg.comp_Parametric.
  - apply Alg.pair_Parametric.
    + apply Alg.drop_Parametric;apply canonical_fe_is_zero_parametric.
    + apply Alg.iden_Parametric.
  - apply Bit.cond_Parametric.
    + apply Alg.injl_Parametric;apply Alg.unit_Parametric.
    + apply Alg.injr_Parametric;apply literal_gej_norm_parametric.
Qed.

Definition gej_norm_env bl bp br := PTree.set _r (br,Tstruct __6121 noattr) (gej_public_env bl bp).
Definition gej_norm_tag_stmt := Scall (Some _t'2)
  (Evar _writeBit (type_of_function C.jets.f_writeBit))
  [Etempvar _dst (tptr(Tstruct _frameItem noattr));Eunop Onotbool (Etempvar _t'1 tint) tint].
Definition gej_norm_header := Ssequence gej_predicate_flag_stmt gej_norm_tag_stmt.
Definition gej_norm_affine_stmt := Scall None
  (Evar _secp256k1_ge_set_gej_var (type_of_function f_secp256k1_ge_set_gej_var))
  [Eaddrof(Evar _r (Tstruct __6121 noattr))(tptr(Tstruct __6121 noattr));
   Eaddrof(Evar _a (Tstruct __6123 noattr))(tptr(Tstruct __6123 noattr))].
Definition gej_norm_payload_stmt := Scall None (Evar _write_ge (type_of_function f_write_ge))
  [Etempvar _dst (tptr(Tstruct _frameItem noattr));
   Eaddrof(Evar _r (Tstruct __6121 noattr))(tptr(Tstruct __6121 noattr))].
Definition gej_norm_skip_stmt := Scall None (Evar _skip_ge (type_of_function f_skip_ge))
  [Etempvar _dst (tptr(Tstruct _frameItem noattr))].
Definition gej_norm_branch := Sifthenelse (Etempvar _t'2 tbool)
  (Ssequence gej_norm_affine_stmt gej_norm_payload_stmt) gej_norm_skip_stmt.
Definition gej_norm_after_read := Ssequence (Ssequence gej_norm_header gej_norm_branch)
  (Sreturn(Some(Econst_int Int.one tint))).
Definition gej_norm_tagged le (infinity:bool) := PTree.set _t'2 (Vint(bit_int(negb infinity)))
  (PTree.set _t'1 (Vint(bit_int infinity)) le).
Lemma gej_norm_body_source : fn_body f_simplicity_gej_normalize=
  Ssequence (Sassign(Evar _src (Tstruct _frameItem noattr))(Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence gej_predicate_read_stmt gej_norm_after_read).
Proof. reflexivity. Qed.

Local Transparent secp_ge.
Lemma gej_norm_skip_link : Genv.find_symbol secp_ge _skip_ge=Some(secp_symbol_block _skip_ge) /\
  Genv.find_funct secp_ge (Vptr(secp_symbol_block _skip_ge) Ptrofs.zero)=Some(Internal f_skip_ge).
Proof. split;reflexivity. Qed.
Local Opaque secp_ge.

Lemma exec_gej_norm_flag le m bl bp br flag :
  Mem.load Mint32 m bp 120=Some(Vint flag) ->
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m gej_predicate_flag_stmt E0
    (PTree.set _t'1 (Vint flag) le) m Out_normal.
Proof.
  intro Load.
  change (Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m
    (curve_call _secp256k1_gej_is_infinity f_secp256k1_gej_is_infinity (Some _t'1)
      [Eaddrof(Evar _a (Tstruct __6123 noattr))(tptr(Tstruct __6123 noattr))]) E0
    (set_opttemp (Some _t'1) (Vint flag) le) m Out_normal).
  eapply exec_curve_call with (vargs:=[Vptr bp Ptrofs.zero]) (v:=Vint flag).
  - unfold secp_pure;repeat (first[left;reflexivity|right]).
  - reflexivity.
  - eapply eval_Econs;[apply eval_Eaddrof;apply eval_Evar_local;reflexivity|reflexivity|constructor].
  - apply (eval_gej_flag_accessor m bp 0 flag);[lia|change(128<=18446744073709551615);lia|exact Load].
Qed.

Lemma exec_gej_norm_tag le m mf bl bp br bd base (infinity:bool) :
  le!_dst=Some(Vptr bd (Ptrofs.repr base)) ->
  le!_t'1=Some(Vint(bit_int infinity)) ->
  Clight2.eval_funcall secp_ge m (Internal C.jets.f_writeBit)
    [Vptr bd (Ptrofs.repr base);Vint(bit_int(negb infinity))] E0 mf (Vint(bit_int(negb infinity))) ->
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m gej_norm_tag_stmt E0
    (PTree.set _t'2 (Vint(bit_int(negb infinity))) le) mf Out_normal.
Proof.
  intros Dst Flag Write;destruct secp_odd_helper_symbols as (_ & _ & Symbol & Funct).
  unfold gej_norm_tag_stmt;eapply exec_Scall with
    (vf:=Vptr(secp_symbol_block _writeBit) Ptrofs.zero)
    (vargs:=[Vptr bd (Ptrofs.repr base);Vint(bit_int(negb infinity))])
    (f:=Internal C.jets.f_writeBit) (vres:=Vint(bit_int(negb infinity))).
  - reflexivity.
  - eapply eval_Elvalue;[eapply eval_Evar_global;[reflexivity|exact Symbol]|apply deref_loc_reference;reflexivity].
  - eapply eval_Econs;[apply eval_Etempvar;exact Dst|reflexivity|].
    eapply eval_Econs.
    + eapply eval_Eunop;[apply eval_Etempvar;exact Flag|destruct infinity;reflexivity].
    + destruct infinity;reflexivity.
    + constructor.
  - exact Funct.
  - reflexivity.
  - exact Write.
Qed.

Theorem exec_gej_norm_header m0 bd base bw edge cursor N bi le m bl bp br (infinity:bool) :
  le!_dst=Some(Vptr bd (Ptrofs.repr base)) -> write_frame_at m0 bd base bw edge cursor N -> 1<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  Mem.load Mint32 m bp 120=Some(Vint(bit_int infinity)) -> exists mt,
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m gej_norm_header E0
    (gej_norm_tagged le infinity) mt Out_normal /\
  finv m0 bd base bw edge cursor N bi mt true [Some(negb infinity)] /\
  lframe (fun b _=>b<>bd /\ b<>bw) m mt /\
  (forall b ofs k p,Mem.perm m b ofs k p -> Mem.perm mt b ofs k p).
Proof.
  intros Dst Output Cap Inv Flag.
  destruct (eval_secp_writeBit_from_invariant m0 bd base bw edge cursor N bi m (negb infinity)
    Output Cap Inv) as (mt & Write & Final & Frame & Perm).
  exists mt;split.
  - unfold gej_norm_header,gej_norm_tagged.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _t'1 (Vint(bit_int infinity)) le).
    + apply exec_gej_norm_flag;exact Flag.
    + apply (exec_gej_norm_tag _ _ _ bl bp br bd base infinity).
      * rewrite PTree.gso by discriminate;exact Dst.
      * apply PTree.gss.
      * exact Write.
  - split;[exact Final|];split;assumption.
Qed.

Theorem exec_gej_norm_infinity_after_read m0 bd base bw edge cursor N bi le m bl bp br :
  le!_dst=Some(Vptr bd (Ptrofs.repr base)) -> write_frame_at m0 bd base bw edge cursor N -> 513<=N ->
  finv m0 bd base bw edge cursor N bi m false [] ->
  Mem.load Mint32 m bp 120=Some(Vint Int.one) -> exists mf,
  Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) le m gej_norm_after_read E0
    (gej_norm_tagged le true) mf (Out_return(Some(Vint Int.one,tint))) /\
  finv m0 bd base bw edge cursor N bi mf true ([Some false]++repeat None 512) /\
  lframe (fun b _=>b<>bd /\ b<>bw) m mf.
Proof.
  intros Dst Output Cap Inv Flag.
  destruct (exec_gej_norm_header m0 bd base bw edge cursor N bi le m bl bp br true
    Dst Output ltac:(lia) Inv Flag) as (mt & Header & Prefix & FrameT & PermT).
  destruct (eval_secp_skip_ge_from_prefix m0 bd base bw edge cursor N bi true [Some false] mt
    Output ltac:(cbn;lia) Prefix) as (mf & Skip & Final & FrameP).
  assert (Skipped:Clight2.exec_stmt secp_ge (gej_norm_env bl bp br) (gej_norm_tagged le true)
    mt gej_norm_skip_stmt E0 (gej_norm_tagged le true) mf Out_normal).
  { unfold gej_norm_skip_stmt.
    eapply exec_Scall with (vf:=Vptr(secp_symbol_block _skip_ge) Ptrofs.zero)
      (f:=Internal f_skip_ge) (vargs:=[Vptr bd (Ptrofs.repr base)]) (vres:=Vundef).
    - reflexivity.
    - eapply eval_Elvalue.
      + eapply eval_Evar_global;[reflexivity|exact(proj1 gej_norm_skip_link)].
      + apply deref_loc_reference;reflexivity.
    - eapply eval_Econs.
      + apply eval_Etempvar;unfold gej_norm_tagged;rewrite !PTree.gso by discriminate;exact Dst.
      + reflexivity.
      + constructor.
    - exact(proj2 gej_norm_skip_link).
    - reflexivity.
    - exact Skip. }
  exists mf;split.
  - unfold gej_norm_after_read.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=gej_norm_tagged le true).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mt) (le1:=gej_norm_tagged le true);[exact Header|].
      unfold gej_norm_branch;eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
      * apply eval_Etempvar;unfold gej_norm_tagged;apply PTree.gss.
      * reflexivity.
      * exact Skipped.
    + apply exec_Sreturn_some;constructor.
  - split;[exact Final|].
    eapply lframe_trans;[exact FrameT|];eapply lframe_implies;[exact FrameP|].
    intros b pos [ND NW] Valid;exact ND.
Qed.
