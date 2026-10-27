(** Original zero-scalar or infinity preprocessing; unused tables are not read. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns
 C.jet_secp_curve_statements C.jet_secp_strauss_first_loop C.jet_secp_generator_preprocess
 C.jet_secp_generator_globalz_call C.jet_secp_generator_initialize C.jet_secp_gej_flag_read
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_clight_internal_permissions C.jet_clight_internal_preserve.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition strauss_infinite_checked_temps le := PTree.set _t'2 (Vint Int.one)
 (PTree.set _t'3 (Vint Int.one) (PTree.set _t'1 (Vint Int.zero) le)).

Theorem exec_strauss_check_infinite e le m value bk ba :
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_gej_is_infinity=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_np=Some (Vlong Int64.zero) -> 0<=value<2^256 -> value<>0 ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of value)) ->
 Mem.load Mint32 m ba 120=Some (Vint Int.one) ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_check E0 (strauss_infinite_checked_temps le) m Out_continue.
Proof.
 intros ScalarSymbol FlagSymbol NA A NP Range Nonzero Input Flag.
 pose proof (eval_strauss_scalar_zero value m bk Range Input) as Scalar.
 rewrite (proj2 (Z.eqb_neq value 0) Nonzero) in Scalar.
 pose proof (eval_gej_flag_accessor m ba 0 Int.one ltac:(clear;lia)
  ltac:(change Ptrofs.max_unsigned with 18446744073709551615;clear;lia) Flag) as Infinity.
 pose (ls:=PTree.set _t'1 (Vint Int.zero) le).
 pose (lf:=PTree.set _t'3 (Vint Int.one) ls).
 rewrite generator_preprocess_check_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=strauss_infinite_checked_temps le) (m1:=m).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=ls) (m1:=m).
   + unfold generator_preprocess_scalar_call;eapply exec_curve_call with
      (vargs:=[Vptr bk Ptrofs.zero]) (v:=Vint Int.zero).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact ScalarSymbol.
     * eapply eval_Econs with (v1:=Vptr bk Ptrofs.zero);[|reflexivity|constructor].
       eapply eval_Ebinop with (v1:=Vptr bk Ptrofs.zero) (v2:=Vlong Int64.zero);
        [apply eval_Etempvar;exact NA|apply eval_Etempvar;exact NP|reflexivity].
     * exact Scalar.
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=Datatypes.false);
      [apply eval_Etempvar;unfold ls;apply PTree.gss|reflexivity|].
     rewrite strauss_other_flag_source.
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=lf) (m1:=m).
     * eapply exec_curve_call with (vargs:=[Vptr ba Ptrofs.zero]) (v:=Vint Int.one).
       -- unfold secp_pure;repeat first [left;reflexivity|right].
       -- exact FlagSymbol.
       -- eapply eval_Econs with (v1:=Vptr ba Ptrofs.zero);[|reflexivity|constructor].
          eapply eval_Ebinop with (v1:=Vptr ba Ptrofs.zero) (v2:=Vlong Int64.zero).
          ++ apply eval_Etempvar;unfold ls;rewrite PTree.gso by discriminate;exact A.
          ++ apply eval_Etempvar;unfold ls;rewrite PTree.gso by discriminate;exact NP.
          ++ reflexivity.
       -- exact Infinity.
     * apply exec_Sset;eapply eval_Ecast;[apply eval_Etempvar;unfold lf;apply PTree.gss|reflexivity].
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=Datatypes.true);
    [apply eval_Etempvar;unfold strauss_infinite_checked_temps;apply PTree.gss|reflexivity|constructor].
Qed.

Definition strauss_skipped_preprocessed_temps le value :=
 if value =? 0 then generator_preprocessed_temps le else
  PTree.set _np (Vlong Int64.one)
   (strauss_infinite_checked_temps (PTree.set _np (Vlong Int64.zero) le)).

Lemma strauss_skipped_preserves le value id : ~In id [_np;_t'1;_t'2;_t'3] ->
 (strauss_skipped_preprocessed_temps le value)!id=le!id.
Proof.
 intro Outside;unfold strauss_skipped_preprocessed_temps;destruct (value =? 0).
 - apply generator_preprocessed_preserves;cbn [In] in Outside;intuition congruence.
 - unfold strauss_infinite_checked_temps;rewrite !PTree.gso;cbn [In] in Outside;intuition congruence.
Qed.
Lemma strauss_skipped_np le value :
 (strauss_skipped_preprocessed_temps le value)!_np=Some (Vlong Int64.one).
Proof.
 unfold strauss_skipped_preprocessed_temps;destruct (value =? 0);
  [unfold generator_preprocessed_temps|];apply PTree.gss.
Qed.

Lemma exec_strauss_skip_loop e le m lc :
 le!_num=Some (Vlong Int64.one) ->
 Clight2.exec_stmt secp_ge e (PTree.set _np (Vlong Int64.zero) le) m generator_preprocess_check E0 lc m Out_continue ->
 lc!_np=Some (Vlong Int64.zero) -> lc!_num=Some (Vlong Int64.one) ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_statement E0
  (PTree.set _np (Vlong Int64.one) lc) m Out_normal.
Proof.
 intros Num Check NP1 Num1;pose (l0:=PTree.set _np (Vlong Int64.zero) le).
 rewrite generator_preprocess_statement_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m).
 - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
 - rewrite generator_preprocess_loop_source.
   eapply exec_Sloop_loop with (t1:=E0) (t2:=E0) (t3:=E0) (out1:=Out_continue)
    (le1:=lc) (m1:=m) (le2:=PTree.set _np (Vlong Int64.one) lc) (m2:=m).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=l0) (m1:=m).
     * eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=Datatypes.true);[|reflexivity|constructor].
       eapply eval_Ebinop.
       -- apply eval_Etempvar;unfold l0;apply PTree.gss.
       -- apply eval_Etempvar;unfold l0;rewrite PTree.gso by discriminate;exact Num.
       -- reflexivity.
     * rewrite generator_preprocess_work_source;eapply exec_Sseq_2;[exact Check|discriminate].
   + constructor.
   + apply exec_Sset;eapply eval_Ebinop;[apply eval_Etempvar;exact NP1|constructor|reflexivity].
   + eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
     eapply exec_Sseq_2;[|discriminate].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=Datatypes.false);[|reflexivity|constructor].
     eapply eval_Ebinop with (v1:=Vlong Int64.one) (v2:=Vlong Int64.one);
      [apply eval_Etempvar;apply PTree.gss| |reflexivity].
     apply eval_Etempvar;rewrite PTree.gso by discriminate;exact Num1.
Qed.

Theorem exec_strauss_preprocess_skips e le m value bk ba :
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_gej_is_infinity=None ->
 le!_na=Some (Vptr bk Ptrofs.zero) -> le!_a=Some (Vptr ba Ptrofs.zero) ->
 le!_num=Some (Vlong Int64.one) -> 0<=value<2^256 ->
 scalar_at m bk 0 (map Int64.repr (scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Clight2.exec_stmt secp_ge e le m generator_preprocess_statement E0
  (strauss_skipped_preprocessed_temps le value) m Out_normal.
Proof.
 intros ZeroSymbol FlagSymbol NA A Num Range Input Skip.
 unfold strauss_skipped_preprocessed_temps;destruct (Z.eqb_spec value 0) as [Zero|Nonzero].
 - subst value;apply (exec_generator_preprocess_zero e le m bk 0 ZeroSymbol NA Num);exact Input.
 - apply (exec_strauss_skip_loop e le m);[exact Num| | |].
   + apply (exec_strauss_check_infinite e (PTree.set _np (Vlong Int64.zero) le) m value bk ba).
     * exact ZeroSymbol.
     * exact FlagSymbol.
     * rewrite PTree.gso by discriminate;exact NA.
     * rewrite PTree.gso by discriminate;exact A.
     * apply PTree.gss.
     * exact Range.
     * exact Nonzero.
     * exact Input.
     * destruct Skip as [Zero|Flag];[contradiction|exact Flag].
   + unfold strauss_infinite_checked_temps;rewrite !PTree.gso by discriminate;apply PTree.gss.
   + unfold strauss_infinite_checked_temps;rewrite !PTree.gso by discriminate;exact Num.
Qed.

Definition strauss_no_points_temps le value aptr zrptr :=
 PTree.set _np (Vlong Int64.zero)
  (generator_globalz_call_temps (strauss_skipped_preprocessed_temps le value) aptr zrptr).
Lemma strauss_no_points_preserves le value aptr zrptr id : ~In id [_np;_t'1;_t'2;_t'3;_t'32;_t'33] ->
 (strauss_no_points_temps le value aptr zrptr)!id=le!id.
Proof.
 intro Outside;unfold strauss_no_points_temps,generator_globalz_call_temps.
 rewrite !PTree.gso by (clear -Outside;cbn [In] in Outside;intuition congruence).
 apply strauss_skipped_preserves;cbn [In] in Outside|-*;tauto.
Qed.

Theorem exec_strauss_no_points e le m value bk ba bs bt bx :
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_gej_is_infinity=None ->
 e!_secp256k1_ge_table_set_globalz=None -> le!_na=Some (Vptr bk Ptrofs.zero) ->
 le!_a=Some (Vptr ba Ptrofs.zero) -> le!_num=Some (Vlong Int64.one) ->
 le!_no=Some (Vlong Int64.zero) -> le!_state=Some (Vptr bs Ptrofs.zero) ->
 0<=value<2^256 -> scalar_at m bk 0 (map Int64.repr (scalar_limbs_of value)) ->
 (value=0 \/ Mem.load Mint32 m ba 120=Some (Vint Int.one)) ->
 Mem.load Mptr m bs 8=Some (Vptr bt Ptrofs.zero) -> Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
 exists mf,
 Clight2.exec_stmt secp_ge e le m generator_no_points_phase E0
  (strauss_no_points_temps le value (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)) mf Out_normal /\
 (strauss_no_points_temps le value (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero))!_np=Some (Vlong Int64.zero) /\
 (strauss_no_points_temps le value (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero))!_no=Some (Vlong Int64.zero) /\
 (forall id,~In id [_np;_t'1;_t'2;_t'3;_t'32;_t'33] ->
  (strauss_no_points_temps le value (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero))!id=le!id) /\
 Mem.unchanged_on (fun _ _=>True) m mf /\ lframe (fun _ _=>True) m mf /\
 keeps_permissions m mf /\ readonly_preserved m mf.
Proof.
 intros ZeroSymbol FlagSymbol GlobalSymbol NA A Num No State Range Input Skip PT PX.
 pose proof (exec_strauss_preprocess_skips e le m value bk ba ZeroSymbol FlagSymbol NA A Num Range Input Skip) as Preprocess.
 pose (lp:=strauss_skipped_preprocessed_temps le value).
 assert (NoP:lp!_no=Some (Vlong Int64.zero)).
 { unfold lp;rewrite strauss_skipped_preserves by (clear;cbn [In];intuition discriminate);exact No. }
 assert (StateP:lp!_state=Some (Vptr bs Ptrofs.zero)).
 { unfold lp;rewrite strauss_skipped_preserves by (clear;cbn [In];intuition discriminate);exact State. }
 destruct (exec_generator_globalz_empty e lp m bs 0 bt Ptrofs.zero bx Ptrofs.zero GlobalSymbol StateP NoP
  ltac:(clear;lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615;clear;lia) PT PX)
  as (mf & Global & Unchanged).
 pose (lc:=generator_globalz_call_temps lp (Vptr bt Ptrofs.zero) (Vptr bx Ptrofs.zero)).
 assert (NoC:lc!_no=Some (Vlong Int64.zero)).
 { unfold lc,generator_globalz_call_temps;rewrite !PTree.gso by discriminate;exact NoP. }
 exists mf;split.
 - rewrite generator_no_points_source;unfold strauss_no_points_temps.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Preprocess|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Global|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact (exec_generator_auxiliary_empty e lc mf NoC)|constructor].
 - split;[unfold strauss_no_points_temps;apply PTree.gss|];split.
   + unfold strauss_no_points_temps;rewrite PTree.gso by discriminate;exact NoC.
   + split;[intros;apply strauss_no_points_preserves;assumption|];split;[exact Unchanged|];split.
     * apply lframe_unchanged;exact Unchanged.
     * split.
       -- intros b pos k p Perm;eapply Mem.perm_unchanged_on;[exact Unchanged|exact I|exact Perm].
       -- apply generator_unchanged_preserved;exact Unchanged.
Qed.
