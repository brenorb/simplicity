(** Original global-Z setup call and skipped auxiliary loop for generate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Errors.
Require Import C.jet_sx_eval C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_statement_prefix C.jet_secp_curve_statements C.jet_secp_generator_globalz_empty.
Require Import C.jet_secp_generator_preprocess C.jet_secp_scalar_get_b32_storage.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque secp_ge.
Set Default Timeout 10.

Definition generator_globalz_statement := nth 6
 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip.
Definition generator_auxiliary_statement := nth 7
 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))) Sskip.
Definition generator_auxiliary_body := match generator_auxiliary_statement with
 | Ssequence _ (Sloop (Ssequence _ body) _)=>body | _=>Sskip end.
Definition generator_state_pointer field ty := Efield
 (Ederef (Etempvar _state (tptr (Tstruct _secp256k1_strauss_state noattr)))
  (Tstruct _secp256k1_strauss_state noattr)) field (tptr ty).
Definition generator_globalz_count := Ebinop Omul
 (Ebinop Oshl (Econst_long Int64.one tlong)
  (Ebinop Osub (Econst_int (Int.repr 5) tint) (Econst_int (Int.repr 2) tint) tint) tlong)
 (Etempvar _no tulong) tulong.
Definition generator_globalz_call_temps (le : temp_env) (aptr zrptr : val) :=
 PTree.set _t'33 zrptr (PTree.set _t'32 aptr le).

Lemma generator_globalz_statement_source : generator_globalz_statement=
 Ssequence (Sset _t'32 (generator_state_pointer _pre_a (Tstruct __6121 noattr)))
  (Ssequence (Sset _t'33 (generator_state_pointer _aux (Tstruct __5467 noattr)))
   (curve_call _secp256k1_ge_table_set_globalz f_secp256k1_ge_table_set_globalz None
    [generator_globalz_count;Etempvar _t'32 (tptr (Tstruct __6121 noattr));
     Etempvar _t'33 (tptr (Tstruct __5467 noattr))])).
Proof. reflexivity. Qed.
Lemma generator_auxiliary_statement_source : generator_auxiliary_statement=
 Ssequence (Sset _np (Ecast (Econst_int Int.zero tint) tulong))
  (Sloop (Ssequence (Sifthenelse
    (Ebinop Olt (Etempvar _np tulong) (Etempvar _no tulong) tint) Sskip Sbreak)
    generator_auxiliary_body)
   (Sset _np (Ebinop Oadd (Etempvar _np tulong) (Econst_int Int.one tint) tulong))).
Proof. reflexivity. Qed.

Lemma generator_strauss_field field delta : In (field,delta) [(_pre_a,8);(_aux,0)] ->
 exists co, (genv_cenv secp_ge)!_secp256k1_strauss_state=Some co /\
 field_offset secp_ge field (co_members co)=OK (delta,Full).
Proof.
 intro Field.
 assert (View:option_map co_members ((genv_cenv secp_ge)!_secp256k1_strauss_state)=
  Some [Member_plain _aux (tptr (Tstruct __5467 noattr));
        Member_plain _pre_a (tptr (Tstruct __6121 noattr));
        Member_plain _ps (tptr (Tstruct _secp256k1_strauss_point_state noattr))]) by (vm_compute;reflexivity).
 destruct ((genv_cenv secp_ge)!_secp256k1_strauss_state) as [co|] eqn:Lookup;[|discriminate].
 exists co;split;[reflexivity|];inversion View as [Members];rewrite Members.
 destruct Field as [Eq | [Eq | Eq]];try contradiction;inversion Eq;subst;reflexivity.
Qed.

Lemma eval_generator_state_pointer e le m b base field delta ty v :
 In (field,delta) [(_pre_a,8);(_aux,0)] ->
 le!_state=Some (Vptr b (Ptrofs.repr base)) -> 0<=base -> base+24<=Ptrofs.max_unsigned ->
 Mem.load Mptr m b (base+delta)=Some v ->
 eval_expr secp_ge e le m (generator_state_pointer field ty) v.
Proof.
 intros Field State Base Hi Load;destruct (generator_strauss_field field delta Field) as (co & Lookup & Offset).
 assert (Range:0<=delta<=8) by (destruct Field as [Eq | [Eq | Eq]];[inversion Eq|inversion Eq|contradiction];lia).
 unfold generator_state_pointer;eapply eval_Elvalue.
 - eapply eval_Efield_struct with (co:=co) (delta:=delta).
   + eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact State|].
     apply deref_loc_copy;reflexivity.
   + reflexivity.
   + exact Lookup.
   + exact Offset.
 - eapply deref_loc_value with (chunk:=Mptr);[reflexivity|].
   rewrite <- (Z.add_0_r base) at 1;rewrite ptr_add_repr1.
   cbn [Mem.loadv];rewrite Ptrofs.unsigned_repr by lia;rewrite Z.add_0_l;exact Load.
Qed.

Lemma eval_generator_globalz_count e le m : le!_no=Some (Vlong Int64.zero) ->
 eval_expr secp_ge e le m generator_globalz_count (Vlong Int64.zero).
Proof.
 intro No;unfold generator_globalz_count.
 eapply eval_Ebinop with (v1:=Vlong (Int64.repr 8)) (v2:=Vlong Int64.zero).
 - eapply eval_Ebinop with (v1:=Vlong Int64.one) (v2:=Vint (Int.repr 3)).
   + constructor.
   + eapply eval_Ebinop;[constructor|constructor|reflexivity].
   + reflexivity.
 - apply eval_Etempvar;exact No.
 - reflexivity.
Qed.

Theorem exec_generator_globalz_empty e le m bs base ba aofs bz zofs :
 e!_secp256k1_ge_table_set_globalz=None ->
 le!_state=Some (Vptr bs (Ptrofs.repr base)) -> le!_no=Some (Vlong Int64.zero) ->
 0<=base -> base+24<=Ptrofs.max_unsigned ->
 Mem.load Mptr m bs (base+8)=Some (Vptr ba aofs) ->
 Mem.load Mptr m bs (base+0)=Some (Vptr bz zofs) -> exists mf,
 Clight2.exec_stmt secp_ge e le m generator_globalz_statement E0
  (generator_globalz_call_temps le (Vptr ba aofs) (Vptr bz zofs)) mf Out_normal /\
 Mem.unchanged_on (fun _ _=>True) m mf.
Proof.
 intros Symbol State No Base Hi A Zr.
 destruct (eval_ge_table_set_globalz_empty m (Vptr ba aofs) (Vptr bz zofs)) as (mf & Call & Unchanged).
 exists mf;split;[|exact Unchanged];rewrite generator_globalz_statement_source.
 set (la:=PTree.set _t'32 (Vptr ba aofs) le).
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=la).
 - apply exec_Sset;eapply eval_generator_state_pointer;[left;reflexivity|exact State|exact Base|exact Hi|exact A].
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=generator_globalz_call_temps le (Vptr ba aofs) (Vptr bz zofs)).
   + apply exec_Sset;eapply eval_generator_state_pointer.
     * right;left;reflexivity.
     * unfold la;rewrite PTree.gso by discriminate;exact State.
     * exact Base.
     * exact Hi.
     * exact Zr.
   + eapply exec_curve_call with (vargs:=[Vlong Int64.zero;Vptr ba aofs;Vptr bz zofs]) (v:=Vundef).
     * unfold secp_pure;repeat first [left;reflexivity|right].
     * exact Symbol.
     * eapply eval_Econs with (v1:=Vlong Int64.zero).
       -- apply eval_generator_globalz_count;unfold generator_globalz_call_temps.
          rewrite PTree.gso by discriminate;rewrite PTree.gso by discriminate;exact No.
       -- reflexivity.
       -- eapply eval_Econs with (v1:=Vptr ba aofs).
          ++ apply eval_Etempvar;unfold generator_globalz_call_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
          ++ reflexivity.
          ++ eapply eval_Econs;[apply eval_Etempvar;unfold generator_globalz_call_temps;apply PTree.gss|reflexivity|constructor].
     * exact Call.
Qed.

Theorem exec_generator_auxiliary_empty e le m : le!_no=Some (Vlong Int64.zero) ->
 Clight2.exec_stmt secp_ge e le m generator_auxiliary_statement E0
  (PTree.set _np (Vlong Int64.zero) le) m Out_normal.
Proof.
 intro No;rewrite generator_auxiliary_statement_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _np (Vlong Int64.zero) le).
 - apply exec_Sset;eapply eval_Ecast;[constructor|reflexivity].
 - eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
   eapply exec_Sseq_2;[|discriminate].
   eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[|reflexivity|constructor].
   eapply eval_Ebinop.
   + apply eval_Etempvar;apply PTree.gss.
   + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact No.
   + reflexivity.
Qed.

Definition generator_no_points_phase := statement_sequence
 (firstn 3 (skipn 5 (fst (split_statement_last (fn_body f_secp256k1_ecmult_strauss_wnaf))))) Sskip.
Definition generator_no_points_temps le aptr zrptr :=
 PTree.set _np (Vlong Int64.zero)
  (generator_globalz_call_temps (generator_preprocessed_temps le) aptr zrptr).
Lemma generator_no_points_source : generator_no_points_phase=
 Ssequence generator_preprocess_statement
  (Ssequence generator_globalz_statement (Ssequence generator_auxiliary_statement Sskip)).
Proof. reflexivity. Qed.

Lemma generator_no_points_preserves le aptr zrptr id :
 id<>_np -> id<>_t'1 -> id<>_t'2 -> id<>_t'32 -> id<>_t'33 ->
 (generator_no_points_temps le aptr zrptr)!id=le!id.
Proof.
 intros NP T1 T2 T32 T33;unfold generator_no_points_temps,generator_globalz_call_temps.
 rewrite PTree.gso by exact NP;rewrite PTree.gso by exact T33;rewrite PTree.gso by exact T32.
 apply generator_preprocessed_preserves;assumption.
Qed.

Theorem exec_generator_no_points e le m bn nofs bs base ba aofs bz zofs :
 e!_secp256k1_scalar_is_zero=None -> e!_secp256k1_ge_table_set_globalz=None ->
 le!_na=Some (Vptr bn (Ptrofs.repr nofs)) -> le!_num=Some (Vlong Int64.one) ->
 le!_no=Some (Vlong Int64.zero) -> le!_state=Some (Vptr bs (Ptrofs.repr base)) ->
 scalar_at m bn nofs [Int64.zero;Int64.zero;Int64.zero;Int64.zero] ->
 0<=base -> base+24<=Ptrofs.max_unsigned ->
 Mem.load Mptr m bs (base+8)=Some (Vptr ba aofs) ->
 Mem.load Mptr m bs (base+0)=Some (Vptr bz zofs) -> exists mf,
 Clight2.exec_stmt secp_ge e le m generator_no_points_phase E0
  (generator_no_points_temps le (Vptr ba aofs) (Vptr bz zofs)) mf Out_normal /\
 Mem.unchanged_on (fun _ _=>True) m mf.
Proof.
 intros ZeroSymbol GlobalSymbol NA Num No State Scalar Base Hi A Zr.
 pose proof (exec_generator_preprocess_zero e le m bn nofs ZeroSymbol NA Num Scalar) as Preprocess.
 set (lp:=generator_preprocessed_temps le).
 assert (NoP:lp!_no=Some (Vlong Int64.zero)).
 { unfold lp;rewrite generator_preprocessed_preserves by discriminate;exact No. }
 assert (StateP:lp!_state=Some (Vptr bs (Ptrofs.repr base))).
 { unfold lp;rewrite generator_preprocessed_preserves by discriminate;exact State. }
 destruct (exec_generator_globalz_empty e lp m bs base ba aofs bz zofs GlobalSymbol StateP NoP Base Hi A Zr)
  as (mf & Global & Unchanged).
 set (lc:=generator_globalz_call_temps lp (Vptr ba aofs) (Vptr bz zofs)).
 assert (NoC:lc!_no=Some (Vlong Int64.zero)).
 { unfold lc,generator_globalz_call_temps;rewrite PTree.gso by discriminate;
   rewrite PTree.gso by discriminate;exact NoP. }
 pose proof (exec_generator_auxiliary_empty e lc mf NoC) as Aux.
 exists mf;split;[|exact Unchanged];rewrite generator_no_points_source.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lp);[exact Preprocess|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=lc);[exact Global|].
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=mf) (le1:=PTree.set _np (Vlong Int64.zero) lc);
  [exact Aux|constructor].
Qed.
