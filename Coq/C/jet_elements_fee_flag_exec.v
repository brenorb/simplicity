(** Execution of the original processed-output classifier. This is not the
    canonical outputIsFee equivalence: the empty-digest converse is separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Values Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Lemma fee_empty_script_field : elements_field_at _sigOutput _emptyScript 241.
Proof. vm_compute; reflexivity. Qed.
Lemma fee_asset_field : elements_field_at _sigOutput _asset 0.
Proof. vm_compute; reflexivity. Qed.
Lemma fee_amount_field : elements_field_at _sigOutput _amt 104.
Proof. vm_compute; reflexivity. Qed.
Lemma fee_asset_prefix_field : elements_field_at _confidential _prefix 32.
Proof. vm_compute; reflexivity. Qed.
Lemma fee_amount_prefix_field : elements_field_at _confAmount _prefix 32.
Proof. vm_compute; reflexivity. Qed.

Definition fee_bool_int (b : bool) := if b then Int.one else Int.zero.
Definition fee_flag_expr := Efield
 (Ederef (Etempvar _output (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr))
 _emptyScript tbool.
Definition fee_prefix_expr field sid := Efield
 (Efield (Ederef (Etempvar _output (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr))
   field (Tstruct sid noattr)) _prefix tint.
Definition fee_prefix_check loadtmp resulttmp field sid :=
 Ssequence (Sset loadtmp (fee_prefix_expr field sid))
  (Sset resulttmp (Ecast (Ebinop Oeq (Econst_int Int.one tint) (Etempvar loadtmp tint) tint) tbool)).

Lemma fee_flag_value e le m b ofs empty :
 le!_output=Some (Vptr b (Ptrofs.repr ofs)) ->
 0<=ofs -> ofs+248<=Ptrofs.max_unsigned ->
 Mem.load Mint8unsigned m b (ofs+241)=Some (Vint (fee_bool_int empty)) ->
 eval_expr elements_ge e le m fee_flag_expr (Vint (fee_bool_int empty)).
Proof.
 intros Output Lo Hi Load;unfold fee_flag_expr.
 eapply eval_elements_field_value with (sid:=_sigOutput) (delta:=241) (chunk:=Mint8unsigned).
 - reflexivity.
 - exact fee_empty_script_field.
 - reflexivity.
 - apply eval_elements_deref_struct;exact Output.
 - rewrite elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Load].
Qed.


Lemma fee_prefix_value e le m b ofs field sid delta value :
 le!_output=Some (Vptr b (Ptrofs.repr ofs)) ->
 0<=ofs -> ofs+248<=Ptrofs.max_unsigned -> 0<=delta -> delta+36<=248 ->
 elements_field_at _sigOutput field delta -> elements_field_at sid _prefix 32 ->
 Mem.load Mint32 m b (ofs+delta+32)=Some (Vint value) ->
 eval_expr elements_ge e le m (fee_prefix_expr field sid) (Vint value).
Proof.
 intros Output Lo Hi D0 DHi Field Prefix Load;unfold fee_prefix_expr.
 eapply eval_elements_field_value with (sid:=sid) (delta:=32) (chunk:=Mint32).
 - reflexivity.
 - exact Prefix.
 - reflexivity.
 - eapply eval_elements_field_struct;[reflexivity|exact Field|].
   apply eval_elements_deref_struct;exact Output.
 - rewrite !elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Load].
Qed.

Lemma fee_explicit_comparison m value :
 sem_binary_operation elements_ge Oeq (Vint Int.one) tint (Vint value) tint m=
 Some (Vint (fee_bool_int (Int.eq Int.one value))).
Proof.
 unfold Cop.sem_binary_operation;unfold Cop.sem_cmp;unfold Cop.sem_binarith.
 unfold Cop.sem_cast;cbn;destruct (Int.eq Int.one value);reflexivity.
Qed.

Lemma fee_bool_cast m bit :
 sem_cast (Vint (fee_bool_int bit)) tint tbool m=Some (Vint (fee_bool_int bit)).
Proof. destruct bit;reflexivity. Qed.

Lemma exec_fee_prefix_check e le m b ofs field sid delta value loadtmp resulttmp :
 le!_output=Some (Vptr b (Ptrofs.repr ofs)) ->
 0<=ofs -> ofs+248<=Ptrofs.max_unsigned -> 0<=delta -> delta+36<=248 ->
 elements_field_at _sigOutput field delta -> elements_field_at sid _prefix 32 ->
 Mem.load Mint32 m b (ofs+delta+32)=Some (Vint value) ->
 Clight2.exec_stmt elements_ge e le m (fee_prefix_check loadtmp resulttmp field sid) E0
  (PTree.set resulttmp (Vint (fee_bool_int (Int.eq Int.one value)))
    (PTree.set loadtmp (Vint value) le)) m Out_normal.
Proof.
 intros Output Lo Hi D0 DHi Field Prefix Load;unfold fee_prefix_check.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set loadtmp (Vint value) le).
 - apply exec_Sset;exact (fee_prefix_value e le m b ofs field sid delta value Output Lo Hi D0 DHi Field Prefix Load).
 - apply exec_Sset;eapply eval_Ecast.
   + eapply eval_Ebinop with (v1:=Vint Int.one) (v2:=Vint value).
     * apply eval_Econst_int.
     * apply eval_Etempvar;apply PTree.gss.
     * apply fee_explicit_comparison.
   + apply fee_bool_cast.
Qed.

Lemma exec_fee_guarded_prefix e le m b ofs field sid delta value loadtmp resulttmp guard bit :
 le!_output=Some (Vptr b (Ptrofs.repr ofs)) ->
 0<=ofs -> ofs+248<=Ptrofs.max_unsigned -> 0<=delta -> delta+36<=248 ->
 elements_field_at _sigOutput field delta -> elements_field_at sid _prefix 32 ->
 Mem.load Mint32 m b (ofs+delta+32)=Some (Vint value) ->
 loadtmp<>_output -> resulttmp<>_output ->
 eval_expr elements_ge e le m guard (Vint (fee_bool_int bit)) ->
 bool_val (Vint (fee_bool_int bit)) (typeof guard) m=Some bit ->
 exists lef,
 Clight2.exec_stmt elements_ge e le m
  (Sifthenelse guard (fee_prefix_check loadtmp resulttmp field sid)
    (Sset resulttmp (Econst_int Int.zero tint))) E0 lef m Out_normal /\
 lef!_output=Some (Vptr b (Ptrofs.repr ofs)) /\
 lef!resulttmp=Some (Vint (fee_bool_int (andb bit (Int.eq Int.one value)))).
Proof.
 intros Output Lo Hi D0 DHi Field Prefix Load LT RT Guard GuardBool.
 destruct bit.
 - exists (PTree.set resulttmp (Vint (fee_bool_int (Int.eq Int.one value)))
     (PTree.set loadtmp (Vint value) le)).
   split.
   + eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true).
     * exact Guard.
     * exact GuardBool.
     * exact (exec_fee_prefix_check e le m b ofs field sid delta value loadtmp resulttmp
         Output Lo Hi D0 DHi Field Prefix Load).
   + split.
     * rewrite PTree.gso by exact (not_eq_sym RT).
       rewrite PTree.gso by exact (not_eq_sym LT);exact Output.
     * apply PTree.gss.
 - exists (PTree.set resulttmp (Vint Int.zero) le);split.
   + eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
     * exact Guard.
     * exact GuardBool.
     * apply exec_Sset;apply eval_Econst_int.
   + split;[rewrite PTree.gso by exact (not_eq_sym RT);exact Output|apply PTree.gss].
Qed.

Definition fee_first_if := Sifthenelse (Etempvar _t'4 tbool)
 (fee_prefix_check _t'5 _t'1 _asset _confidential) (Sset _t'1 (Econst_int Int.zero tint)).
Definition fee_second_if := Sifthenelse (Etempvar _t'1 tint)
 (fee_prefix_check _t'3 _t'2 _amt _confAmount) (Sset _t'2 (Econst_int Int.zero tint)).
Definition fee_original_body := Ssequence
 (Ssequence (Ssequence (Sset _t'4 fee_flag_expr) fee_first_if) fee_second_if)
 (Sreturn (Some (Etempvar _t'2 tint))).
Definition fee_classifier empty asset amount :=
 andb (andb empty (Int.eq Int.one asset)) (Int.eq Int.one amount).

Lemma fee_original_body_source : fn_body f_isFee=fee_original_body.
Proof. reflexivity. Qed.

Lemma exec_fee_original_body e le m b ofs empty asset amount :
 le!_output=Some (Vptr b (Ptrofs.repr ofs)) ->
 0<=ofs -> ofs+248<=Ptrofs.max_unsigned ->
 Mem.load Mint8unsigned m b (ofs+241)=Some (Vint (fee_bool_int empty)) ->
 Mem.load Mint32 m b (ofs+32)=Some (Vint asset) ->
 Mem.load Mint32 m b (ofs+136)=Some (Vint amount) ->
 exists lef,Clight2.exec_stmt elements_ge e le m (fn_body f_isFee) E0 lef m
  (Out_return (Some (Vint (fee_bool_int (fee_classifier empty asset amount)),tint))).
Proof.
 intros Output Lo Hi Flag Asset Amount.
 set (lea:=PTree.set _t'4 (Vint (fee_bool_int empty)) le).
 set (first:=andb empty (Int.eq Int.one asset)).
 assert (OutputA : lea!_output=Some (Vptr b (Ptrofs.repr ofs))).
 { unfold lea;rewrite PTree.gso by discriminate;exact Output. }
 assert (Stage1 : exists leb,
  Clight2.exec_stmt elements_ge e lea m fee_first_if E0 leb m Out_normal /\
  leb!_output=Some (Vptr b (Ptrofs.repr ofs)) /\
  leb!_t'1=Some (Vint (fee_bool_int first))).
 { unfold fee_first_if,first;eapply exec_fee_guarded_prefix with (delta:=0) (value:=asset).
   - exact OutputA.
   - exact Lo.
   - exact Hi.
   - lia.
   - lia.
   - exact fee_asset_field.
   - exact fee_asset_prefix_field.
   - replace (ofs+0+32) with (ofs+32) by lia;exact Asset.
   - discriminate.
   - discriminate.
   - apply eval_Etempvar;unfold lea;apply PTree.gss.
   - destruct empty;reflexivity. }
 destruct Stage1 as (leb & FirstCall & OutputB & FirstValue).
 assert (Stage2 : exists lec,
  Clight2.exec_stmt elements_ge e leb m fee_second_if E0 lec m Out_normal /\
  lec!_output=Some (Vptr b (Ptrofs.repr ofs)) /\
  lec!_t'2=Some (Vint (fee_bool_int (andb first (Int.eq Int.one amount))))).
 { unfold fee_second_if;eapply exec_fee_guarded_prefix with (delta:=104) (value:=amount).
   - exact OutputB.
   - exact Lo.
   - exact Hi.
   - lia.
   - lia.
   - exact fee_amount_field.
   - exact fee_amount_prefix_field.
   - replace (ofs+104+32) with (ofs+136) by lia;exact Amount.
   - discriminate.
   - discriminate.
   - apply eval_Etempvar;exact FirstValue.
   - destruct first;reflexivity. }
 destruct Stage2 as (lec & SecondCall & OutputC & Result).
 exists lec;rewrite fee_original_body_source;unfold fee_original_body.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lec).
 - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=leb).
   + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lea).
     * apply exec_Sset;exact (fee_flag_value e le m b ofs empty Output Lo Hi Flag).
     * exact FirstCall.
   + exact SecondCall.
 - apply exec_Sreturn_some;apply eval_Etempvar;exact Result.
Qed.

Definition fee_initial_temps b ofs :=
 PTree.set _output (Vptr b (Ptrofs.repr ofs)) (create_undef_temps (fn_temps f_isFee)).

Lemma fee_function_entry m b ofs : function_entry2 elements_ge f_isFee
 [Vptr b (Ptrofs.repr ofs)] m empty_env (fee_initial_temps b ofs) m.
Proof.
 apply function_entry2_intro.
 - apply list_norepet_nil.
 - repeat constructor;simpl;intuition discriminate.
 - intros x y HX HY;cbn in HX,HY;intuition (subst;discriminate).
 - apply alloc_variables_nil.
 - reflexivity.
Qed.

Theorem eval_processed_isFee m b ofs empty asset amount :
 0<=ofs -> ofs+248<=Ptrofs.max_unsigned ->
 Mem.load Mint8unsigned m b (ofs+241)=Some (Vint (fee_bool_int empty)) ->
 Mem.load Mint32 m b (ofs+32)=Some (Vint asset) ->
 Mem.load Mint32 m b (ofs+136)=Some (Vint amount) ->
 Clight2.eval_funcall elements_ge m (Internal f_isFee) [Vptr b (Ptrofs.repr ofs)] E0 m
  (Vint (fee_bool_int (fee_classifier empty asset amount))).
Proof.
 intros Lo Hi Flag Asset Amount.
 destruct (exec_fee_original_body empty_env (fee_initial_temps b ofs) m b ofs empty asset amount
  ltac:(unfold fee_initial_temps;apply PTree.gss) Lo Hi Flag Asset Amount) as (lef & Body).
 eapply eval_funcall_internal with (e:=empty_env) (le1:=fee_initial_temps b ofs) (le2:=lef)
  (m1:=m) (m2:=m) (out:=Out_return (Some (Vint (fee_bool_int (fee_classifier empty asset amount)),tint))).
 - apply fee_function_entry.
 - exact Body.
 - split;[discriminate|apply fee_bool_cast].
 - reflexivity.
Qed.
