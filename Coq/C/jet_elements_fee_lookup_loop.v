(** Execute the original fee search over every represented finite table.
    The functional answer below records its binary-search choices, not the
    canonical total_fee specification or the correctness of fee building. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_memcmp_model.
Require Import C.jet_elements_fee_lookup_compare C.jet_elements_fee_lookup_branches C.jet_elements_fee_lookup_table.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Fixpoint fee_lookup_answer fuel key entries : int64 := match fuel with
  | O=>Int64.zero
  | S fuel=>match nth_error entries (length entries/2) with
    | None=>Int64.zero
    | Some x=>match bytes_cmp key (fee_entry_key x) with
      | Eq=>fee_entry_amount x
      | Lt=>fee_lookup_answer fuel key (fee_search_part false entries)
      | Gt=>fee_lookup_answer fuel key (fee_search_part true entries) end end end.
Definition fee_lookup_loop_value out value :=
  (out=Out_normal /\ value=Int64.zero) \/ out=Out_return(Some(Vlong value,tulong)).

Lemma fee_lookup_guard le m len : le!_len=Some(Vlong(Int64.repr len)) ->
  0<len<=Int64.max_unsigned ->
  Clight2.exec_stmt elements_ge empty_env le m
    (Sifthenelse (Etempvar _len tulong) Sskip Sbreak) E0 le m Out_normal.
Proof.
  intros Length Len;eapply exec_Sifthenelse with (v1:=Vlong(Int64.repr len)) (b:=true).
  - apply eval_Etempvar;exact Length.
  - change (Some(negb(Int64.eq (Int64.repr len) Int64.zero))=Some true).
    rewrite Int64.eq_false;[reflexivity|].
    intro Equal;apply (f_equal Int64.unsigned) in Equal.
    rewrite Int64.unsigned_repr,Int64.unsigned_zero in Equal by lia;lia.
  - constructor.
Qed.

Lemma fee_lookup_loop_continue le lm lf m out len :
  le!_len=Some(Vlong(Int64.repr len)) -> 0<len<=Int64.max_unsigned ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_work E0 lm m Out_normal ->
  Clight2.exec_stmt elements_ge empty_env lm m fee_lookup_loop E0 lf m out ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_loop E0 lf m out.
Proof.
  intros Length Len Work Next;unfold fee_lookup_loop,Swhile in *.
  change E0 with (E0 ** E0 ** E0).
  eapply exec_Sloop_loop with (le1:=lm) (m1:=m) (le2:=lm) (m2:=m) (out1:=Out_normal).
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply fee_lookup_guard with (len:=len);assumption|exact Work].
  - constructor.
  - constructor.
  - exact Next.
Qed.

Lemma fee_lookup_loop_hit le lf m len fee :
  le!_len=Some(Vlong(Int64.repr len)) -> 0<len<=Int64.max_unsigned ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_work E0 lf m (Out_return(Some(Vlong fee,tulong))) ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_loop E0 lf m (Out_return(Some(Vlong fee,tulong))).
Proof.
  intros Length Len Work;unfold fee_lookup_loop,Swhile.
  eapply exec_Sloop_stop1 with (out':=Out_return(Some(Vlong fee,tulong)));[|constructor].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[apply fee_lookup_guard with (len:=len);assumption|exact Work].
Qed.

Theorem exec_fee_lookup_loop (Model : memcmp_model) : forall fuel entries,
  (length entries<=fuel)%nat -> forall le m keyval tableval key,
  le!_len=Some(Vlong(Int64.repr(Z.of_nat(length entries)))) ->
  le!_assetid=Some keyval -> le!_feeOutputs=Some tableval ->
  fee_lookup_storage m keyval tableval key entries -> exists lef out,
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_loop E0 lef m out /\
  fee_lookup_loop_value out (fee_lookup_answer fuel key entries).
Proof.
  induction fuel as [|fuel IH];intros entries Fuel le m keyval tableval key Length KeyArg TableArg Storage.
  - assert (Empty : entries=[]) by (destruct entries;[reflexivity|cbn in Fuel;lia]).
    subst entries;exists le,Out_normal;split;[|left;split;reflexivity].
    unfold fee_lookup_loop,Swhile;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
    change E0 with (E0 ** E0);eapply exec_Sseq_2;[|discriminate].
    eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=false);
      [apply eval_Etempvar;exact Length|reflexivity|constructor].
  - destruct entries as [|head tail].
    { exists le,Out_normal;split;[|left;split;reflexivity].
      unfold fee_lookup_loop,Swhile;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
      change E0 with (E0 ** E0);eapply exec_Sseq_2;[|discriminate].
      eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=false);
        [apply eval_Etempvar;exact Length|reflexivity|constructor]. }
    set (entries:=head::tail) in *.
    assert (Nonempty : entries<>[]) by (unfold entries;discriminate).
    destruct Storage as [Empty|(bk & keybase & bt & base & KeyVal & TableVal & KeyRep & TableRep)];[contradiction|].
    subst keyval tableval.
    pose proof TableRep as (Base & Max & Rows).
    destruct KeyRep as (K0 & KMax & KeyLen & KeyBytes).
    assert (Len : 0<Z.of_nat(length entries)<=Int64.max_unsigned).
    { change Ptrofs.max_unsigned with 18446744073709551615 in Max.
      change Int64.max_unsigned with 18446744073709551615;destruct entries;cbn in *;[contradiction|lia]. }
    assert (Mid : (length entries/2<length entries)%nat) by
      (apply Nat.div_lt;[destruct entries;cbn in *;[congruence|lia]|lia]).
    destruct (nth_error entries (length entries/2)) as [x|] eqn:At.
    2: { apply nth_error_None in At;lia. }
    destruct (Rows _ x At) as (Load & C0 & CMax & CandidateLen & CandidateBytes & Fee).
    rewrite Nat2Z.inj_div in Load.
    destruct (exec_fee_lookup_work Model le m (Z.of_nat(length entries)) bt base bk keybase
      (fee_entry_block x) (fee_entry_offset x) key (fee_entry_key x) (fee_entry_amount x)
      Length TableArg KeyArg Len Base Max K0 KMax C0 CMax Load Fee KeyLen CandidateLen KeyBytes CandidateBytes)
      as (cmp & Sign & Work).
    set (compared:=fee_lookup_compared (fee_entry_block x) (fee_entry_offset x) cmp le) in *.
    assert (Miss : forall high,
      Clight2.exec_stmt elements_ge empty_env le m fee_lookup_work E0
        (fee_lookup_moved high bt base (Z.of_nat(length entries)) compared) m Out_normal ->
      exists lef out,Clight2.exec_stmt elements_ge empty_env le m fee_lookup_loop E0 lef m out /\
        fee_lookup_loop_value out (fee_lookup_answer fuel key (fee_search_part high entries))).
    { intros high Step.
      assert (TableC : compared!_feeOutputs=Some(Vptr bt (Ptrofs.repr base))).
      { unfold compared;rewrite fee_lookup_compared_frame by discriminate;exact TableArg. }
      destruct (fee_lookup_moved_fields high bt base (Z.of_nat(length entries)) compared TableC)
        as (NextLen & NextTable & Frame).
      set (next:=fee_lookup_moved high bt base (Z.of_nat(length entries)) compared) in *.
      assert (NextKey : next!_assetid=Some(Vptr bk (Ptrofs.repr keybase))).
      { unfold next;rewrite Frame by discriminate;unfold compared;rewrite fee_lookup_compared_frame by discriminate;exact KeyArg. }
      assert (NextStorage : fee_lookup_storage m (Vptr bk (Ptrofs.repr keybase))
        (Vptr bt (Ptrofs.repr(fee_lookup_next_base high base (Z.of_nat(length entries)))))
        key (fee_search_part high entries)).
      { right;exists bk,keybase,bt,(fee_lookup_next_base high base (Z.of_nat(length entries))).
        split;[reflexivity|];split;[reflexivity|];split.
        - repeat split;assumption.
        - apply fee_table_part;assumption. }
      rewrite <-(fee_search_part_length high entries Nonempty) in NextLen.
      destruct (IH (fee_search_part high entries) ltac:(pose proof (fee_search_part_small high entries Nonempty);lia)
        next m (Vptr bk (Ptrofs.repr keybase))
        (Vptr bt (Ptrofs.repr(fee_lookup_next_base high base (Z.of_nat(length entries)))))
        key NextLen NextKey NextTable NextStorage) as (lef & out & Loop & Result).
      exists lef,out;split;[eapply fee_lookup_loop_continue;[exact Length|exact Len|exact Step|exact Loop]|exact Result]. }
    cbn [fee_lookup_answer];rewrite At.
    destruct (bytes_cmp key (fee_entry_key x)) eqn:Which;cbn [fee_lookup_branch_temps fee_lookup_branch_out] in Work |- *.
    + exists (fee_lookup_hit_temps (fee_entry_block x) (fee_entry_offset x) (fee_entry_amount x) compared),
        (Out_return(Some(Vlong(fee_entry_amount x),tulong)));split;[|right;reflexivity].
      eapply fee_lookup_loop_hit;[exact Length|exact Len|exact Work].
    + apply (Miss false);exact Work.
    + apply (Miss true);exact Work.
Qed.

Theorem exec_fee_lookup_body (Model : memcmp_model) fuel entries le m keyval tableval key :
  (length entries<=fuel)%nat ->
  le!_len=Some(Vlong(Int64.repr(Z.of_nat(length entries)))) ->
  le!_assetid=Some keyval -> le!_feeOutputs=Some tableval ->
  fee_lookup_storage m keyval tableval key entries -> exists lef out,
  Clight2.exec_stmt elements_ge empty_env le m (fn_body f_lookup_fee) E0 lef m out /\
  outcome_result_value out tulong (Vlong(fee_lookup_answer fuel key entries)) m.
Proof.
  intros Fuel Length KeyArg TableArg Storage.
  destruct (exec_fee_lookup_loop Model fuel entries Fuel le m keyval tableval key Length KeyArg TableArg Storage)
    as (lef & out & Loop & [(Normal & Zero)|Returned]).
  - subst out;exists lef,(Out_return(Some(Vint Int.zero,tint)));split.
    + rewrite fee_lookup_function_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
        [exact Loop|apply exec_Sreturn_some;constructor].
    + split;[discriminate|rewrite Zero;reflexivity].
  - subst out;exists lef,(Out_return(Some(Vlong(fee_lookup_answer fuel key entries),tulong)));split.
    + rewrite fee_lookup_function_source;change E0 with (E0 ** E0);eapply exec_Sseq_2;
        [exact Loop|discriminate].
    + split;[discriminate|reflexivity].
Qed.

Definition fee_lookup_initial_temps keyval tableval len :=
  PTree.set _len (Vlong(Int64.repr len)) (PTree.set _feeOutputs tableval
    (PTree.set _assetid keyval (create_undef_temps(fn_temps f_lookup_fee)))).
Lemma fee_lookup_function_entry m keyval tableval len : function_entry2 elements_ge f_lookup_fee
  [keyval;tableval;Vlong(Int64.repr len)] m empty_env (fee_lookup_initial_temps keyval tableval len) m.
Proof.
  apply function_entry2_intro.
  - apply list_norepet_nil.
  - repeat constructor;simpl;intuition discriminate.
  - intros x y X Y;cbn in X,Y;intuition (subst;discriminate).
  - apply alloc_variables_nil.
  - reflexivity.
Qed.

Theorem eval_fee_lookup_table (Model : memcmp_model) m keyval tableval key entries :
  fee_lookup_storage m keyval tableval key entries ->
  Clight2.eval_funcall elements_ge m (Internal f_lookup_fee)
    [keyval;tableval;Vlong(Int64.repr(Z.of_nat(length entries)))] E0 m
    (Vlong(fee_lookup_answer (length entries) key entries)).
Proof.
  intro Storage.
  destruct (exec_fee_lookup_body Model (length entries) entries
    (fee_lookup_initial_temps keyval tableval (Z.of_nat(length entries))) m keyval tableval key
    ltac:(lia) ltac:(unfold fee_lookup_initial_temps;apply PTree.gss)
    ltac:(unfold fee_lookup_initial_temps;rewrite !PTree.gso by discriminate;apply PTree.gss)
    ltac:(unfold fee_lookup_initial_temps;rewrite PTree.gso by discriminate;apply PTree.gss) Storage)
    as (lef & out & Body & Result).
  eapply eval_funcall_internal with (e:=empty_env)
    (le1:=fee_lookup_initial_temps keyval tableval (Z.of_nat(length entries))) (le2:=lef)
    (m1:=m) (m2:=m) (out:=out).
  - apply fee_lookup_function_entry.
  - exact Body.
  - exact Result.
  - reflexivity.
Qed.

Corollary eval_fee_lookup_empty m keyval tableval :
  Clight2.eval_funcall elements_ge m (Internal f_lookup_fee) [keyval;tableval;Vlong Int64.zero] E0 m
    (Vlong Int64.zero).
Proof.
  eapply eval_funcall_internal with (e:=empty_env) (le1:=fee_lookup_initial_temps keyval tableval 0)
    (le2:=fee_lookup_initial_temps keyval tableval 0) (m1:=m) (m2:=m)
    (out:=Out_return(Some(Vint Int.zero,tint))).
  - apply fee_lookup_function_entry.
  - apply exec_fee_lookup_zero;unfold fee_lookup_initial_temps;apply PTree.gss.
  - split;[discriminate|reflexivity].
  - reflexivity.
Qed.
