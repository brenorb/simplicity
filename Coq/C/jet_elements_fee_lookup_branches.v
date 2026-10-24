(** Original fee-search branches. These execution lemmas introduce no libc
    premise; the comparison call and its explicit model are separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_index_eval.
Require Import C.jet_elements_fee_lookup_compare C.jet_memcmp_model.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition fee_lookup_eq := Ebinop Oeq (Econst_int Int.zero tint) (Etempvar _cmp tint) tint.
Definition fee_lookup_gt := Ebinop Olt (Econst_int Int.zero tint) (Etempvar _cmp tint) tint.
Definition fee_lookup_offset := Ebinop Oadd fee_lookup_half (Econst_int Int.one tint) tulong.
Definition fee_lookup_advance := Ebinop Oadd
  (Etempvar _feeOutputs (tptr (tptr (Tstruct _sigOutput noattr)))) fee_lookup_offset
  (tptr (tptr (Tstruct _sigOutput noattr))).
Definition fee_lookup_tail_len := Ebinop Osub (Etempvar _len tulong) fee_lookup_offset tulong.
Definition fee_lookup_upper := Ssequence (Sset _feeOutputs fee_lookup_advance) (Sset _len fee_lookup_tail_len).
Definition fee_lookup_lower := Sset _len fee_lookup_half.
Definition fee_lookup_fee := Efield
  (Ederef (Etempvar _t'2 (tptr (Tstruct _sigOutput noattr))) (Tstruct _sigOutput noattr)) _assetFee tulong.
Definition fee_lookup_hit := Ssequence (Sset _t'2 fee_lookup_mid)
  (Ssequence (Sset _t'3 fee_lookup_fee) (Sreturn(Some(Etempvar _t'3 tulong)))).
Lemma fee_lookup_branches_source : fee_lookup_after_compare=
  Ssequence (Sifthenelse fee_lookup_eq fee_lookup_hit Sskip)
    (Sifthenelse fee_lookup_gt fee_lookup_upper fee_lookup_lower).
Proof. reflexivity. Qed.
Lemma fee_lookup_assetFee_field : elements_field_at _sigOutput _assetFee 216.
Proof. vm_compute;reflexivity. Qed.

Lemma fee_lookup_split_bounds len : 0<len<=Int64.max_unsigned ->
  0<=len/2<len /\ 1<=len/2+1<=len /\ 0<=len-(len/2+1)<len.
Proof.
  intro Len;pose proof (Z.div_mod len 2 ltac:(lia));pose proof (Z.mod_pos_bound len 2 ltac:(lia)).
  pose proof (Z.div_pos len 2 ltac:(lia) ltac:(lia));repeat split;lia.
Qed.

Lemma fee_lookup_sign_tests c cmp : memcmp_sign c cmp ->
  Int.eq Int.zero cmp=(match c with Eq=>true | _=>false end) /\
  Int.lt Int.zero cmp=(match c with Gt=>true | _=>false end).
Proof.
  destruct c;cbn [memcmp_sign];intro Sign.
  - subst cmp;split;reflexivity.
  - split.
    + apply Int.eq_false;intro Equal;subst cmp;change (Int.signed Int.zero) with 0 in Sign;lia.
    + unfold Int.lt;rewrite Int.signed_zero;destruct (zlt 0 (Int.signed cmp));lia.
  - split.
    + apply Int.eq_false;intro Equal;subst cmp;change (Int.signed Int.zero) with 0 in Sign;lia.
    + unfold Int.lt;rewrite Int.signed_zero;destruct (zlt 0 (Int.signed cmp));lia.
Qed.

Lemma eval_fee_lookup_eq e le m cmp : le!_cmp=Some(Vint cmp) ->
  eval_expr elements_ge e le m fee_lookup_eq (Val.of_bool(Int.eq Int.zero cmp)).
Proof.
  intro Cmp;unfold fee_lookup_eq;eapply eval_Ebinop;
    [constructor|apply eval_Etempvar;exact Cmp|reflexivity].
Qed.
Lemma eval_fee_lookup_gt e le m cmp : le!_cmp=Some(Vint cmp) ->
  eval_expr elements_ge e le m fee_lookup_gt (Val.of_bool(Int.lt Int.zero cmp)).
Proof.
  intro Cmp;unfold fee_lookup_gt;eapply eval_Ebinop;
    [constructor|apply eval_Etempvar;exact Cmp|reflexivity].
Qed.

Lemma eval_fee_lookup_offset e le m len : le!_len=Some(Vlong(Int64.repr len)) ->
  0<len<=Int64.max_unsigned ->
  eval_expr elements_ge e le m fee_lookup_offset (Vlong(Int64.repr(len/2+1))).
Proof.
  intros Length Len;pose proof (fee_lookup_split_bounds len Len) as (Half & _).
  unfold fee_lookup_offset;eapply eval_Ebinop.
  - apply eval_fee_lookup_half with (len:=len);[exact Length|lia].
  - constructor.
  - change (Some(Vlong(Int64.add (Int64.repr(len/2)) Int64.one))=Some(Vlong(Int64.repr(len/2+1)))).
    unfold Int64.add;rewrite Int64.unsigned_repr by lia;reflexivity.
Qed.

Lemma eval_fee_lookup_advance e le m len bt base :
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  0<len<=Int64.max_unsigned -> 0<=base -> base+8*(len/2+1)<=Ptrofs.max_unsigned ->
  eval_expr elements_ge e le m fee_lookup_advance (Vptr bt (Ptrofs.repr(base+8*(len/2+1)))).
Proof.
  intros Length Table Len Base Max;pose proof (fee_lookup_split_bounds len Len) as (_ & Offset & _).
  unfold fee_lookup_advance;eapply eval_Ebinop.
  - apply eval_Etempvar;exact Table.
  - apply eval_fee_lookup_offset with (len:=len);assumption.
  - cbn [typeof fee_lookup_offset];unfold sem_binary_operation.
    rewrite (sem_add_ptr_long_sizeof (Clight.genv_cenv elements_ge) (tptr(Tstruct _sigOutput noattr))
      (Int64.repr(len/2+1)) (Ptrofs.repr base) bt 8 m eq_refl).
    rewrite elements_ptr_index_repr;[reflexivity|exact Base|lia|lia|exact Max].
Qed.

Lemma eval_fee_lookup_tail_len e le m len : le!_len=Some(Vlong(Int64.repr len)) ->
  0<len<=Int64.max_unsigned ->
  eval_expr elements_ge e le m fee_lookup_tail_len (Vlong(Int64.repr(len-(len/2+1)))).
Proof.
  intros Length Len;pose proof (fee_lookup_split_bounds len Len) as (_ & Offset & _).
  unfold fee_lookup_tail_len;eapply eval_Ebinop.
  - apply eval_Etempvar;exact Length.
  - apply eval_fee_lookup_offset with (len:=len);assumption.
  - change (Some(Vlong(Int64.sub (Int64.repr len) (Int64.repr(len/2+1))))=
      Some(Vlong(Int64.repr(len-(len/2+1))))).
    unfold Int64.sub;rewrite !Int64.unsigned_repr by lia;reflexivity.
Qed.

Lemma eval_fee_lookup_fee e le m bp ofs fee : le!_t'2=Some(Vptr bp (Ptrofs.repr ofs)) ->
  0<=ofs -> ofs+224<=Ptrofs.max_unsigned+1 ->
  Mem.load Mint64 m bp (ofs+216)=Some(Vlong fee) ->
  eval_expr elements_ge e le m fee_lookup_fee (Vlong fee).
Proof.
  intros Output Lo Max Load;unfold fee_lookup_fee.
  eapply eval_elements_field_value with (sid:=_sigOutput) (delta:=216) (chunk:=Mint64).
  - reflexivity.
  - exact fee_lookup_assetFee_field.
  - reflexivity.
  - apply eval_elements_deref_struct;exact Output.
  - rewrite elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Load].
Qed.

Definition fee_lookup_hit_temps bp ofs fee le :=
  PTree.set _t'3 (Vlong fee) (PTree.set _t'2 (Vptr bp (Ptrofs.repr ofs)) le).
Theorem exec_fee_lookup_hit le m len bt base bp ofs fee :
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  0<len<=Int64.max_unsigned -> 0<=base -> base+8*(len/2)<=Ptrofs.max_unsigned ->
  0<=ofs -> ofs+224<=Ptrofs.max_unsigned+1 ->
  Mem.load Mptr m bt (base+8*(len/2))=Some(Vptr bp (Ptrofs.repr ofs)) ->
  Mem.load Mint64 m bp (ofs+216)=Some(Vlong fee) ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_hit E0
    (fee_lookup_hit_temps bp ofs fee le) m (Out_return(Some(Vlong fee,tulong))).
Proof.
  intros Length Table Len Base Max Lo End Entry Load;unfold fee_lookup_hit,fee_lookup_hit_temps.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'2 (Vptr bp (Ptrofs.repr ofs)) le).
  - apply exec_Sset;apply eval_fee_lookup_mid with (bt:=bt) (base:=base) (len:=len);try assumption;lia.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
    + apply exec_Sset;apply eval_fee_lookup_fee with (bp:=bp) (ofs:=ofs) (fee:=fee);try assumption;apply PTree.gss.
    + apply exec_Sreturn_some;apply eval_Etempvar;apply PTree.gss.
Qed.

Definition fee_lookup_moved (high : bool) bt base len le :=
  if high then PTree.set _len (Vlong(Int64.repr(len-(len/2+1))))
    (PTree.set _feeOutputs (Vptr bt (Ptrofs.repr(base+8*(len/2+1)))) le)
  else PTree.set _len (Vlong(Int64.repr(len/2))) le.

Theorem exec_fee_lookup_move le m len bt base (high : bool) :
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  0<len<=Int64.max_unsigned -> 0<=base -> (high=true -> base+8*(len/2+1)<=Ptrofs.max_unsigned) ->
  Clight2.exec_stmt elements_ge empty_env le m (if high then fee_lookup_upper else fee_lookup_lower) E0
    (fee_lookup_moved high bt base len le) m Out_normal.
Proof.
  intros Length Table Len Base Max;destruct high;unfold fee_lookup_moved.
  - unfold fee_lookup_upper;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m).
    + apply exec_Sset;apply eval_fee_lookup_advance with (len:=len) (bt:=bt) (base:=base);
        try assumption;apply Max;reflexivity.
    + apply exec_Sset;apply eval_fee_lookup_tail_len with (len:=len);[|exact Len].
      rewrite PTree.gso by discriminate;exact Length.
  - unfold fee_lookup_lower;apply exec_Sset;apply eval_fee_lookup_half with (len:=len);[exact Length|lia].
Qed.

Theorem exec_fee_lookup_after_hit le m len bt base bp ofs fee :
  le!_cmp=Some(Vint Int.zero) ->
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  0<len<=Int64.max_unsigned -> 0<=base -> base+8*(len/2)<=Ptrofs.max_unsigned ->
  0<=ofs -> ofs+224<=Ptrofs.max_unsigned+1 ->
  Mem.load Mptr m bt (base+8*(len/2))=Some(Vptr bp (Ptrofs.repr ofs)) ->
  Mem.load Mint64 m bp (ofs+216)=Some(Vlong fee) ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_after_compare E0
    (fee_lookup_hit_temps bp ofs fee le) m (Out_return(Some(Vlong fee,tulong))).
Proof.
  intros Cmp Length Table Len Base Max Lo End Entry Load;rewrite fee_lookup_branches_source.
  change E0 with (E0 ** E0);eapply exec_Sseq_2;[|discriminate].
  eapply exec_Sifthenelse with (v1:=Vtrue) (b:=true).
  - exact (eval_fee_lookup_eq empty_env le m Int.zero Cmp).
  - reflexivity.
  - apply exec_fee_lookup_hit with (len:=len) (bt:=bt) (base:=base);assumption.
Qed.

Theorem exec_fee_lookup_after_miss le m len bt base cmp high :
  le!_cmp=Some(Vint cmp) -> Int.eq Int.zero cmp=false -> Int.lt Int.zero cmp=high ->
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  0<len<=Int64.max_unsigned -> 0<=base -> (high=true -> base+8*(len/2+1)<=Ptrofs.max_unsigned) ->
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_after_compare E0
    (fee_lookup_moved high bt base len le) m Out_normal.
Proof.
  intros Cmp Ne Gt Length Table Len Base Max;rewrite fee_lookup_branches_source.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
  - eapply exec_Sifthenelse with (v1:=Vfalse) (b:=false).
    + pose proof (eval_fee_lookup_eq empty_env le m cmp Cmp) as Test;rewrite Ne in Test;exact Test.
    + reflexivity.
    + constructor.
  - eapply exec_Sifthenelse with (v1:=Val.of_bool high) (b:=high).
    + rewrite <-Gt;apply eval_fee_lookup_gt;exact Cmp.
    + destruct high;reflexivity.
    + apply exec_fee_lookup_move;assumption.
Qed.

Lemma fee_lookup_compared_frame bp ofs cmp le id : id<>_cmp -> id<>_t'1 -> id<>_t'4 ->
  (fee_lookup_compared bp ofs cmp le)!id=le!id.
Proof. intros A B C;unfold fee_lookup_compared;rewrite !PTree.gso by assumption;reflexivity. Qed.

Definition fee_lookup_next_length (high : bool) len := if high then len-(len/2+1) else len/2.
Definition fee_lookup_next_base (high : bool) base len := if high then base+8*(len/2+1) else base.
Lemma fee_lookup_next_decreases high len : 0<len<=Int64.max_unsigned ->
  0<=fee_lookup_next_length high len<len.
Proof. intro Len;pose proof (fee_lookup_split_bounds len Len) as (A & B & C);destruct high;assumption. Qed.

Lemma fee_lookup_moved_fields high bt base len le : le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  (fee_lookup_moved high bt base len le)!_len=Some(Vlong(Int64.repr(fee_lookup_next_length high len))) /\
  (fee_lookup_moved high bt base len le)!_feeOutputs=
    Some(Vptr bt (Ptrofs.repr(fee_lookup_next_base high base len))) /\
  (forall id,id<>_len -> id<>_feeOutputs -> (fee_lookup_moved high bt base len le)!id=le!id).
Proof.
  intro Table;destruct high;unfold fee_lookup_moved,fee_lookup_next_length,fee_lookup_next_base.
  - split;[apply PTree.gss|];split.
    + rewrite PTree.gso by discriminate;apply PTree.gss.
    + intros id A B;rewrite !PTree.gso by assumption;reflexivity.
  - split;[apply PTree.gss|];split.
    + rewrite PTree.gso by discriminate;exact Table.
    + intros id A B;rewrite PTree.gso by assumption;reflexivity.
Qed.

Definition fee_lookup_branch_temps c bt base len bp ofs fee le := match c with
  | Eq=>fee_lookup_hit_temps bp ofs fee le
  | Lt=>fee_lookup_moved false bt base len le
  | Gt=>fee_lookup_moved true bt base len le end.
Definition fee_lookup_branch_out c fee := match c with
  | Eq=>Out_return(Some(Vlong fee,tulong)) | _=>Out_normal end.

Definition fee_lookup_loop := Swhile (Etempvar _len tulong) fee_lookup_work.
Lemma fee_lookup_function_source : fn_body f_lookup_fee=
  Ssequence fee_lookup_loop (Sreturn(Some(Econst_int Int.zero tint))).
Proof. reflexivity. Qed.

Theorem exec_fee_lookup_zero e le m : le!_len=Some(Vlong Int64.zero) ->
  Clight2.exec_stmt elements_ge e le m (fn_body f_lookup_fee) E0 le m
    (Out_return(Some(Vint Int.zero,tint))).
Proof.
  intro Length;rewrite fee_lookup_function_source.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=m).
  - unfold fee_lookup_loop,Swhile;eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
    change E0 with (E0 ** E0);eapply exec_Sseq_2;[|discriminate].
    eapply exec_Sifthenelse with (v1:=Vlong Int64.zero) (b:=false).
    + apply eval_Etempvar;exact Length.
    + reflexivity.
    + constructor.
  - apply exec_Sreturn_some;constructor.
Qed.

Theorem exec_fee_lookup_work (Model : memcmp_model) le m len bt base bk keybase bp ofs key candidate fee :
  le!_len=Some(Vlong(Int64.repr len)) -> le!_feeOutputs=Some(Vptr bt (Ptrofs.repr base)) ->
  le!_assetid=Some(Vptr bk (Ptrofs.repr keybase)) ->
  0<len<=Int64.max_unsigned -> 0<=base -> base+8*len<=Ptrofs.max_unsigned ->
  0<=keybase -> keybase+32<=Ptrofs.max_unsigned+1 -> 0<=ofs -> ofs+224<=Ptrofs.max_unsigned+1 ->
  Mem.load Mptr m bt (base+8*(len/2))=Some(Vptr bp (Ptrofs.repr ofs)) ->
  Mem.load Mint64 m bp (ofs+216)=Some(Vlong fee) ->
  length key=32%nat -> length candidate=32%nat ->
  bytes_at m bk keybase key -> bytes_at m bp ofs candidate -> exists cmp,
  memcmp_sign (bytes_cmp key candidate) cmp /\
  Clight2.exec_stmt elements_ge empty_env le m fee_lookup_work E0
    (fee_lookup_branch_temps (bytes_cmp key candidate) bt base len bp ofs fee
      (fee_lookup_compared bp ofs cmp le)) m (fee_lookup_branch_out (bytes_cmp key candidate) fee).
Proof.
  intros Length Table Key Len Base Max K0 KMax C0 CMax Load Fee KeyLen CandidateLen KeyBytes CandidateBytes.
  pose proof (fee_lookup_split_bounds len Len) as (Half & Offset & Tail).
  destruct (exec_fee_lookup_compare Model le m len bt base bk keybase bp ofs key candidate
    Length Table Key ltac:(lia) Base ltac:(lia) K0 KMax C0 ltac:(lia) Load KeyLen CandidateLen KeyBytes CandidateBytes)
    as (cmp & Compare & Sign).
  pose proof (fee_lookup_sign_tests (bytes_cmp key candidate) cmp Sign) as (EqTest & GtTest).
  assert (NewLen : (fee_lookup_compared bp ofs cmp le)!_len=Some(Vlong(Int64.repr len))).
  { rewrite fee_lookup_compared_frame by discriminate;exact Length. }
  assert (NewTable : (fee_lookup_compared bp ofs cmp le)!_feeOutputs=Some(Vptr bt (Ptrofs.repr base))).
  { rewrite fee_lookup_compared_frame by discriminate;exact Table. }
  assert (NewCmp : (fee_lookup_compared bp ofs cmp le)!_cmp=Some(Vint cmp)).
  { unfold fee_lookup_compared;apply PTree.gss. }
  exists cmp;split;[exact Sign|];rewrite fee_lookup_compare_source.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=fee_lookup_compared bp ofs cmp le) (m1:=m);
    [exact Compare|].
  destruct (bytes_cmp key candidate) eqn:Which;cbn [fee_lookup_branch_temps fee_lookup_branch_out].
  - change (cmp=Int.zero) in Sign;subst cmp.
    apply exec_fee_lookup_after_hit with (len:=len) (bt:=bt) (base:=base);try assumption;lia.
  - apply exec_fee_lookup_after_miss with (cmp:=cmp);try assumption;try lia;discriminate.
  - apply exec_fee_lookup_after_miss with (cmp:=cmp);try assumption;lia.
Qed.
