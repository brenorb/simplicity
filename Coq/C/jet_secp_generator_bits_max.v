(** The actual two final maximum-count updates after generator wNAF calls.
    The calls themselves, including memset, remain a separate obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_generator_split_call.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition generator_raise_bits (high : bool) :=
 let id:=if high then _bits_ng_128 else _bits_ng_1 in
 Sifthenelse (Ebinop Ogt (Etempvar id tint) (Etempvar _bits tint) tint)
  (Sset _bits (Etempvar id tint)) Sskip.
Definition generator_bits_max := match generator_wnaf_setup with
 | Ssequence _ (Ssequence _ tail)=>tail | _=>Sskip end.
Definition generator_raise_temps (le : temp_env) current candidate :=
 if current <? candidate then PTree.set _bits (Vint (Int.repr candidate)) le else le.
Definition generator_bits_max_temps le low high :=
 generator_raise_temps (generator_raise_temps le 0 low) low high.

Lemma generator_bits_max_source : generator_bits_max=
 Ssequence (generator_raise_bits false) (generator_raise_bits true).
Proof. reflexivity. Qed.

Lemma eval_generator_raise_guard (high : bool) e le m current candidate :
 0<=current<=129 -> 0<=candidate<=129 -> le!_bits=Some (Vint (Int.repr current)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr candidate)) ->
 eval_expr secp_ge e le m
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

Theorem exec_generator_raise_bits (high : bool) e le m current candidate :
 0<=current<=129 -> 0<=candidate<=129 -> le!_bits=Some (Vint (Int.repr current)) ->
 le!(if high then _bits_ng_128 else _bits_ng_1)=Some (Vint (Int.repr candidate)) ->
 Clight2.exec_stmt secp_ge e le m (generator_raise_bits high) E0
  (generator_raise_temps le current candidate) m Out_normal.
Proof.
 intros Current Candidate Bits Count.
 pose proof (eval_generator_raise_guard high e le m current candidate Current Candidate Bits Count) as Guard.
 unfold generator_raise_bits,generator_raise_temps.
 destruct (current <? candidate) eqn:Choose.
 - eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);
    [exact Guard|reflexivity|apply exec_Sset;apply eval_Etempvar;exact Count].
 - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[exact Guard|reflexivity|constructor].
Qed.

Lemma generator_raise_bits_value le current candidate : le!_bits=Some (Vint (Int.repr current)) ->
 (generator_raise_temps le current candidate)!_bits=Some (Vint (Int.repr (Z.max current candidate))).
Proof.
 intro Bits;unfold generator_raise_temps;destruct (current <? candidate) eqn:Choose.
 - apply Z.ltb_lt in Choose;rewrite Z.max_r by lia;apply PTree.gss.
 - apply Z.ltb_ge in Choose;rewrite Z.max_l by lia;exact Bits.
Qed.
Lemma generator_raise_bits_other le current candidate id : id<>_bits ->
 (generator_raise_temps le current candidate)!id=le!id.
Proof. intro Other;unfold generator_raise_temps;destruct (current <? candidate);[apply PTree.gso;exact Other|reflexivity]. Qed.

Theorem exec_generator_bits_max e le m low high :
 0<=low<=129 -> 0<=high<=129 -> le!_bits=Some (Vint Int.zero) ->
 le!_bits_ng_1=Some (Vint (Int.repr low)) -> le!_bits_ng_128=Some (Vint (Int.repr high)) ->
 Clight2.exec_stmt secp_ge e le m generator_bits_max E0 (generator_bits_max_temps le low high) m Out_normal /\
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
   + apply (exec_generator_raise_bits false e le m 0 low);try assumption;lia.
   + exact (exec_generator_raise_bits true e _ m low high Low High AfterLow AfterHigh).
 - split.
   + unfold generator_bits_max_temps;apply generator_raise_bits_value;exact AfterLow.
   + intros id Other;unfold generator_bits_max_temps;rewrite !generator_raise_bits_other by exact Other;reflexivity.
Qed.
