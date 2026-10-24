(** Original signed62 array addresses, including the loop's i-1 expression. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events Globalenvs Errors.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_modinv_fg_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition fg_s62_type := Tstruct _secp256k1_modinv64_signed62 noattr.
Definition fg_array id := Efield (Ederef (Etempvar id (tptr fg_s62_type)) fg_s62_type)
 _v (tarray tlong 5).
Definition fg_index id ix := Ederef (Ebinop Oadd (fg_array id) ix (tptr tlong)) tlong.

Lemma fg_array_layout : exists co,
 (genv_cenv secp_ge)!_secp256k1_modinv64_signed62=Some co /\
 field_offset secp_ge _v (co_members co)=OK (0,Full).
Proof.
 assert (Members : option_map co_members ((genv_cenv secp_ge)!_secp256k1_modinv64_signed62)=
  Some [Member_plain _v (tarray tlong 5)]) by (vm_compute;reflexivity).
 destruct ((genv_cenv secp_ge)!_secp256k1_modinv64_signed62) as [co|] eqn:Composite;
  [|discriminate].
 exists co;split;[reflexivity|];injection Members as Members;rewrite Members;reflexivity.
Qed.

Definition fg_for := match fg_rest with Ssequence s _=>s | _=>Sskip end.
Definition fg_loop := match fg_for with Ssequence _ s=>s | _=>Sskip end.
Definition fg_work := match fg_loop with Sloop (Ssequence _ s) _=>s | _=>Sskip end.
Definition fg_guard := Ebinop Olt (Etempvar _i tint) (Etempvar _len tint) tint.
Definition fg_step := Sset _i (Ebinop Oadd (Etempvar _i tint) (Econst_int Int.one tint) tint).
Lemma fg_for_source : fg_for=Ssequence (Sset _i (Econst_int Int.one tint)) fg_loop.
Proof. reflexivity. Qed.
Lemma fg_loop_source : fg_loop=Sloop (Ssequence (Sifthenelse fg_guard Sskip Sbreak) fg_work) fg_step.
Proof. reflexivity. Qed.

Lemma eval_fg_guard e le m i len : 0<=i<=len -> len<=5 ->
 le!_i=Some (Vint (Int.repr i)) -> le!_len=Some (Vint (Int.repr len)) ->
 eval_expr secp_ge e le m fg_guard (Vint (if i <? len then Int.one else Int.zero)).
Proof.
 intros I Len Index Length;unfold fg_guard;eapply eval_Ebinop;
 [apply eval_Etempvar;exact Index|apply eval_Etempvar;exact Length|].
 change (Some (Val.of_bool (Int.lt (Int.repr i) (Int.repr len)))=
  Some (Vint (if i <? len then Int.one else Int.zero))).
 unfold Int.lt;rewrite !Int.signed_repr by
  (change Int.min_signed with (-2^31);change Int.max_signed with (2^31-1);lia).
 destruct (zlt i len),(Z.ltb_spec i len);try lia;reflexivity.
Qed.

Lemma exec_fg_step e le m i : 0<=i<5 -> le!_i=Some (Vint (Int.repr i)) ->
 Clight2.exec_stmt secp_ge e le m fg_step E0 (PTree.set _i (Vint (Int.repr (i+1))) le) m Out_normal.
Proof.
 intros Bound Index;unfold fg_step;apply exec_Sset;eapply eval_Ebinop;
 [apply eval_Etempvar;exact Index|constructor|].
 change (Some (Vint (Int.add (Int.repr i) Int.one))=Some (Vint (Int.repr (i+1)))).
 unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with (2^32-1);lia);reflexivity.
Qed.

Theorem exec_fg_loop_exit e le m len : 0<=len<=5 ->
 le!_i=Some (Vint (Int.repr len)) -> le!_len=Some (Vint (Int.repr len)) ->
 Clight2.exec_stmt secp_ge e le m fg_loop E0 le m Out_normal.
Proof.
 intros Bound Index Length;rewrite fg_loop_source.
 eapply exec_Sloop_stop1 with (out':=Out_break);[|constructor].
 eapply exec_Sseq_2;[|discriminate].
 eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
 - pose proof (eval_fg_guard e le m len len ltac:(lia) ltac:(lia) Index Length) as Guard.
   rewrite Z.ltb_irrefl in Guard;exact Guard.
 - reflexivity.
 - constructor.
Qed.

Lemma eval_fg_array e le m id b : le!id=Some (Vptr b Ptrofs.zero) ->
 eval_expr secp_ge e le m (fg_array id) (Vptr b Ptrofs.zero).
Proof.
 intro Ptr;destruct fg_array_layout as (co & Composite & Offset).
 eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.zero).
 - change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) at 1.
   unfold fg_array;eapply eval_Efield_struct with (co:=co) (delta:=0).
   + eapply eval_Elvalue.
     * apply eval_Ederef;apply eval_Etempvar;exact Ptr.
     * apply deref_loc_copy;reflexivity.
   + reflexivity.
   + exact Composite.
   + exact Offset.
 - apply deref_loc_reference;reflexivity.
Qed.

Lemma eval_fg_index e le m id b ix k : 0<=k<5 -> typeof ix=tint ->
 le!id=Some (Vptr b Ptrofs.zero) -> eval_expr secp_ge e le m ix (Vint (Int.repr k)) ->
 eval_lvalue secp_ge e le m (fg_index id ix) b (Ptrofs.repr (8*k)) Full.
Proof.
 intros Bound Ty Ptr Index.
 assert (Signed : Int.signed (Int.repr k)=k).
 { apply Int.signed_repr;change (-2147483648<=k<=2147483647);lia. }
 assert (K : 0<=k<=Ptrofs.max_unsigned) by (change Ptrofs.max_unsigned with (2^64-1);lia).
 assert (Addr : Ptrofs.add Ptrofs.zero
  (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr k)))=Ptrofs.repr (8*k)).
 { unfold Ptrofs.of_ints;rewrite Signed;rewrite Ptrofs.add_zero_l;
   unfold Ptrofs.mul;rewrite (Ptrofs.unsigned_repr k K);reflexivity. }
 unfold fg_index;apply eval_Ederef.
 eapply eval_Ebinop with (v1:=Vptr b Ptrofs.zero) (v2:=Vint (Int.repr k)).
 - apply eval_fg_array;exact Ptr.
 - exact Index.
 - rewrite Ty.
   change (Some (Vptr b (Ptrofs.add Ptrofs.zero
    (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints (Int.repr k)))))=
    Some (Vptr b (Ptrofs.repr (8*k))));rewrite Addr;reflexivity.
Qed.

Lemma eval_fg_previous e le m i : 1<=i<=5 -> le!_i=Some (Vint (Int.repr i)) ->
 eval_expr secp_ge e le m (Ebinop Osub (Etempvar _i tint) (Econst_int Int.one tint) tint)
  (Vint (Int.repr (i-1))).
Proof.
 intros Bound Index;eapply eval_Ebinop;
 [apply eval_Etempvar;exact Index|constructor|].
 change (Some (Vint (Int.sub (Int.repr i) Int.one))=Some (Vint (Int.repr (i-1)))).
 unfold Int.sub;rewrite Int.unsigned_repr by (change Int.max_unsigned with (2^32-1);lia).
 reflexivity.
Qed.

Lemma eval_fg_index_load e le m id b ix k value : 0<=k<5 -> typeof ix=tint ->
 le!id=Some (Vptr b Ptrofs.zero) -> eval_expr secp_ge e le m ix (Vint (Int.repr k)) ->
 Mem.load Mint64 m b (8*k)=Some (Vlong value) ->
 eval_expr secp_ge e le m (fg_index id ix) (Vlong value).
Proof.
 intros Bound Ty Ptr Index Load.
 eapply eval_Elvalue with (loc:=b) (ofs:=Ptrofs.repr (8*k));
 [apply eval_fg_index;assumption|].
 apply deref_loc_value with (chunk:=Mint64);[reflexivity|].
 unfold Mem.loadv;rewrite Ptrofs.unsigned_repr;
 [exact Load|change Ptrofs.max_unsigned with (2^64-1);lia].
Qed.

Theorem exec_fg_index_store e le m mf id b ix k src value :
 0<=k<5 -> typeof ix=tint -> typeof src=tulong ->
 le!id=Some (Vptr b Ptrofs.zero) -> eval_expr secp_ge e le m ix (Vint (Int.repr k)) ->
 eval_expr secp_ge e le m src (Vlong value) ->
 Mem.store Mint64 m b (8*k) (Vlong value)=Some mf ->
 Clight2.exec_stmt secp_ge e le m (Sassign (fg_index id ix) src) E0 le mf Out_normal.
Proof.
 intros Bound Ty Src Ptr Index Value Store.
 eapply exec_Sassign with (loc:=b) (ofs:=Ptrofs.repr (8*k)) (bf:=Full)
  (v2:=Vlong value) (v:=Vlong value).
 - apply eval_fg_index;assumption.
 - exact Value.
 - rewrite Src;reflexivity.
 - apply assign_loc_value with (chunk:=Mint64);[reflexivity|].
   unfold Mem.storev;rewrite Ptrofs.unsigned_repr;
   [exact Store|change Ptrofs.max_unsigned with (2^64-1);lia].
Qed.
