(** The original signed table-index arithmetic, including C division and
    scaled pointer addition. This does not assert correctness of a table. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values.
Require Import C.jet_secp_linkage C.jets_secp.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition table_magnitude (neg : bool) (n : Z) := if neg then -n else n.
Definition table_storage_index n := (Z.abs n-1)/2.
Definition table_magnitude_expr (neg : bool) :=
 if neg then Eunop Oneg (Etempvar _n tint) tint else Etempvar _n tint.
Definition table_index_expr neg :=
 Ebinop Odiv (Ebinop Osub (table_magnitude_expr neg) (Econst_int (Int.repr 1) tint) tint)
   (Econst_int (Int.repr 2) tint) tint.
Definition table_entry_expr neg :=
 Ebinop Oadd (Etempvar _pre (tptr (Tstruct __6125 noattr))) (table_index_expr neg)
   (tptr (Tstruct __6125 noattr)).

Lemma table_storage_index_bound n : 0<Z.abs n<16384 -> 0<=table_storage_index n<8192.
Proof.
 intro H;unfold table_storage_index;split;[apply Z.div_pos|apply Z.div_lt_upper_bound];lia.
Qed.

Lemma table_magnitude_abs neg n : 0<table_magnitude neg n<16384 ->
 table_magnitude neg n=Z.abs n /\ -16384<n<16384.
Proof.
 destruct neg;unfold table_magnitude;intro H.
 - rewrite Z.abs_neq by lia;split;lia.
 - rewrite Z.abs_eq by lia;split;lia.
Qed.

Lemma table_signed_repr n : -16384<=n<=16384 -> Int.signed (Int.repr n)=n.
Proof.
 intro H;apply Int.signed_repr.
 change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia.
Qed.

Lemma table_machine_division m a : 0<a<16384 ->
 sem_binary_operation secp_ge Odiv (Vint (Int.repr (a-1))) tint (Vint (Int.repr 2)) tint m=
 Some (Vint (Int.repr ((a-1)/2))).
Proof.
 intro H.
 change ((if Int.eq (Int.repr 2) Int.zero ||
   Int.eq (Int.repr (a-1)) (Int.repr Int.min_signed) && Int.eq (Int.repr 2) Int.mone
   then None else Some (Vint (Int.divs (Int.repr (a-1)) (Int.repr 2))))=
   Some (Vint (Int.repr ((a-1)/2)))).
 change (Int.eq (Int.repr 2) Int.zero) with false.
 change (Int.eq (Int.repr 2) Int.mone) with false.
 rewrite andb_false_r;cbn [orb].
 unfold Int.divs;rewrite !table_signed_repr by lia.
 rewrite Z.quot_div_nonneg by lia;reflexivity.
Qed.

Lemma eval_table_index_expr neg n e le m :
 le!_n=Some (Vint (Int.repr n)) -> 0<table_magnitude neg n<16384 ->
 eval_expr secp_ge e le m (table_index_expr neg) (Vint (Int.repr (table_storage_index n))).
Proof.
 intros HN Bound;destruct (table_magnitude_abs neg n Bound) as [Mag NB].
 assert (Magnitude : eval_expr secp_ge e le m (table_magnitude_expr neg)
   (Vint (Int.repr (table_magnitude neg n)))).
 { destruct neg;cbn [table_magnitude_expr table_magnitude].
   - eapply eval_Eunop;[apply eval_Etempvar;exact HN|].
     change (Some (Vint (Int.neg (Int.repr n)))=Some (Vint (Int.repr (-n)))).
     rewrite Int.neg_repr;reflexivity.
   - apply eval_Etempvar;exact HN. }
 assert (Sub : Int.sub (Int.repr (table_magnitude neg n)) (Int.repr 1)=
   Int.repr (table_magnitude neg n-1)).
 { rewrite Int.sub_signed,!table_signed_repr by lia;reflexivity. }
 unfold table_index_expr.
 unfold table_storage_index;rewrite <-Mag.
 eapply eval_Ebinop with (v1:=Vint (Int.repr (table_magnitude neg n-1))) (v2:=Vint (Int.repr 2)).
 - eapply eval_Ebinop;[exact Magnitude|constructor|].
   assert (HT : typeof (table_magnitude_expr neg)=tint) by (destruct neg;reflexivity).
   rewrite HT.
   change (Some (Vint (Int.sub (Int.repr (table_magnitude neg n)) (Int.repr 1)))=
     Some (Vint (Int.repr (table_magnitude neg n-1))));rewrite Sub;reflexivity.
 - constructor.
 - apply table_machine_division;exact Bound.
Qed.

Lemma eval_table_entry_expr neg n e le m b base :
 le!_n=Some (Vint (Int.repr n)) ->
 le!_pre=Some (Vptr b (Ptrofs.repr base)) ->
 0<table_magnitude neg n<16384 -> 0<=base ->
 base+64*table_storage_index n+64<=Ptrofs.max_unsigned ->
 eval_expr secp_ge e le m (table_entry_expr neg)
   (Vptr b (Ptrofs.repr (base+64*table_storage_index n))).
Proof.
 intros HN HP Bound Base Max.
 destruct (table_magnitude_abs neg n Bound) as [Mag NB].
 assert (Abs : 0<Z.abs n<16384) by (rewrite <-Mag;exact Bound).
 pose proof (table_storage_index_bound n Abs) as Index.
 unfold table_entry_expr.
 eapply eval_Ebinop.
 - apply eval_Etempvar;exact HP.
 - exact (eval_table_index_expr neg n e le m HN Bound).
 - change (Some (Vptr b (Ptrofs.add (Ptrofs.repr base)
     (Ptrofs.mul (Ptrofs.repr 64) (Ptrofs.repr (Int.signed (Int.repr (table_storage_index n)))))))=
     Some (Vptr b (Ptrofs.repr (base+64*table_storage_index n)))).
   rewrite table_signed_repr by lia.
   unfold Ptrofs.add,Ptrofs.mul.
   rewrite (Ptrofs.unsigned_repr base) by lia.
   rewrite (Ptrofs.unsigned_repr 64) by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
   rewrite (Ptrofs.unsigned_repr (table_storage_index n))
     by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
   rewrite Ptrofs.unsigned_repr by lia.
   reflexivity.
Qed.
