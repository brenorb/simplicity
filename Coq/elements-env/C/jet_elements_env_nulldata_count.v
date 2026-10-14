(** Execution of [countNullDataCodes(scriptPubKey)] (elements/env.c): the
    scan of a script that decides whether it is a TX_NULL_DATA script and
    counts its push operations.  The C function is related to a functional
    scanner [nd_count] over the bytes of the script; every early [return 0]
    of the C code (opcode above 0x60, truncated push length, truncated push
    data) is a [None] of the scanner. *)
From Coq Require Import ZArith List Lia PeanoNat Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_be32_exec.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_isfee.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation RBUF := (Tstruct _rawElementsBuffer noattr).
Local Notation SPK := (Ederef (Etempvar _scriptPubKey (tptr RBUF)) RBUF).
Local Notation RET0S := (Sreturn (Some (Econst_int (Int.repr 0) tint))).

Definition RET0 : outcome := Out_return (Some (Vint (Int.repr 0), tint)).

(** The statement, by its idioms. *)
Definition nd_len_set (tl : ident) : statement := Sset tl (Efield SPK _len tuint).

Definition nd_eof_stmt (tl : ident) : statement :=
  Ssequence (nd_len_set tl)
    (Sifthenelse (Ebinop Oeq (Etempvar tl tuint) (Etempvar _i tulong) tint) RET0S Sskip).

Definition nd_read_stmt (tt tp tb : ident) (last : statement) : statement :=
  Ssequence
    (Ssequence (Sset tt (Etempvar _i tulong))
       (Sset _i (Ebinop Oadd (Etempvar tt tulong) (Econst_int (Int.repr 1) tint) tulong)))
    (Ssequence (Sset tp (Efield SPK _buf (tptr tuchar)))
       (Ssequence
          (Sset tb (Ederef (Ebinop Oadd (Etempvar tp (tptr tuchar)) (Etempvar tt tulong) (tptr tuchar)) tuchar))
          last)).

Definition nd_skip_set1 (tb : ident) : statement := Sset _skip (Ecast (Etempvar tb tuchar) tulong).
Definition nd_skip_add (tb : ident) (k : Z) : statement :=
  Sset _skip
    (Ebinop Oadd (Etempvar _skip tulong)
       (Ebinop Oshl (Ecast (Etempvar tb tuchar) tulong) (Econst_int (Int.repr k) tint) tulong) tulong).

Definition nd_skipcalc : statement :=
  Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 76) tint) tint)
    (Sset _skip (Ecast (Etempvar _code tuchar) tulong))
    (Sifthenelse (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr 79) tint) tint)
      (Ssequence (nd_eof_stmt _t'19)
        (Ssequence (nd_read_stmt _t'3 _t'17 _t'18 (nd_skip_set1 _t'18))
          (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 77) tint) (Etempvar _code tuchar) tint)
            (Ssequence (nd_eof_stmt _t'16)
              (Ssequence (nd_read_stmt _t'4 _t'14 _t'15 (nd_skip_add _t'15 8))
                (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 78) tint) (Etempvar _code tuchar) tint)
                  (Ssequence (nd_eof_stmt _t'13)
                    (Ssequence (nd_read_stmt _t'5 _t'11 _t'12 (nd_skip_add _t'12 16))
                      (Ssequence (nd_eof_stmt _t'10)
                        (nd_read_stmt _t'6 _t'8 _t'9 (nd_skip_add _t'9 24)))))
                  Sskip)))
            Sskip)))
      Sskip).

Definition nd_tail : statement :=
  Ssequence
    (Ssequence (nd_len_set _t'7)
       (Sifthenelse
          (Ebinop Olt (Ebinop Osub (Etempvar _t'7 tuint) (Etempvar _i tulong) tulong)
             (Etempvar _skip tulong) tint)
          RET0S Sskip))
    (Ssequence (Sset _i (Ebinop Oadd (Etempvar _i tulong) (Etempvar _skip tulong) tulong))
       (Sset _result (Ebinop Oadd (Etempvar _result tulong) (Econst_int (Int.repr 1) tint) tulong))).

Definition nd_s1 : statement :=
  Ssequence
    (Ssequence (nd_len_set _t'22)
       (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _t'22 tuint) tint) Sskip Sbreak))
    (Ssequence (Sset _skip (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (nd_read_stmt _t'2 _t'20 _t'21 (Sset _code (Ecast (Etempvar _t'21 tuchar) tuchar)))
        (Ssequence
          (Sifthenelse (Ebinop Olt (Econst_int (Int.repr 96) tint) (Etempvar _code tuchar) tint) RET0S Sskip)
          (Ssequence nd_skipcalc nd_tail)))).

Definition nd_head : statement :=
  Ssequence
    (Ssequence (nd_len_set _t'23)
       (Sifthenelse (Ebinop Oeq (Econst_int (Int.repr 0) tint) (Etempvar _t'23 tuint) tint)
          (Sset _t'1 (Econst_int (Int.repr 1) tint))
          (Ssequence (Sset _t'24 (Efield SPK _buf (tptr tuchar)))
             (Ssequence
                (Sset _t'25
                   (Ederef (Ebinop Oadd (Etempvar _t'24 (tptr tuchar)) (Econst_int (Int.repr 0) tint)
                              (tptr tuchar)) tuchar))
                (Sset _t'1
                   (Ecast (Ebinop One (Econst_int (Int.repr 106) tint) (Etempvar _t'25 tuchar) tint)
                      tbool))))))
    (Sifthenelse (Etempvar _t'1 tint) RET0S Sskip).

Lemma nd_body_shape :
  fn_body f_countNullDataCodes =
    Ssequence nd_head
      (Ssequence (Sset _result (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Ssequence
          (Ssequence (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong)) (Sloop nd_s1 Sskip))
          (Sreturn (Some (Etempvar _result tulong))))).
Proof. reflexivity. Qed.

Local Opaque sha_ge.

(** Arithmetic of the machine comparisons on small values. *)
Lemma nd_i64_eq a b : 0 <= a <= 4294967296 -> 0 <= b <= 4294967296 ->
  Int64.eq (Int64.repr a) (Int64.repr b) = (a =? b).
Proof.
  intros Ha Hb. unfold Int64.eq.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zeq a b) as [E|E]; destruct (Z.eqb_spec a b); try reflexivity; contradiction.
Qed.

Lemma nd_i64_ltu a b : 0 <= a <= 8589934592 -> 0 <= b <= 8589934592 ->
  Int64.ltu (Int64.repr a) (Int64.repr b) = (a <? b).
Proof.
  intros Ha Hb. unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zlt a b) as [E|E]; destruct (Z.ltb_spec a b); try reflexivity; lia.
Qed.

Lemma nd_i64_add a b : 0 <= a <= 8589934592 -> 0 <= b <= 8589934592 ->
  Int64.add (Int64.repr a) (Int64.repr b) = Int64.repr (a + b).
Proof.
  intros Ha Hb. unfold Int64.add.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

Lemma nd_i64_sub a b : 0 <= b <= a -> a <= 8589934592 ->
  Int64.sub (Int64.repr a) (Int64.repr b) = Int64.repr (a - b).
Proof.
  intros Hb Ha. unfold Int64.sub.
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). reflexivity.
Qed.

Lemma nd_i64_shl b k : 0 <= b < 256 -> 0 <= k <= 24 ->
  Int64.shl (Int64.repr b) (Int64.repr (Int.unsigned (Int.repr k))) = Int64.repr (b * 2 ^ k).
Proof.
  intros Hb Hk. unfold Int64.shl.
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  rewrite !Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma nd_byte_signed c : 0 <= Int.unsigned c < 256 -> Int.signed c = Int.unsigned c.
Proof.
  intros Hc. unfold Int.signed.
  destruct (zlt (Int.unsigned c) Int.half_modulus) as [_|HH];
    [reflexivity|change Int.half_modulus with 2147483648 in HH; lia].
Qed.

Lemma nd_int_lt_l k c : 0 <= k < 256 -> 0 <= Int.unsigned c < 256 ->
  Int.lt (Int.repr k) c = (k <? Int.unsigned c).
Proof.
  intros Hk Hc. unfold Int.lt. rewrite (nd_byte_signed c) by exact Hc.
  rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  destruct (zlt k (Int.unsigned c)); destruct (Z.ltb_spec k (Int.unsigned c)); try reflexivity; lia.
Qed.

Lemma nd_int_lt_r k c : 0 <= k < 256 -> 0 <= Int.unsigned c < 256 ->
  Int.lt c (Int.repr k) = (Int.unsigned c <? k).
Proof.
  intros Hk Hc. unfold Int.lt. rewrite (nd_byte_signed c) by exact Hc.
  rewrite Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
  destruct (zlt (Int.unsigned c) k); destruct (Z.ltb_spec (Int.unsigned c) k); try reflexivity; lia.
Qed.

Lemma nd_int_eq k c : 0 <= k < 256 -> Int.eq (Int.repr k) c = (k =? Int.unsigned c).
Proof.
  intros Hk. unfold Int.eq. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  destruct (zeq k (Int.unsigned c)); destruct (Z.eqb_spec k (Int.unsigned c)); try reflexivity; contradiction.
Qed.

Lemma nd_load_byte m b ofs x :
  Mem.load Mint8unsigned m b ofs = Some (Vint x) -> Int.zero_ext 8 x = x /\ 0 <= Int.unsigned x < 256.
Proof.
  intros HL. pose proof (Mem.load_cast _ _ _ _ _ HL) as HC. cbn in HC. injection HC as HC.
  split; [symmetry; exact HC|]. rewrite HC. change 256 with (two_p 8). apply Int.zero_ext_range.
  change Int.zwordsize with 32. lia.
Qed.

Lemma nd_index_offset o i :
  0 <= i -> Ptrofs.unsigned o + i <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 1) (Ptrofs.of_int64 (Int64.repr i)))) =
    Ptrofs.unsigned o + i.
Proof.
  intros Hi Hlt. pose proof (Ptrofs.unsigned_range o) as Ho.
  change Ptrofs.max_unsigned with 18446744073709551615 in Hlt.
  assert (Hof : Ptrofs.of_int64 (Int64.repr i) = Ptrofs.repr i).
  { unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr; [reflexivity|].
    change Int64.max_unsigned with 18446744073709551615. lia. }
  rewrite Hof, Ptrofs.mul_commut, Ptrofs.mul_one.
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr i) by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  apply Ptrofs.unsigned_repr. change Ptrofs.max_unsigned with 18446744073709551615. lia.
Qed.

Lemma nd_bool_val (b : bool) m : bool_val (Val.of_bool b) tint m = Some b.
Proof. destruct b; reflexivity. Qed.

Section CountNullData.
(** The lemmas hold in any local environment [e]: [parseNullData] reuses
    the script-reading idioms with its own locals. *)
Variable e : env.
Variables (m : mem) (bsp : block) (osp : Z) (len : int) (bb : block) (ob : ptrofs) (bs : list int).
Hypothesis Hosp : 0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned.
Hypothesis HLen : Mem.load Mint32 m bsp (osp + 8) = Some (Vint len).

Let L : Z := Int.unsigned len.
Let spv := Vptr bsp (Ptrofs.repr osp).

Hypothesis HBuf : 0 < L -> Mem.load Mptr m bsp osp = Some (Vptr bb ob).
Hypothesis HobM : Ptrofs.unsigned ob + L <= Ptrofs.max_unsigned.
Hypothesis HBs : forall i, 0 <= i < L ->
  Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob + i) = Some (Vint (nth (Z.to_nat i) bs Int.zero)).

Definition nd_b (i : Z) : int := nth (Z.to_nat i) bs Int.zero.
Definition nd_byte (i : Z) : Z := Int.unsigned (nd_b i).

Lemma nd_L : 0 <= L <= 4294967295.
Proof. unfold L. pose proof (Int.unsigned_range_2 len) as H. change Int.max_unsigned with 4294967295 in H. exact H. Qed.

Lemma nd_byte_range i : 0 <= i < L -> 0 <= nd_byte i < 256.
Proof. intros Hi. exact (proj2 (nd_load_byte _ _ _ _ (HBs i Hi))). Qed.

(** The functional scanner. *)
Definition nd_skip (code i : Z) : option (Z * Z) :=
  if code <? 76 then Some (i, code)
  else if code <? 79 then
    if L =? i then None else
    if 77 <=? code then
      if L =? i + 1 then None else
      if 78 <=? code then
        if L =? i + 1 + 1 then None else
        if L =? i + 1 + 1 + 1 then None else
        Some (i + 1 + 1 + 1 + 1,
              nd_byte i + nd_byte (i + 1) * 2 ^ 8 + nd_byte (i + 1 + 1) * 2 ^ 16 + nd_byte (i + 1 + 1 + 1) * 2 ^ 24)
      else Some (i + 1 + 1, nd_byte i + nd_byte (i + 1) * 2 ^ 8)
    else Some (i + 1, nd_byte i)
  else Some (i, 0).

Definition nd_op (i : Z) : option Z :=
  if 96 <? nd_byte i then None
  else match nd_skip (nd_byte i) (i + 1) with
       | None => None
       | Some (i', skip) => if L - i' <? skip then None else Some (i' + skip)
       end.

Fixpoint nd_loop (fuel : nat) (i acc : Z) : option Z :=
  if i <? L then
    match fuel with
    | O => None
    | S f => match nd_op i with
             | None => None
             | Some i' => nd_loop f i' (acc + 1)
             end
    end
  else Some acc.

Definition nd_count : Z :=
  if L =? 0 then 0
  else if negb (106 =? nd_byte 0) then 0
  else match nd_loop (Z.to_nat L) 1 0 with Some r => r | None => 0 end.

(** Temporaries that leave the scanner state alone. *)
Definition nd_keeps (id : ident) : Prop :=
  forall (v : val) (le : temp_env),
    (PTree.set id v le)!_i = le!_i /\ (PTree.set id v le)!_code = le!_code /\
    (PTree.set id v le)!_skip = le!_skip /\ (PTree.set id v le)!_result = le!_result /\
    (PTree.set id v le)!_scriptPubKey = le!_scriptPubKey.

Definition nd_core (le : temp_env) (i acc : Z) : Prop :=
  le!_i = Some (Vlong (Int64.repr i)) /\ le!_result = Some (Vlong (Int64.repr acc)) /\
  le!_scriptPubKey = Some spv.

Definition nd_st (le : temp_env) (i : Z) (c : int) (skip acc : Z) : Prop :=
  nd_core le i acc /\ le!_code = Some (Vint c) /\ le!_skip = Some (Vlong (Int64.repr skip)).

Lemma nd_st_set id v le i c s a : nd_keeps id -> nd_st le i c s a -> nd_st (PTree.set id v le) i c s a.
Proof.
  intros HK ((Hi & Hr & Hs) & Hc & Hk). destruct (HK v le) as (K1 & K2 & K3 & K4 & K5).
  unfold nd_st, nd_core. rewrite K1, K2, K3, K4, K5. repeat split; assumption.
Qed.

Lemma nd_seq_ret le s1 s2 le1 :
  Clight2.exec_stmt sha_ge e le m s1 E0 le1 m RET0 ->
  Clight2.exec_stmt sha_ge e le m (Ssequence s1 s2) E0 le1 m RET0.
Proof. intros H. eapply exec_Sseq_2; [exact H|discriminate]. Qed.

Lemma nd_seq le s1 s2 le1 le2 out :
  Clight2.exec_stmt sha_ge e le m s1 E0 le1 m Out_normal ->
  Clight2.exec_stmt sha_ge e le1 m s2 E0 le2 m out ->
  Clight2.exec_stmt sha_ge e le m (Ssequence s1 s2) E0 le2 m out.
Proof. intros H1 H2. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); eassumption. Qed.

Lemma nd_if le a (b : bool) s1 s2 le' out :
  eval_expr sha_ge e le m a (Val.of_bool b) -> typeof a = tint ->
  Clight2.exec_stmt sha_ge e le m (if b then s1 else s2) E0 le' m out ->
  Clight2.exec_stmt sha_ge e le m (Sifthenelse a s1 s2) E0 le' m out.
Proof.
  intros HE HT HX. eapply exec_Sifthenelse with (v1 := Val.of_bool b) (b := b);
    [exact HE|rewrite HT; apply nd_bool_val|exact HX].
Qed.

Lemma nd_ret0 le : Clight2.exec_stmt sha_ge e le m RET0S E0 le m RET0.
Proof. apply exec_Sreturn_some. apply eval_Econst_int. Qed.

(** Expressions. *)
Lemma nd_ev_len le :
  le!_scriptPubKey = Some spv ->
  eval_expr sha_ge e le m (Efield SPK _len tuint) (Vint len).
Proof.
  intros HS. eapply eval_envu_field_value;
    [reflexivity|exact envu_rawElementsBuffer_len|reflexivity|apply eval_envu_deref_struct; exact HS|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|exact HLen].
Qed.

Lemma nd_ev_buf le :
  le!_scriptPubKey = Some spv -> 0 < L ->
  eval_expr sha_ge e le m (Efield SPK _buf (tptr tuchar)) (Vptr bb ob).
Proof.
  intros HS HL. eapply eval_envu_field_value;
    [reflexivity|exact envu_rawElementsBuffer_buf|reflexivity|apply eval_envu_deref_struct; exact HS|].
  rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|]. rewrite Z.add_0_r. exact (HBuf HL).
Qed.

Lemma nd_ev_byte le tp tt i :
  le!tp = Some (Vptr bb ob) -> le!tt = Some (Vlong (Int64.repr i)) -> 0 <= i < L ->
  eval_expr sha_ge e le m
    (Ederef (Ebinop Oadd (Etempvar tp (tptr tuchar)) (Etempvar tt tulong) (tptr tuchar)) tuchar)
    (Vint (nd_b i)).
Proof.
  intros Hp Ht Hi. eapply eval_Elvalue.
  - eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact Hp|apply eval_Etempvar; exact Ht|reflexivity].
  - eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
    rewrite nd_index_offset by lia. exact (HBs i Hi).
Qed.

Lemma nd_ev_len_eq_i le tl i :
  le!tl = Some (Vint len) -> le!_i = Some (Vlong (Int64.repr i)) -> 0 <= i <= L ->
  eval_expr sha_ge e le m (Ebinop Oeq (Etempvar tl tuint) (Etempvar _i tulong) tint)
    (Val.of_bool (L =? i)).
Proof.
  intros Hl Hi Hr. pose proof nd_L.
  eapply eval_Ebinop; [apply eval_Etempvar; exact Hl|apply eval_Etempvar; exact Hi|].
  change (Some (Val.of_bool (Int64.eq (Int64.repr (Int.unsigned len)) (Int64.repr i))) =
          Some (Val.of_bool (L =? i))).
  fold L. rewrite nd_i64_eq by lia. reflexivity.
Qed.

Lemma nd_ev_code_lt le c k :
  le!_code = Some (Vint c) -> 0 <= k < 256 -> 0 <= Int.unsigned c < 256 ->
  eval_expr sha_ge e le m (Ebinop Olt (Etempvar _code tuchar) (Econst_int (Int.repr k) tint) tint)
    (Val.of_bool (Int.unsigned c <? k)).
Proof.
  intros Hc Hk Hr. eapply eval_Ebinop; [apply eval_Etempvar; exact Hc|apply eval_Econst_int|].
  change (Some (Val.of_bool (Int.lt c (Int.repr k))) = Some (Val.of_bool (Int.unsigned c <? k))).
  rewrite nd_int_lt_r by assumption. reflexivity.
Qed.

Lemma nd_ev_lt_code le c k :
  le!_code = Some (Vint c) -> 0 <= k < 256 -> 0 <= Int.unsigned c < 256 ->
  eval_expr sha_ge e le m (Ebinop Olt (Econst_int (Int.repr k) tint) (Etempvar _code tuchar) tint)
    (Val.of_bool (k <? Int.unsigned c)).
Proof.
  intros Hc Hk Hr. eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hc|].
  change (Some (Val.of_bool (Int.lt (Int.repr k) c)) = Some (Val.of_bool (k <? Int.unsigned c))).
  rewrite nd_int_lt_l by assumption. reflexivity.
Qed.

Lemma nd_ev_le_code le c k :
  le!_code = Some (Vint c) -> 0 <= k < 256 -> 0 <= Int.unsigned c < 256 ->
  eval_expr sha_ge e le m (Ebinop Ole (Econst_int (Int.repr k) tint) (Etempvar _code tuchar) tint)
    (Val.of_bool (k <=? Int.unsigned c)).
Proof.
  intros Hc Hk Hr. eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact Hc|].
  change (Some (Val.of_bool (negb (Int.lt c (Int.repr k)))) = Some (Val.of_bool (k <=? Int.unsigned c))).
  rewrite nd_int_lt_r by assumption.
  destruct (Z.ltb_spec (Int.unsigned c) k); destruct (Z.leb_spec k (Int.unsigned c)); try reflexivity; lia.
Qed.

(** [if (len == i) return 0;] *)
Lemma nd_eof_exec tl le i c s a :
  nd_keeps tl -> nd_st le i c s a -> 0 <= i <= L ->
  exists le',
    Clight2.exec_stmt sha_ge e le m (nd_eof_stmt tl) E0 le' m
      (if L =? i then RET0 else Out_normal) /\
    nd_st le' i c s a.
Proof.
  intros HK HS Hi. pose proof HS as ((Hli & Hr & Hsp) & Hc & Hk).
  exists (PTree.set tl (Vint len) le). split; [|apply nd_st_set; assumption].
  unfold nd_eof_stmt, nd_len_set.
  eapply nd_seq; [apply exec_Sset; apply nd_ev_len; exact Hsp|].
  eapply nd_if with (b := L =? i).
  - apply nd_ev_len_eq_i; [apply PTree.gss| |exact Hi].
    rewrite (proj1 (HK (Vint len) le)). exact Hli.
  - reflexivity.
  - destruct (L =? i); [apply nd_ret0|apply exec_Sskip].
Qed.

(** Reading the byte at [i] and advancing [i]. *)
Definition nd_trip (tt tp tb : ident) : Prop :=
  nd_keeps tt /\ nd_keeps tp /\ nd_keeps tb /\
  (forall (v : val) (le : temp_env), (PTree.set tp v le)!tt = le!tt) /\
  (forall (v : val) (le : temp_env), (PTree.set _i v le)!tt = le!tt).

Definition nd_read_le (tt tp tb : ident) (le : temp_env) (i : Z) : temp_env :=
  PTree.set tb (Vint (nd_b i)) (PTree.set tp (Vptr bb ob)
    (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le))).

Lemma nd_read_exec tt tp tb last le i le' out :
  nd_trip tt tp tb ->
  le!_i = Some (Vlong (Int64.repr i)) -> le!_scriptPubKey = Some spv -> 0 <= i < L ->
  Clight2.exec_stmt sha_ge e (nd_read_le tt tp tb le i) m last E0 le' m out ->
  Clight2.exec_stmt sha_ge e le m (nd_read_stmt tt tp tb last) E0 le' m out.
Proof.
  intros (Kt & Kp & Kb & Hpt & Hit) Hli Hsp Hi HX. pose proof nd_L.
  unfold nd_read_stmt, nd_read_le in *.
  set (le1 := PTree.set tt (Vlong (Int64.repr i)) le) in *.
  set (le2 := PTree.set _i (Vlong (Int64.repr (i + 1))) le1) in *.
  set (le3 := PTree.set tp (Vptr bb ob) le2) in *.
  eapply nd_seq with (le1 := le2).
  { eapply nd_seq with (le1 := le1).
    - apply exec_Sset. apply eval_Etempvar. exact Hli.
    - apply exec_Sset. eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss|apply eval_Econst_int|].
      rewrite <- (nd_i64_add i 1) by lia. reflexivity. }
  eapply nd_seq with (le1 := le3).
  { apply exec_Sset. apply nd_ev_buf; [|lia].
    unfold le2, le1. rewrite PTree.gso by discriminate.
    rewrite (proj2 (proj2 (proj2 (proj2 (Kt (Vlong (Int64.repr i)) le))))). exact Hsp. }
  eapply nd_seq; [|exact HX].
  apply exec_Sset. apply nd_ev_byte; [apply PTree.gss| |exact Hi].
  unfold le3, le2, le1. rewrite Hpt, Hit. apply PTree.gss.
Qed.

Lemma nd_read_core tt tp tb le i a :
  nd_trip tt tp tb -> nd_core le i a ->
  nd_core (nd_read_le tt tp tb le i) (i + 1) a.
Proof.
  intros (Kt & Kp & Kb & Hpt & Hit) (Hli & Hr & Hsp). unfold nd_read_le, nd_core.
  destruct (Kb (Vint (nd_b i)) (PTree.set tp (Vptr bb ob)
    (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le)))) as (B1 & _ & _ & B4 & B5).
  destruct (Kp (Vptr bb ob)
    (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le))) as (P1 & _ & _ & P4 & P5).
  destruct (Kt (Vlong (Int64.repr i)) le) as (_ & _ & _ & T4 & T5).
  rewrite B1, B4, B5, P1, P4, P5. split; [apply PTree.gss|].
  rewrite !(PTree.gso _ _ (i := _result)) by discriminate.
  rewrite !(PTree.gso _ _ (i := _scriptPubKey)) by discriminate.
  rewrite T4, T5. split; assumption.
Qed.

Lemma nd_read_other tt tp tb le i :
  nd_trip tt tp tb ->
  (nd_read_le tt tp tb le i)!_code = le!_code /\ (nd_read_le tt tp tb le i)!_skip = le!_skip.
Proof.
  intros (Kt & Kp & Kb & Hpt & Hit). unfold nd_read_le.
  destruct (Kb (Vint (nd_b i)) (PTree.set tp (Vptr bb ob)
    (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le)))) as (_ & B2 & B3 & _ & _).
  destruct (Kp (Vptr bb ob)
    (PTree.set _i (Vlong (Int64.repr (i + 1))) (PTree.set tt (Vlong (Int64.repr i)) le))) as (_ & P2 & P3 & _ & _).
  destruct (Kt (Vlong (Int64.repr i)) le) as (_ & T2 & T3 & _ & _).
  rewrite B2, B3, P2, P3.
  rewrite (PTree.gso _ _ (i := _code)) by discriminate.
  rewrite (PTree.gso _ _ (i := _skip)) by discriminate.
  rewrite T2, T3. split; reflexivity.
Qed.

Lemma nd_read_tb tt tp tb le i : (nd_read_le tt tp tb le i)!tb = Some (Vint (nd_b i)).
Proof. apply PTree.gss. Qed.

(** [skip = buf[i++]]. *)
Lemma nd_read_skip1 tt tp tb le i c s a :
  nd_trip tt tp tb -> nd_st le i c s a -> 0 <= i < L ->
  exists le',
    Clight2.exec_stmt sha_ge e le m (nd_read_stmt tt tp tb (nd_skip_set1 tb)) E0 le' m Out_normal /\
    nd_st le' (i + 1) c (nd_byte i) a.
Proof.
  intros HT (HC & Hc & Hk) Hi. pose proof HC as (Hli & Hr & Hsp).
  pose proof (nd_read_core tt tp tb le i a HT HC) as (C1 & C2 & C3).
  destruct (nd_read_other tt tp tb le i HT) as (O1 & O2).
  exists (PTree.set _skip (Vlong (Int64.repr (nd_byte i))) (nd_read_le tt tp tb le i)). split.
  - eapply nd_read_exec; [exact HT|exact Hli|exact Hsp|exact Hi|].
    apply exec_Sset. eapply eval_Ecast; [apply eval_Etempvar; apply nd_read_tb|reflexivity].
  - unfold nd_st, nd_core. rewrite PTree.gss. rewrite !PTree.gso by discriminate.
    rewrite O1. repeat split; assumption.
Qed.

(** [skip += (uint_fast32_t)(buf[i++]) << k]. *)
Lemma nd_read_skipk tt tp tb k le i c s a :
  nd_trip tt tp tb -> nd_st le i c s a -> 0 <= i < L -> 0 <= s < 4294967296 -> 8 <= k <= 24 ->
  exists le',
    Clight2.exec_stmt sha_ge e le m (nd_read_stmt tt tp tb (nd_skip_add tb k)) E0 le' m Out_normal /\
    nd_st le' (i + 1) c (s + nd_byte i * 2 ^ k) a.
Proof.
  intros HT (HC & Hc & Hk) Hi Hs Hkr. pose proof HC as (Hli & Hr & Hsp).
  pose proof (nd_read_core tt tp tb le i a HT HC) as (C1 & C2 & C3).
  destruct (nd_read_other tt tp tb le i HT) as (O1 & O2).
  pose proof (nd_byte_range i Hi) as HB.
  assert (HP : 0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia|apply Z.pow_le_mono_r; lia]).
  change (2 ^ 24) with 16777216 in HP.
  exists (PTree.set _skip (Vlong (Int64.repr (s + nd_byte i * 2 ^ k))) (nd_read_le tt tp tb le i)). split.
  - eapply nd_read_exec; [exact HT|exact Hli|exact Hsp|exact Hi|].
    apply exec_Sset.
    eapply eval_Ebinop with (v1 := Vlong (Int64.repr s)) (v2 := Vlong (Int64.repr (nd_byte i * 2 ^ k))).
    + apply eval_Etempvar. rewrite O2. exact Hk.
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr (nd_byte i))) (v2 := Vint (Int.repr k)).
      * eapply eval_Ecast; [apply eval_Etempvar; apply nd_read_tb|reflexivity].
      * apply eval_Econst_int.
      * unfold sem_binary_operation, sem_shl, sem_shift. cbn [classify_shift typeof tulong tint typeconv remove_attributes].
        assert (HLt : Int.ltu (Int.repr k) Int64.iwordsize' = true).
        { unfold Int.ltu. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
          change (Int.unsigned Int64.iwordsize') with 64. apply zlt_true. lia. }
        cbn. rewrite HLt. rewrite nd_i64_shl by lia. reflexivity.
    + rewrite <- (nd_i64_add s (nd_byte i * 2 ^ k)) by nia. reflexivity.
  - unfold nd_st, nd_core. rewrite PTree.gss. rewrite !PTree.gso by discriminate.
    rewrite O1. repeat split; assumption.
Qed.
Ltac nd_keeps_tac :=
  unfold nd_keeps; intros v le; rewrite !PTree.gso by discriminate; repeat split; reflexivity.
Ltac nd_trip_tac :=
  unfold nd_trip, nd_keeps; repeat split; intros;
  rewrite !PTree.gso by discriminate; repeat split; reflexivity.

Lemma nd_keeps_t19 : nd_keeps _t'19. Proof. nd_keeps_tac. Qed.
Lemma nd_keeps_t16 : nd_keeps _t'16. Proof. nd_keeps_tac. Qed.
Lemma nd_keeps_t13 : nd_keeps _t'13. Proof. nd_keeps_tac. Qed.
Lemma nd_keeps_t10 : nd_keeps _t'10. Proof. nd_keeps_tac. Qed.
Lemma nd_trip_1 : nd_trip _t'3 _t'17 _t'18. Proof. nd_trip_tac. Qed.
Lemma nd_trip_2 : nd_trip _t'4 _t'14 _t'15. Proof. nd_trip_tac. Qed.
Lemma nd_trip_3 : nd_trip _t'5 _t'11 _t'12. Proof. nd_trip_tac. Qed.
Lemma nd_trip_4 : nd_trip _t'6 _t'8 _t'9. Proof. nd_trip_tac. Qed.
Lemma nd_trip_c : nd_trip _t'2 _t'20 _t'21. Proof. nd_trip_tac. Qed.

(** The push-length decoding. *)
Lemma nd_skipcalc_exec le i c a :
  nd_st le i c 0 a -> 1 <= i <= L -> 0 <= Int.unsigned c < 256 ->
  match nd_skip (Int.unsigned c) i with
  | Some (i', s') =>
      exists le', Clight2.exec_stmt sha_ge e le m nd_skipcalc E0 le' m Out_normal /\
        nd_st le' i' c s' a /\ i <= i' <= L /\ 0 <= s' < 4294967296
  | None => exists le', Clight2.exec_stmt sha_ge e le m nd_skipcalc E0 le' m RET0
  end.
Proof.
  intros HS Hi Hc. pose proof HS as ((Hli & Hr & Hsp) & Hcd & Hk). pose proof nd_L as HLr.
  pose proof (nd_ev_code_lt le c 76 Hcd ltac:(lia) Hc) as E1.
  pose proof (nd_ev_code_lt le c 79 Hcd ltac:(lia) Hc) as E2.
  unfold nd_skip, nd_skipcalc.
  destruct (Int.unsigned c <? 76) eqn:E76.
  { exists (PTree.set _skip (Vlong (Int64.repr (Int.unsigned c))) le). split; [|split; [|lia]].
    - eapply nd_if; [exact E1|reflexivity|].
      apply exec_Sset. eapply eval_Ecast; [apply eval_Etempvar; exact Hcd|reflexivity].
    - unfold nd_st, nd_core. rewrite PTree.gss, !PTree.gso by discriminate. repeat split; assumption. }
  destruct (Int.unsigned c <? 79) eqn:E79.
  2: { exists le. split; [|split; [exact HS|lia]].
       eapply nd_if; [exact E1|reflexivity|]. eapply nd_if; [exact E2|reflexivity|]. apply exec_Sskip. }
  assert (HOuter : forall le' out,
    Clight2.exec_stmt sha_ge e le m
      (Ssequence (nd_eof_stmt _t'19)
        (Ssequence (nd_read_stmt _t'3 _t'17 _t'18 (nd_skip_set1 _t'18))
          (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 77) tint) (Etempvar _code tuchar) tint)
            (Ssequence (nd_eof_stmt _t'16)
              (Ssequence (nd_read_stmt _t'4 _t'14 _t'15 (nd_skip_add _t'15 8))
                (Sifthenelse (Ebinop Ole (Econst_int (Int.repr 78) tint) (Etempvar _code tuchar) tint)
                  (Ssequence (nd_eof_stmt _t'13)
                    (Ssequence (nd_read_stmt _t'5 _t'11 _t'12 (nd_skip_add _t'12 16))
                      (Ssequence (nd_eof_stmt _t'10)
                        (nd_read_stmt _t'6 _t'8 _t'9 (nd_skip_add _t'9 24)))))
                  Sskip)))
            Sskip))) E0 le' m out ->
    Clight2.exec_stmt sha_ge e le m nd_skipcalc E0 le' m out).
  { intros le' out HX. unfold nd_skipcalc.
    eapply nd_if; [exact E1|reflexivity|]. eapply nd_if; [exact E2|reflexivity|]. exact HX. }
  (* one length byte *)
  destruct (nd_eof_exec _t'19 le i c 0 a nd_keeps_t19 HS ltac:(lia)) as (le1 & X1 & S1).
  destruct (L =? i) eqn:EL1.
  { exists le1. apply HOuter. apply nd_seq_ret. exact X1. }
  apply Z.eqb_neq in EL1.
  destruct (nd_read_skip1 _t'3 _t'17 _t'18 le1 i c 0 a nd_trip_1 S1 ltac:(lia)) as (le2 & X2 & S2).
  pose proof (nd_byte_range i ltac:(lia)) as B1.
  pose proof (nd_ev_le_code le2 c 77 (proj1 (proj2 S2)) ltac:(lia) Hc) as E3.
  destruct (77 <=? Int.unsigned c) eqn:E77.
  2: { exists le2. split; [|split; [exact S2|lia]].
       apply HOuter. eapply nd_seq; [exact X1|]. eapply nd_seq; [exact X2|].
       eapply nd_if; [exact E3|reflexivity|]. apply exec_Sskip. }
  (* two length bytes *)
  destruct (nd_eof_exec _t'16 le2 (i + 1) c (nd_byte i) a nd_keeps_t16 S2 ltac:(lia)) as (le3 & X3 & S3).
  destruct (L =? i + 1) eqn:EL2.
  { exists le3. apply HOuter. eapply nd_seq; [exact X1|]. eapply nd_seq; [exact X2|].
    eapply nd_if; [exact E3|reflexivity|]. apply nd_seq_ret. exact X3. }
  apply Z.eqb_neq in EL2.
  destruct (nd_read_skipk _t'4 _t'14 _t'15 8 le3 (i + 1) c (nd_byte i) a nd_trip_2 S3
    ltac:(lia) ltac:(lia) ltac:(lia)) as (le4 & X4 & S4).
  pose proof (nd_byte_range (i + 1) ltac:(lia)) as B2.
  pose proof (nd_ev_le_code le4 c 78 (proj1 (proj2 S4)) ltac:(lia) Hc) as E4.
  destruct (78 <=? Int.unsigned c) eqn:E78.
  2: { exists le4. split; [|split; [exact S4|change (2 ^ 8) with 256; lia]].
       apply HOuter. eapply nd_seq; [exact X1|]. eapply nd_seq; [exact X2|].
       eapply nd_if; [exact E3|reflexivity|]. eapply nd_seq; [exact X3|]. eapply nd_seq; [exact X4|].
       eapply nd_if; [exact E4|reflexivity|]. apply exec_Sskip. }
  (* four length bytes *)
  destruct (nd_eof_exec _t'13 le4 (i + 1 + 1) c (nd_byte i + nd_byte (i + 1) * 2 ^ 8) a nd_keeps_t13 S4
    ltac:(lia)) as (le5 & X5 & S5).
  destruct (L =? i + 1 + 1) eqn:EL3.
  { exists le5. apply HOuter. eapply nd_seq; [exact X1|]. eapply nd_seq; [exact X2|].
    eapply nd_if; [exact E3|reflexivity|]. eapply nd_seq; [exact X3|]. eapply nd_seq; [exact X4|].
    eapply nd_if; [exact E4|reflexivity|]. apply nd_seq_ret. exact X5. }
  apply Z.eqb_neq in EL3.
  destruct (nd_read_skipk _t'5 _t'11 _t'12 16 le5 (i + 1 + 1) c (nd_byte i + nd_byte (i + 1) * 2 ^ 8) a
    nd_trip_3 S5 ltac:(lia) ltac:(change (2 ^ 8) with 256; lia) ltac:(lia)) as (le6 & X6 & S6).
  pose proof (nd_byte_range (i + 1 + 1) ltac:(lia)) as B3.
  destruct (nd_eof_exec _t'10 le6 (i + 1 + 1 + 1) c
    (nd_byte i + nd_byte (i + 1) * 2 ^ 8 + nd_byte (i + 1 + 1) * 2 ^ 16) a nd_keeps_t10 S6
    ltac:(lia)) as (le7 & X7 & S7).
  destruct (L =? i + 1 + 1 + 1) eqn:EL4.
  { exists le7. apply HOuter. eapply nd_seq; [exact X1|]. eapply nd_seq; [exact X2|].
    eapply nd_if; [exact E3|reflexivity|]. eapply nd_seq; [exact X3|]. eapply nd_seq; [exact X4|].
    eapply nd_if; [exact E4|reflexivity|]. eapply nd_seq; [exact X5|]. eapply nd_seq; [exact X6|].
    apply nd_seq_ret. exact X7. }
  apply Z.eqb_neq in EL4.
  destruct (nd_read_skipk _t'6 _t'8 _t'9 24 le7 (i + 1 + 1 + 1) c
    (nd_byte i + nd_byte (i + 1) * 2 ^ 8 + nd_byte (i + 1 + 1) * 2 ^ 16) a
    nd_trip_4 S7 ltac:(lia) ltac:(change (2 ^ 8) with 256; change (2 ^ 16) with 65536; lia) ltac:(lia))
    as (le8 & X8 & S8).
  pose proof (nd_byte_range (i + 1 + 1 + 1) ltac:(lia)) as B4.
  exists le8. split; [|split; [exact S8|]].
  - apply HOuter. eapply nd_seq; [exact X1|]. eapply nd_seq; [exact X2|].
    eapply nd_if; [exact E3|reflexivity|]. eapply nd_seq; [exact X3|]. eapply nd_seq; [exact X4|].
    eapply nd_if; [exact E4|reflexivity|]. eapply nd_seq; [exact X5|]. eapply nd_seq; [exact X6|].
    eapply nd_seq; [exact X7|exact X8].
  - change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216. lia.
Qed.

(** [if (len - i < skip) return 0; i += skip; result++;] *)
Lemma nd_tail_exec le i c s a :
  nd_st le i c s a -> 0 <= i <= L -> 0 <= s < 4294967296 -> 0 <= a <= 4294967296 ->
  if L - i <? s
  then exists le', Clight2.exec_stmt sha_ge e le m nd_tail E0 le' m RET0
  else exists le', Clight2.exec_stmt sha_ge e le m nd_tail E0 le' m Out_normal /\
         nd_core le' (i + s) (a + 1).
Proof.
  intros ((Hli & Hr & Hsp) & Hcd & Hk) Hi Hs Ha. pose proof nd_L as HLr.
  set (le1 := PTree.set _t'7 (Vint len) le).
  assert (HC : eval_expr sha_ge e le1 m
    (Ebinop Olt (Ebinop Osub (Etempvar _t'7 tuint) (Etempvar _i tulong) tulong) (Etempvar _skip tulong) tint)
    (Val.of_bool (L - i <? s))).
  { eapply eval_Ebinop with (v1 := Vlong (Int64.repr (L - i))) (v2 := Vlong (Int64.repr s)).
    - eapply eval_Ebinop; [apply eval_Etempvar; apply PTree.gss
                          |apply eval_Etempvar; unfold le1; rewrite PTree.gso by discriminate; exact Hli|].
      rewrite <- (nd_i64_sub L i) by lia. reflexivity.
    - apply eval_Etempvar. unfold le1. rewrite PTree.gso by discriminate. exact Hk.
    - change (Some (Val.of_bool (Int64.ltu (Int64.repr (L - i)) (Int64.repr s))) =
              Some (Val.of_bool (L - i <? s))).
      rewrite nd_i64_ltu by lia. reflexivity. }
  assert (H1 : Clight2.exec_stmt sha_ge e le m (nd_len_set _t'7) E0 le1 m Out_normal).
  { apply exec_Sset. apply nd_ev_len. exact Hsp. }
  unfold nd_tail.
  destruct (L - i <? s) eqn:ET.
  - exists le1. apply nd_seq_ret. eapply nd_seq; [exact H1|].
    eapply nd_if; [exact HC|reflexivity|]. apply nd_ret0.
  - apply Z.ltb_ge in ET.
    set (le2 := PTree.set _i (Vlong (Int64.repr (i + s))) le1).
    set (le3 := PTree.set _result (Vlong (Int64.repr (a + 1))) le2).
    exists le3. split.
    + eapply nd_seq with (le1 := le1).
      { eapply nd_seq; [exact H1|]. eapply nd_if; [exact HC|reflexivity|]. apply exec_Sskip. }
      eapply nd_seq with (le1 := le2).
      * apply exec_Sset.
        eapply eval_Ebinop; [apply eval_Etempvar; unfold le1; rewrite PTree.gso by discriminate; exact Hli
                            |apply eval_Etempvar; unfold le1; rewrite PTree.gso by discriminate; exact Hk|].
        rewrite <- (nd_i64_add i s) by lia. reflexivity.
      * apply exec_Sset.
        eapply eval_Ebinop; [apply eval_Etempvar; unfold le2, le1; rewrite !PTree.gso by discriminate; exact Hr
                            |apply eval_Econst_int|].
        rewrite <- (nd_i64_add a 1) by lia. reflexivity.
    + unfold nd_core, le3, le2, le1. rewrite PTree.gss.
      rewrite (PTree.gso _ _ (i := _i)) by discriminate. rewrite PTree.gss.
      rewrite !PTree.gso by discriminate. repeat split; assumption.
Qed.

(** One iteration of the scan. *)
Lemma nd_iter le i a :
  nd_core le i a -> 1 <= i < L -> 0 <= a <= i ->
  match nd_op i with
  | Some i' =>
      exists le', Clight2.exec_stmt sha_ge e le m nd_s1 E0 le' m Out_normal /\
        nd_core le' i' (a + 1) /\ i < i' <= L
  | None => exists le', Clight2.exec_stmt sha_ge e le m nd_s1 E0 le' m RET0
  end.
Proof.
  intros (Hli & Hr & Hsp) Hi Ha. pose proof nd_L as HLr.
  set (le0 := PTree.set _t'22 (Vint len) le).
  set (leS := PTree.set _skip (Vlong (Int64.repr 0)) le0).
  assert (CS : nd_core leS i a).
  { unfold nd_core, leS, le0. rewrite !PTree.gso by discriminate. repeat split; assumption. }
  set (leR := nd_read_le _t'2 _t'20 _t'21 leS i).
  set (leC := PTree.set _code (Vint (nd_b i)) leR).
  destruct (nd_load_byte _ _ _ _ (HBs i ltac:(lia))) as [Hz Hbr]. fold (nd_b i) in Hz, Hbr.
  assert (StC : nd_st leC (i + 1) (nd_b i) 0 a).
  { pose proof (nd_read_core _t'2 _t'20 _t'21 leS i a nd_trip_c CS) as (C1 & C2 & C3).
    destruct (nd_read_other _t'2 _t'20 _t'21 leS i nd_trip_c) as (O1 & O2).
    unfold nd_st, nd_core, leC. rewrite PTree.gss, !PTree.gso by discriminate.
    fold leR in C1, C2, C3, O2. rewrite O2. unfold leS. rewrite PTree.gss. repeat split; assumption. }
  assert (HPre : forall rest le' out,
    Clight2.exec_stmt sha_ge e leC m rest E0 le' m out ->
    Clight2.exec_stmt sha_ge e le m
      (Ssequence
        (Ssequence (nd_len_set _t'22)
           (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _t'22 tuint) tint) Sskip Sbreak))
        (Ssequence (Sset _skip (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Ssequence
            (nd_read_stmt _t'2 _t'20 _t'21 (Sset _code (Ecast (Etempvar _t'21 tuchar) tuchar)))
            rest))) E0 le' m out).
  { intros rest le' out HX.
    eapply nd_seq with (le1 := le0).
    { eapply nd_seq; [apply exec_Sset; apply nd_ev_len; exact Hsp|].
      eapply nd_if with (b := true); [|reflexivity|apply exec_Sskip].
      eapply eval_Ebinop; [apply eval_Etempvar; unfold le0; rewrite PTree.gso by discriminate; exact Hli
                          |apply eval_Etempvar; apply PTree.gss|].
      change (Some (Val.of_bool (Int64.ltu (Int64.repr i) (Int64.repr (Int.unsigned len)))) = Some (Val.of_bool true)).
      fold L. rewrite nd_i64_ltu by lia. rewrite (proj2 (Z.ltb_lt i L)) by lia. reflexivity. }
    eapply nd_seq with (le1 := leS).
    { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
    eapply nd_seq with (le1 := leC); [|exact HX].
    eapply nd_read_exec; [exact nd_trip_c|exact (proj1 CS)|exact (proj2 (proj2 CS))|lia|].
    apply exec_Sset. eapply eval_Ecast with (v1 := Vint (nd_b i)); [apply eval_Etempvar; apply nd_read_tb|].
    change (Some (Vint (Int.zero_ext 8 (nd_b i))) = Some (Vint (nd_b i))). rewrite Hz. reflexivity. }
  pose proof (nd_ev_lt_code leC (nd_b i) 96 (proj1 (proj2 StC)) ltac:(lia) Hbr) as E96e.
  fold (nd_byte i) in E96e.
  unfold nd_op, nd_s1.
  destruct (96 <? nd_byte i) eqn:E96.
  { exists leC. apply HPre. apply nd_seq_ret. eapply nd_if; [exact E96e|reflexivity|]. apply nd_ret0. }
  pose proof (nd_skipcalc_exec leC (i + 1) (nd_b i) a StC ltac:(lia) Hbr) as HK.
  fold (nd_byte i) in HK.
  destruct (nd_skip (nd_byte i) (i + 1)) as [[i' s']|].
  2: { destruct HK as (le' & X). exists le'. apply HPre.
       eapply nd_seq; [eapply nd_if; [exact E96e|reflexivity|apply exec_Sskip]|].
       apply nd_seq_ret. exact X. }
  destruct HK as (le2 & X & S2 & Hi' & Hs').
  pose proof (nd_tail_exec le2 i' (nd_b i) s' a S2 ltac:(lia) Hs' ltac:(lia)) as HT.
  destruct (L - i' <? s') eqn:ET.
  - destruct HT as (le3 & X3). exists le3. apply HPre.
    eapply nd_seq; [eapply nd_if; [exact E96e|reflexivity|apply exec_Sskip]|].
    eapply nd_seq; [exact X|exact X3].
  - destruct HT as (le3 & X3 & C3). apply Z.ltb_ge in ET. exists le3. split; [|split; [exact C3|lia]].
    apply HPre.
    eapply nd_seq; [eapply nd_if; [exact E96e|reflexivity|apply exec_Sskip]|].
    eapply nd_seq; [exact X|exact X3].
Qed.

Lemma nd_loop_exec fuel : forall i a le,
  nd_core le i a -> 1 <= i <= L -> 0 <= a <= i -> L - i <= Z.of_nat fuel ->
  match nd_loop fuel i a with
  | Some r =>
      exists le', Clight2.exec_stmt sha_ge e le m (Sloop nd_s1 Sskip) E0 le' m Out_normal /\
        le'!_result = Some (Vlong (Int64.repr r))
  | None => exists le', Clight2.exec_stmt sha_ge e le m (Sloop nd_s1 Sskip) E0 le' m RET0
  end.
Proof.
  assert (HExit : forall i a le, nd_core le i a -> i = L ->
    exists le', Clight2.exec_stmt sha_ge e le m (Sloop nd_s1 Sskip) E0 le' m Out_normal /\
      le'!_result = Some (Vlong (Int64.repr a))).
  { intros i a le (Hli & Hr & Hsp) ->. pose proof nd_L as HLr.
    exists (PTree.set _t'22 (Vint len) le). split; [|rewrite PTree.gso by discriminate; exact Hr].
    eapply exec_Sloop_stop1 with (out' := Out_break); [|constructor].
    unfold nd_s1. eapply exec_Sseq_2; [|discriminate].
    eapply nd_seq; [apply exec_Sset; apply nd_ev_len; exact Hsp|].
    eapply nd_if with (b := false); [|reflexivity|apply exec_Sbreak].
    eapply eval_Ebinop; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact Hli
                        |apply eval_Etempvar; apply PTree.gss|].
    change (Some (Val.of_bool (Int64.ltu (Int64.repr L) (Int64.repr (Int.unsigned len)))) = Some (Val.of_bool false)).
    fold L. rewrite nd_i64_ltu by lia. rewrite Z.ltb_irrefl. reflexivity. }
  induction fuel as [|fuel IH]; intros i a le HC Hi Ha Hf.
  - cbn [nd_loop]. assert (i = L) by lia.
    rewrite (proj2 (Z.ltb_ge i L)) by lia. exact (HExit i a le HC H).
  - cbn [nd_loop]. destruct (i <? L) eqn:EL.
    2: { apply Z.ltb_ge in EL. exact (HExit i a le HC ltac:(lia)). }
    apply Z.ltb_lt in EL.
    pose proof (nd_iter le i a HC ltac:(lia) Ha) as HI.
    destruct (nd_op i) as [i'|].
    2: { destruct HI as (le1 & X). exists le1.
         eapply exec_Sloop_stop1 with (out' := RET0); [exact X|unfold RET0; constructor]. }
    destruct HI as (le1 & X & C1 & Hi').
    pose proof (IH i' (a + 1) le1 C1 ltac:(lia) ltac:(lia) ltac:(lia)) as HR.
    destruct (nd_loop fuel i' (a + 1)) as [r|].
    + destruct HR as (le2 & X2 & R). exists le2. split; [|exact R].
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop; [exact X|constructor|apply exec_Sskip|exact X2].
    + destruct HR as (le2 & X2). exists le2.
      change E0 with (E0 ** E0 ** E0).
      eapply exec_Sloop_loop; [exact X|constructor|apply exec_Sskip|exact X2].
Qed.

Lemma nd_loop_bound fuel : forall i a r, 0 <= a <= i -> i <= L -> nd_loop fuel i a = Some r -> 0 <= r <= L.
Proof.
  induction fuel as [|fuel IH]; intros i a r Ha Hi; cbn [nd_loop].
  - destruct (i <? L) eqn:EL; [discriminate|]. intros H. injection H as <-. lia.
  - destruct (i <? L) eqn:EL.
    + apply Z.ltb_lt in EL. unfold nd_op.
      destruct (96 <? nd_byte i); [discriminate|].
      destruct (nd_skip (nd_byte i) (i + 1)) as [[i' s']|] eqn:ES; [|discriminate].
      destruct (L - i' <? s') eqn:ET; [discriminate|]. apply Z.ltb_ge in ET.
      assert (Hi' : i + 1 <= i' /\ 0 <= s').
      { revert ES. unfold nd_skip.
        pose proof (nd_byte_range i ltac:(lia)) as B0.
        destruct (nd_byte i <? 76); [intros E; injection E as <- <-; lia|].
        destruct (nd_byte i <? 79); [|intros E; injection E as <- <-; lia].
        destruct (L =? i + 1) eqn:Q1; [discriminate|]. apply Z.eqb_neq in Q1.
        pose proof (nd_byte_range (i + 1) ltac:(lia)) as B1.
        destruct (77 <=? nd_byte i); [|intros E; injection E as <- <-; lia].
        destruct (L =? i + 1 + 1) eqn:Q2; [discriminate|]. apply Z.eqb_neq in Q2.
        pose proof (nd_byte_range (i + 1 + 1) ltac:(lia)) as B2.
        destruct (78 <=? nd_byte i); [|intros E; injection E as <- <-; change (2 ^ 8) with 256; lia].
        destruct (L =? i + 1 + 1 + 1) eqn:Q3; [discriminate|]. apply Z.eqb_neq in Q3.
        pose proof (nd_byte_range (i + 1 + 1 + 1) ltac:(lia)) as B3.
        destruct (L =? i + 1 + 1 + 1 + 1) eqn:Q4; [discriminate|]. apply Z.eqb_neq in Q4.
        pose proof (nd_byte_range (i + 1 + 1 + 1 + 1) ltac:(lia)) as B4.
        intros E; injection E as <- <-.
        change (2 ^ 8) with 256. change (2 ^ 16) with 65536. change (2 ^ 24) with 16777216. lia. }
      intros H. apply (IH (i' + s') (a + 1) r); [lia|lia|exact H].
    + intros H. injection H as <-. lia.
Qed.
(** [if (0 == len || 0x6a != buf[0]) return 0;] *)
Lemma nd_head_exec le :
  le!_scriptPubKey = Some spv ->
  exists le',
    Clight2.exec_stmt sha_ge e le m nd_head E0 le' m
      (if L =? 0 then RET0 else if negb (106 =? nd_byte 0) then RET0 else Out_normal) /\
    le'!_scriptPubKey = Some spv.
Proof.
  intros Hsp. pose proof nd_L as HLr.
  set (leA := PTree.set _t'23 (Vint len) le).
  assert (EA : eval_expr sha_ge e leA m
    (Ebinop Oeq (Econst_int (Int.repr 0) tint) (Etempvar _t'23 tuint) tint) (Val.of_bool (L =? 0))).
  { eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
    change (Some (Val.of_bool (Int.eq (Int.repr 0) len)) = Some (Val.of_bool (L =? 0))).
    rewrite nd_int_eq by lia. fold L. rewrite Z.eqb_sym. reflexivity. }
  assert (HA : Clight2.exec_stmt sha_ge e le m (nd_len_set _t'23) E0 leA m Out_normal).
  { apply exec_Sset. apply nd_ev_len. exact Hsp. }
  unfold nd_head.
  destruct (L =? 0) eqn:EL0.
  - exists (PTree.set _t'1 (Vint (Int.repr 1)) leA). split.
    + eapply nd_seq with (le1 := PTree.set _t'1 (Vint (Int.repr 1)) leA).
      * eapply nd_seq; [exact HA|]. eapply nd_if; [exact EA|reflexivity|].
        apply exec_Sset. apply eval_Econst_int.
      * eapply exec_Sifthenelse with (v1 := Vint (Int.repr 1)) (b := true);
          [apply eval_Etempvar; apply PTree.gss|reflexivity|apply nd_ret0].
    + unfold leA. rewrite !PTree.gso by discriminate. exact Hsp.
  - apply Z.eqb_neq in EL0.
    remember (negb (106 =? nd_byte 0)) as bN eqn:EbN.
    set (leB := PTree.set _t'24 (Vptr bb ob) leA).
    set (leC := PTree.set _t'25 (Vint (nd_b 0)) leB).
    set (leD := PTree.set _t'1 (Val.of_bool bN) leC).
    exists leD. split.
    + eapply nd_seq with (le1 := leD).
      * eapply nd_seq; [exact HA|]. eapply nd_if; [exact EA|reflexivity|].
        eapply nd_seq with (le1 := leB).
        { apply exec_Sset. apply nd_ev_buf; [|lia]. unfold leA. rewrite PTree.gso by discriminate. exact Hsp. }
        eapply nd_seq with (le1 := leC).
        { apply exec_Sset. eapply eval_byte0; [apply PTree.gss|].
          pose proof (HBs 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. exact H0. }
        apply exec_Sset. eapply eval_Ecast with (v1 := Val.of_bool bN).
        -- eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; apply PTree.gss|].
           change (Some (Val.of_bool (negb (Int.eq (Int.repr 106) (nd_b 0)))) = Some (Val.of_bool bN)).
           rewrite nd_int_eq by lia. fold (nd_byte 0). rewrite <- EbN. reflexivity.
        -- destruct bN; reflexivity.
      * eapply nd_if with (b := bN); [apply eval_Etempvar; apply PTree.gss|reflexivity|].
        destruct bN; [apply nd_ret0|apply exec_Sskip].
    + unfold leD, leC, leB, leA. rewrite !PTree.gso by discriminate. exact Hsp.
Qed.

Lemma nd_entry le0 :
  le0 = PTree.set _scriptPubKey spv (create_undef_temps (fn_temps f_countNullDataCodes)) ->
  function_entry2 sha_ge f_countNullDataCodes [spv] m empty_env le0 m.
Proof.
  intros ->. apply function_entry2_intro.
  - apply list_norepet_nil.
  - repeat constructor; simpl; intuition discriminate.
  - intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
  - apply alloc_variables_nil.
  - reflexivity.
Qed.

Theorem eval_countNullDataCodes_gen :
  e = empty_env ->
  Clight2.eval_funcall sha_ge m (Internal f_countNullDataCodes) [spv] E0 m (Vlong (Int64.repr nd_count)).
Proof.
  intros He. pose proof nd_L as HLr.
  set (le0 := PTree.set _scriptPubKey spv (create_undef_temps (fn_temps f_countNullDataCodes))).
  destruct (nd_head_exec le0 (PTree.gss _ _ _)) as (le1 & XH & Hsp1).
  assert (HRet0 : forall le',
    Clight2.exec_stmt sha_ge e le0 m (fn_body f_countNullDataCodes) E0 le' m RET0 ->
    nd_count = 0 ->
    Clight2.eval_funcall sha_ge m (Internal f_countNullDataCodes) [spv] E0 m (Vlong (Int64.repr nd_count))).
  { intros le' HX HZ. rewrite HZ.
    eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m) (m2 := m) (le2 := le') (out := RET0);
      [rewrite He; apply nd_entry; reflexivity|exact HX|cbn; split; [discriminate|reflexivity]|rewrite He; reflexivity]. }
  destruct (L =? 0) eqn:EL0.
  { apply (HRet0 le1); [rewrite nd_body_shape; apply nd_seq_ret; exact XH|].
    unfold nd_count. rewrite EL0. reflexivity. }
  remember (negb (106 =? nd_byte 0)) as bN eqn:EbN. destruct bN.
  { apply (HRet0 le1); [rewrite nd_body_shape; apply nd_seq_ret; exact XH|].
    unfold nd_count. rewrite EL0, <- EbN. reflexivity. }
  apply Z.eqb_neq in EL0.
  set (leR := PTree.set _result (Vlong (Int64.repr 0)) le1).
  set (leI := PTree.set _i (Vlong (Int64.repr 1)) leR).
  assert (HC : nd_core leI 1 0).
  { unfold nd_core, leI, leR. rewrite PTree.gss. rewrite PTree.gso by discriminate. rewrite PTree.gss.
    rewrite !PTree.gso by discriminate. repeat split; try reflexivity. exact Hsp1. }
  assert (HR : Clight2.exec_stmt sha_ge e le1 m
    (Sset _result (Ecast (Econst_int (Int.repr 0) tint) tulong)) E0 leR m Out_normal).
  { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
  assert (HI : Clight2.exec_stmt sha_ge e leR m
    (Sset _i (Ecast (Econst_int (Int.repr 1) tint) tulong)) E0 leI m Out_normal).
  { apply exec_Sset. eapply eval_Ecast; [apply eval_Econst_int|reflexivity]. }
  pose proof (nd_loop_exec (Z.to_nat L) 1 0 leI HC ltac:(lia) ltac:(lia) ltac:(lia)) as HLp.
  assert (HCnt : nd_count = match nd_loop (Z.to_nat L) 1 0 with Some r => r | None => 0 end).
  { unfold nd_count. rewrite (proj2 (Z.eqb_neq L 0) EL0), <- EbN. reflexivity. }
  destruct (nd_loop (Z.to_nat L) 1 0) as [r|] eqn:ELp.
  - destruct HLp as (le2 & X2 & R). rewrite HCnt.
    eapply eval_funcall_internal with (e := e) (le1 := le0) (m1 := m) (m2 := m) (le2 := le2)
      (out := Out_return (Some (Vlong (Int64.repr r), tulong)));
      [rewrite He; apply nd_entry; reflexivity| |cbn; split; [discriminate|reflexivity]|rewrite He; reflexivity].
    rewrite nd_body_shape.
    eapply nd_seq; [exact XH|]. eapply nd_seq; [exact HR|].
    eapply nd_seq with (le1 := le2); [eapply nd_seq; [exact HI|exact X2]|].
    apply exec_Sreturn_some. apply eval_Etempvar. exact R.
  - destruct HLp as (le2 & X2).
    apply (HRet0 le2); [|exact HCnt].
    rewrite nd_body_shape.
    eapply nd_seq; [exact XH|]. eapply nd_seq; [exact HR|].
    apply nd_seq_ret. eapply nd_seq; [exact HI|exact X2].
Qed.

Lemma nd_count_bound : 0 <= nd_count <= L.
Proof.
  pose proof nd_L as HLr. unfold nd_count.
  destruct (L =? 0) eqn:EL0; [lia|]. apply Z.eqb_neq in EL0.
  destruct (negb (106 =? nd_byte 0)); [lia|].
  destruct (nd_loop (Z.to_nat L) 1 0) as [r|] eqn:E; [|lia].
  exact (nd_loop_bound (Z.to_nat L) 1 0 r ltac:(lia) ltac:(lia) E).
Qed.
End CountNullData.

Theorem eval_countNullDataCodes m bsp osp (len : int) bb ob (bs : list int) :
  0 <= osp /\ osp + 16 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m bsp (osp + 8) = Some (Vint len) ->
  (0 < Int.unsigned len -> Mem.load Mptr m bsp osp = Some (Vptr bb ob)) ->
  Ptrofs.unsigned ob + Int.unsigned len <= Ptrofs.max_unsigned ->
  (forall i, 0 <= i < Int.unsigned len ->
     Mem.load Mint8unsigned m bb (Ptrofs.unsigned ob + i) = Some (Vint (nth (Z.to_nat i) bs Int.zero))) ->
  Clight2.eval_funcall sha_ge m (Internal f_countNullDataCodes) [Vptr bsp (Ptrofs.repr osp)] E0 m
    (Vlong (Int64.repr (nd_count len bs))).
Proof.
  intros Hosp HLen HBuf HobM HBs.
  exact (eval_countNullDataCodes_gen empty_env m bsp osp len bb ob bs Hosp HLen HBuf HobM HBs eq_refl).
Qed.
