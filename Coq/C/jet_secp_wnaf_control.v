(** Control flow for the original wNAF loop body. No public jet registration. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
  C.jet_secp_wnaf_digit C.jet_secp_scalar_get_bits C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_get_b32_numeric C.jet_secp_curve_statements C.jet_secp_fns C.jet_secp_fe_math.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition wnaf_dispatch := nth 0 wnaf_loop_statements Sskip.
Definition wnaf_bit_call := match wnaf_dispatch with Ssequence call _=>call | _=>Sskip end.
Definition wnaf_bit_if := match wnaf_dispatch with Ssequence _ branch=>branch | _=>Sskip end.
Definition wnaf_now_set := nth 1 wnaf_loop_statements Sskip.
Definition wnaf_now_clamp := nth 2 wnaf_loop_statements Sskip.
Definition wnaf_window_select := Ssequence wnaf_now_set wnaf_now_clamp.
Definition wnaf_nonzero_body := statement_sequence (skipn 1 wnaf_loop_statements)
  (snd (split_statement_last wnaf_loop_body)).
Definition wnaf_select_temps le bit len w :=
  let lw:=PTree.set _now (Vint (Int.repr w)) le in
  if zlt (len-bit) w then PTree.set _now (Vint (Int.repr (len-bit))) lw else lw.
Definition wnaf_after_temps le bit width := PTree.set _bit (Vint (Int.repr (bit+width)))
  (PTree.set _last_set_bit (Vint (Int.repr bit)) le).

Lemma wnaf_dispatch_source : wnaf_loop_body=Ssequence wnaf_dispatch wnaf_nonzero_body.
Proof. reflexivity. Qed.
Lemma wnaf_bit_call_source : wnaf_bit_call=
  curve_call _secp256k1_scalar_get_bits f_secp256k1_scalar_get_bits (Some _t'2)
    [Eaddrof (Evar _s (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
      Etempvar _bit tint;Econst_int Int.one tint].
Proof. reflexivity. Qed.
Lemma wnaf_bit_if_source : wnaf_bit_if=
  Sifthenelse (Ebinop Oeq (Etempvar _t'2 tuint) (Ecast (Etempvar _carry tint) tuint) tint)
    (Ssequence (Sset _bit (Ebinop Oadd (Etempvar _bit tint) (Econst_int Int.one tint) tint)) Scontinue)
    Sskip.
Proof. reflexivity. Qed.
Lemma wnaf_now_sources :
  wnaf_now_set=Sset _now (Etempvar _w tint) /\
  wnaf_now_clamp=Sifthenelse
    (Ebinop Ogt (Etempvar _now tint) (Ebinop Osub (Etempvar _len tint) (Etempvar _bit tint) tint) tint)
    (Sset _now (Ebinop Osub (Etempvar _len tint) (Etempvar _bit tint) tint)) Sskip.
Proof. split;reflexivity. Qed.
Lemma wnaf_after_digit_source : wnaf_after_digit=
  Ssequence (Sset _last_set_bit (Etempvar _bit tint))
    (Sset _bit (Ebinop Oadd (Etempvar _bit tint) (Etempvar _now tint) tint)).
Proof. reflexivity. Qed.

Lemma wnaf_skip_value n bit carry : 0<=bit -> (n/2^bit) mod 2=carry ->
  n/2^bit+carry=2*(n/2^(bit+1)+carry).
Proof.
  intros Bit Low;rewrite <-div_div_pow by lia;change (2^1) with 2.
  pose proof (Z.div_mod (n/2^bit) 2 ltac:(lia));nia.
Qed.

Lemma wnaf_window_bounds bit len w : 0<=bit<len -> len<=256 -> 2<=w<=31 ->
  1<=Z.min w (len-bit)<=w /\ bit+Z.min w (len-bit)<=len /\
  bit<bit+Z.min w (len-bit)<=len.
Proof. intros Bit Len W;pose proof (Z.le_min_l w (len-bit));pose proof (Z.le_min_r w (len-bit));
  pose proof (Z.min_glb w (len-bit) 1 ltac:(lia) ltac:(lia));lia.
Qed.

Lemma exec_wnaf_bit_read le m bs n bit :
  0<=n<2^256 -> 0<=bit<256 -> le!_bit=Some (Vint (Int.repr bit)) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_bit_call E0
    (PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le) m Out_normal.
Proof.
  intros N Bit HB Storage;rewrite wnaf_bit_call_source.
  eapply exec_curve_call with (vargs:=[Vptr bs Ptrofs.zero;Vint (Int.repr bit);Vint Int.one])
    (v:=Vint (Int.repr ((n/2^bit) mod 2))).
  - unfold secp_pure;repeat (first [left;reflexivity|right]).
  - reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
    + reflexivity.
    + eapply eval_Econs;[apply eval_Etempvar;exact HB|reflexivity|].
      eapply eval_Econs;[constructor|reflexivity|constructor].
  - apply (eval_scalar_get_bits_slice m bs 0 n bit 1);try assumption;try lia.
    pose proof (Z.mod_pos_bound bit 64 ltac:(lia));lia.
Qed.

Lemma eval_wnaf_bit_compare e le m low carry :
  le!_t'2=Some (Vint (Int.repr low)) -> le!_carry=Some (Vint (Int.repr carry)) ->
  0<=low<2 -> 0<=carry<2 ->
  eval_expr secp_ge e le m
    (Ebinop Oeq (Etempvar _t'2 tuint) (Ecast (Etempvar _carry tint) tuint) tint)
    (Val.of_bool (if zeq low carry then true else false)).
Proof.
  intros HL HC Low Carry.
  eapply eval_Ebinop.
  - apply eval_Etempvar;exact HL.
  - eapply eval_Ecast;[apply eval_Etempvar;exact HC|reflexivity].
  - change (Some (Val.of_bool (Int.eq (Int.repr low) (Int.repr carry)))=
      Some (Val.of_bool (if zeq low carry then true else false))).
    unfold Int.eq;rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.

Theorem exec_wnaf_dispatch_skip le m bs n bit carry :
  0<=n<2^256 -> 0<=bit<256 -> (carry=0 \/ carry=1) ->
  (n/2^bit) mod 2=carry ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_carry=Some (Vint (Int.repr carry)) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0
    (PTree.set _bit (Vint (Int.repr (bit+1)))
      (PTree.set _t'2 (Vint (Int.repr carry)) le)) m Out_continue.
Proof.
  intros N Bit Carry Low HB HC Storage.
  unfold wnaf_dispatch;change (nth 0 wnaf_loop_statements Sskip) with (Ssequence wnaf_bit_call wnaf_bit_if).
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'2 (Vint (Int.repr carry)) le).
  - rewrite <-Low;apply exec_wnaf_bit_read;assumption.
  - rewrite wnaf_bit_if_source.
    eapply exec_Sifthenelse with (v1:=Vtrue) (b:=true);[|reflexivity|].
    + replace Vtrue with (Val.of_bool (if zeq carry carry then true else false)) by
        (destruct zeq;[reflexivity|congruence]).
      apply eval_wnaf_bit_compare;try (apply PTree.gss);try (destruct Carry;lia).
      rewrite PTree.gso by discriminate;exact HC.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _bit (Vint (Int.repr (bit+1))) (PTree.set _t'2 (Vint (Int.repr carry)) le)).
      * apply exec_Sset;eapply eval_Ebinop.
        -- apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HB.
        -- constructor.
        -- change (Some (Vint (Int.add (Int.repr bit) Int.one))=Some (Vint (Int.repr (bit+1)))).
           unfold Int.add;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
      * constructor.
Qed.

Theorem exec_wnaf_dispatch_nonzero le m bs n bit carry :
  0<=n<2^256 -> 0<=bit<256 -> (carry=0 \/ carry=1) ->
  (n/2^bit) mod 2<>carry ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_carry=Some (Vint (Int.repr carry)) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0
    (PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le) m Out_normal.
Proof.
  intros N Bit Carry Low HB HC Storage.
  unfold wnaf_dispatch;change (nth 0 wnaf_loop_statements Sskip) with (Ssequence wnaf_bit_call wnaf_bit_if).
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le).
  - apply exec_wnaf_bit_read;assumption.
  - rewrite wnaf_bit_if_source.
    eapply exec_Sifthenelse with (v1:=Vfalse) (b:=false);[|reflexivity|constructor].
    replace Vfalse with (Val.of_bool (if zeq ((n/2^bit) mod 2) carry then true else false)) by
      (destruct zeq;[congruence|reflexivity]).
    apply eval_wnaf_bit_compare;try (apply PTree.gss);try (destruct Carry;lia).
    + rewrite PTree.gso by discriminate;exact HC.
    + apply Z.mod_pos_bound;lia.
Qed.

Lemma eval_wnaf_clamp_guard e le m bit len w :
  0<=bit<len -> len<=256 -> 2<=w<=31 ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_len=Some (Vint (Int.repr len)) ->
  le!_now=Some (Vint (Int.repr w)) ->
  eval_expr secp_ge e le m
    (Ebinop Ogt (Etempvar _now tint) (Ebinop Osub (Etempvar _len tint) (Etempvar _bit tint) tint) tint)
    (Val.of_bool (if zlt (len-bit) w then true else false)).
Proof.
  intros Bit Len W HB HL HN.
  eapply eval_Ebinop.
  - apply eval_Etempvar;exact HN.
  - eapply eval_Ebinop;[apply eval_Etempvar;exact HL|apply eval_Etempvar;exact HB|reflexivity].
  - change (Some (Val.of_bool (Int.lt (Int.sub (Int.repr len) (Int.repr bit)) (Int.repr w)))=
      Some (Val.of_bool (if zlt (len-bit) w then true else false))).
    rewrite Int.sub_signed;unfold Int.lt.
    rewrite (Int.signed_repr len) by (change Int.min_signed with (-2147483648);
      change Int.max_signed with 2147483647;lia).
    rewrite (Int.signed_repr bit) by (change Int.min_signed with (-2147483648);
      change Int.max_signed with 2147483647;lia).
    rewrite (Int.signed_repr (len-bit)),(Int.signed_repr w) by
      (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
Qed.

Lemma exec_wnaf_select e le m bit len w :
  0<=bit<len -> len<=256 -> 2<=w<=31 ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_len=Some (Vint (Int.repr len)) ->
  le!_w=Some (Vint (Int.repr w)) ->
  Clight2.exec_stmt secp_ge e le m wnaf_window_select E0
    (wnaf_select_temps le bit len w) m Out_normal.
Proof.
  intros Bit Len W HB HL HW.
  unfold wnaf_window_select;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _now (Vint (Int.repr w)) le).
  - rewrite (proj1 wnaf_now_sources);apply exec_Sset;apply eval_Etempvar;exact HW.
  - rewrite (proj2 wnaf_now_sources);unfold wnaf_select_temps;destruct zlt as [Small|Large].
    + eapply exec_Sifthenelse with (v1:=Vtrue) (b:=true);[|reflexivity|].
      * replace Vtrue with (Val.of_bool (if zlt (len-bit) w then true else false)) by
          (destruct zlt;[reflexivity|lia]).
        apply eval_wnaf_clamp_guard;try assumption;try (apply PTree.gss);
          rewrite PTree.gso by discriminate;assumption.
      * apply exec_Sset;eapply eval_Ebinop.
        -- apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HL.
        -- apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HB.
        -- change (Some (Vint (Int.sub (Int.repr len) (Int.repr bit)))=Some (Vint (Int.repr (len-bit)))).
           rewrite Int.sub_signed,!Int.signed_repr by
             (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia);reflexivity.
    + eapply exec_Sifthenelse with (v1:=Vfalse) (b:=false);[|reflexivity|constructor].
      replace Vfalse with (Val.of_bool (if zlt (len-bit) w then true else false)) by
        (destruct zlt;[lia|reflexivity]).
      apply eval_wnaf_clamp_guard;try assumption;try (apply PTree.gss);
        rewrite PTree.gso by discriminate;assumption.
Qed.

Lemma wnaf_select_now le bit len w :
  (wnaf_select_temps le bit len w)!_now=Some (Vint (Int.repr (Z.min w (len-bit)))).
Proof.
  unfold wnaf_select_temps;destruct zlt as [Small|Large];rewrite PTree.gss.
  - rewrite Z.min_r by lia;reflexivity.
  - rewrite Z.min_l by lia;reflexivity.
Qed.
Lemma wnaf_select_other le bit len w id : id<>_now ->
  (wnaf_select_temps le bit len w)!id=le!id.
Proof. intro NE;unfold wnaf_select_temps;destruct zlt;rewrite !PTree.gso by congruence;reflexivity. Qed.

Lemma exec_wnaf_after_digit e le m bit width :
  0<=bit<256 -> 1<=width<=31 -> bit+width<=256 ->
  le!_bit=Some (Vint (Int.repr bit)) -> le!_now=Some (Vint (Int.repr width)) ->
  Clight2.exec_stmt secp_ge e le m wnaf_after_digit E0
    (wnaf_after_temps le bit width) m Out_normal.
Proof.
  intros Bit Width End HB HW;rewrite wnaf_after_digit_source;unfold wnaf_after_temps.
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
    (le1:=PTree.set _last_set_bit (Vint (Int.repr bit)) le).
  - apply exec_Sset;apply eval_Etempvar;exact HB.
  - apply exec_Sset;eapply eval_Ebinop.
    + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HB.
    + apply eval_Etempvar;rewrite PTree.gso by discriminate;exact HW.
    + change (Some (Vint (Int.add (Int.repr bit) (Int.repr width)))=
        Some (Vint (Int.repr (bit+width)))).
      unfold Int.add;rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity.
Qed.

Lemma exec_wnaf_sequence_append e prefix last tail le m le1 m1 le2 m2 out :
  Clight2.exec_stmt secp_ge e le m (statement_sequence prefix last) E0 le1 m1 Out_normal ->
  Clight2.exec_stmt secp_ge e le1 m1 tail E0 le2 m2 out ->
  Clight2.exec_stmt secp_ge e le m (statement_sequence prefix (Ssequence last tail)) E0 le2 m2 out.
Proof.
  revert le m le1 m1;induction prefix as [|head prefix IH];intros le m le1 m1 HP HT;
    cbn [statement_sequence] in *.
  - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
  - inversion HP;subst;[|contradiction].
    match goal with H : ?t1 ** ?t2=E0 |- _ =>destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[eassumption|].
    eapply IH;eassumption.
Qed.

Lemma wnaf_nonzero_body_source : wnaf_nonzero_body=
  Ssequence wnaf_now_set (Ssequence wnaf_now_clamp
    (Ssequence (Ssequence wnaf_window_call wnaf_word_add)
      (Ssequence wnaf_carry_set (Ssequence wnaf_digit_set (Ssequence wnaf_digit_store wnaf_after_digit))))).
Proof. reflexivity. Qed.

Definition wnaf_loop_fields le bit len w carry sign b base last : Prop :=
  le!_bit=Some (Vint (Int.repr bit)) /\ le!_len=Some (Vint (Int.repr len)) /\
  le!_w=Some (Vint (Int.repr w)) /\ le!_carry=Some (Vint (Int.repr carry)) /\
  le!_sign=Some (Vint (Int.repr sign)) /\ le!_wnaf=Some (Vptr b (Ptrofs.repr base)) /\
  le!_last_set_bit=Some (Vint (Int.repr last)).

Lemma wnaf_digit_other le word w id : id<>_word -> id<>_carry ->
  (wnaf_digit_final le word w)!id=le!id.
Proof. intros NE1 NE2;unfold wnaf_digit_final;rewrite !PTree.gso by congruence;reflexivity. Qed.
Lemma wnaf_after_other le bit width id : id<>_bit -> id<>_last_set_bit ->
  (wnaf_after_temps le bit width)!id=le!id.
Proof. intros NE1 NE2;unfold wnaf_after_temps;rewrite !PTree.gso by congruence;reflexivity. Qed.

Lemma wnaf_scalar_store_preserved m mf b ofs v bs n :
  Mem.store Mint32 m b ofs v=Some mf -> b<>bs ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)).
Proof.
  intros Store Separate (Len & Base & Align & Max & Perm & Loads).
  unfold scalar_at;repeat split;try assumption.
  - intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Perm;exact Range].
  - intros i limb Nth;rewrite (Mem.load_store_other _ _ _ _ _ _ Store);[apply Loads;exact Nth|].
    left;congruence.
Qed.

Definition wnaf_nonzero_temps le n bit len w carry :=
  let width:=Z.min w (len-bit) in
  wnaf_after_temps (wnaf_digit_final
    (PTree.set _t'3 (Vint (Int.repr ((n/2^bit) mod 2^width)))
      (wnaf_select_temps le bit len w)) (wnaf_word n bit width carry) w) bit width.

Theorem exec_wnaf_nonzero_body le m n bit len w carry sign b base bs last :
  0<=n<2^256 -> 0<=bit<len -> len<=256 -> 2<=w<=31 ->
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry -> (sign=1 \/ sign= -1) ->
  wnaf_loop_fields le bit len w carry sign b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned ->
  Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  exists mf,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_nonzero_body E0
      (wnaf_nonzero_temps le n bit len w carry) mf Out_normal /\
    Mem.store Mint32 m b (base+4*bit)
      (Vint (Int.repr (sign*wnaf_digit (wnaf_word n bit (Z.min w (len-bit)) carry) w)))=Some mf /\
    wnaf_loop_fields (wnaf_nonzero_temps le n bit len w carry)
      (bit+Z.min w (len-bit)) len w (wnaf_carry (wnaf_word n bit (Z.min w (len-bit)) carry) w)
      sign b base bit /\
    (wnaf_carry (wnaf_word n bit (Z.min w (len-bit)) carry) w=0 \/
      wnaf_carry (wnaf_word n bit (Z.min w (len-bit)) carry) w=1) /\
    -2^(w-1)<wnaf_digit (wnaf_word n bit (Z.min w (len-bit)) carry) w<2^(w-1) /\
    wnaf_digit (wnaf_word n bit (Z.min w (len-bit)) carry) w mod 2=1 /\
    n/2^bit+carry=wnaf_digit (wnaf_word n bit (Z.min w (len-bit)) carry) w+
      2^(Z.min w (len-bit))*(n/2^(bit+Z.min w (len-bit))+
        wnaf_carry (wnaf_word n bit (Z.min w (len-bit)) carry) w).
Proof.
  intros N Bit Len W Carry Different Sign (HB & HL & HW & HC & HS & HP & HLast)
    Storage Base Max Writable.
  pose (width:=Z.min w (len-bit)).
  destruct (wnaf_window_bounds bit len w Bit Len W) as (Width & End & Advance).
  change (1<=width<=w) in Width;change (bit+width<=len) in End.
  pose (ls:=wnaf_select_temps le bit len w).
  assert (Select : Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_window_select E0 ls m Out_normal)
    by (apply exec_wnaf_select;assumption).
  assert (LN : ls!_now=Some (Vint (Int.repr width))) by (apply wnaf_select_now).
  assert (LC : ls!_carry=Some (Vint (Int.repr carry))) by
    (unfold ls;rewrite wnaf_select_other by discriminate;exact HC).
  assert (LW : ls!_w=Some (Vint (Int.repr w))) by
    (unfold ls;rewrite wnaf_select_other by discriminate;exact HW).
  assert (LP : ls!_wnaf=Some (Vptr b (Ptrofs.repr base))) by
    (unfold ls;rewrite wnaf_select_other by discriminate;exact HP).
  assert (LB : ls!_bit=Some (Vint (Int.repr bit))) by
    (unfold ls;rewrite wnaf_select_other by discriminate;exact HB).
  assert (LS : ls!_sign=Some (Vint (Int.repr sign))) by
    (unfold ls;rewrite wnaf_select_other by discriminate;exact HS).
  destruct (exec_wnaf_window_digit ls m n bit width w carry b base sign bs
    N ltac:(lia) Width W ltac:(lia) Carry Different Sign LN LC LW LP LB LS Storage Base Max Writable)
    as (mf & DigitExec & Store & Load & NewCarry & Digit & Odd & Weighted).
  pose (ld:=wnaf_digit_final (PTree.set _t'3 (Vint (Int.repr ((n/2^bit) mod 2^width))) ls)
    (wnaf_word n bit width carry) w).
  assert (DB : ld!_bit=Some (Vint (Int.repr bit))).
  { unfold ld;rewrite wnaf_digit_other by discriminate;rewrite PTree.gso by discriminate;exact LB. }
  assert (DN : ld!_now=Some (Vint (Int.repr width))).
  { unfold ld;rewrite wnaf_digit_other by discriminate;rewrite PTree.gso by discriminate;exact LN. }
  assert (After : Clight2.exec_stmt secp_ge (wnaf_env bs) ld mf wnaf_after_digit E0
    (wnaf_after_temps ld bit width) mf Out_normal).
  { apply exec_wnaf_after_digit;try assumption;lia. }
  assert (Tail : Clight2.exec_stmt secp_ge (wnaf_env bs) ls m
    (statement_sequence [Ssequence wnaf_window_call wnaf_word_add;wnaf_carry_set;wnaf_digit_set]
      (Ssequence wnaf_digit_store wnaf_after_digit)) E0
    (wnaf_after_temps ld bit width) mf Out_normal).
  { eapply exec_wnaf_sequence_append;[exact DigitExec|exact After]. }
  exists mf;split.
  - rewrite wnaf_nonzero_body_source.
    change (Clight2.exec_stmt secp_ge (wnaf_env bs) le m
      (statement_sequence [wnaf_now_set] (Ssequence wnaf_now_clamp
        (statement_sequence [Ssequence wnaf_window_call wnaf_word_add;wnaf_carry_set;wnaf_digit_set]
          (Ssequence wnaf_digit_store wnaf_after_digit)))) E0
      (wnaf_after_temps ld bit width) mf Out_normal).
    eapply exec_wnaf_sequence_append;[exact Select|exact Tail].
  - split;[exact Store|];split.
    + unfold wnaf_loop_fields,wnaf_nonzero_temps;fold width ls ld.
      split;[apply PTree.gss|].
      split;[|split;[|split;[|split;[|split]]]].
      * rewrite wnaf_after_other by discriminate;unfold ld;rewrite wnaf_digit_other by discriminate;
          rewrite PTree.gso by discriminate;unfold ls;rewrite wnaf_select_other by discriminate;exact HL.
      * rewrite wnaf_after_other by discriminate;unfold ld;rewrite wnaf_digit_other by discriminate;
          rewrite PTree.gso by discriminate;exact LW.
      * rewrite wnaf_after_other by discriminate;unfold ld,wnaf_digit_final;
          rewrite PTree.gso by discriminate;apply PTree.gss.
      * rewrite wnaf_after_other by discriminate;unfold ld;rewrite wnaf_digit_other by discriminate;
          rewrite PTree.gso by discriminate;exact LS.
      * rewrite wnaf_after_other by discriminate;unfold ld;rewrite wnaf_digit_other by discriminate;
          rewrite PTree.gso by discriminate;exact LP.
      * unfold wnaf_after_temps;rewrite PTree.gso by discriminate;apply PTree.gss.
    + split;[exact NewCarry|];split;[exact Digit|];split;assumption.
Qed.

Lemma wnaf_skip_fields le bit len w carry sign b base last :
  wnaf_loop_fields le bit len w carry sign b base last ->
  wnaf_loop_fields (PTree.set _bit (Vint (Int.repr (bit+1)))
    (PTree.set _t'2 (Vint (Int.repr carry)) le)) (bit+1) len w carry sign b base last.
Proof.
  intros (HB & HL & HW & HC & HS & HP & HLast);unfold wnaf_loop_fields.
  repeat split;try (apply PTree.gss);rewrite !PTree.gso by discriminate;assumption.
Qed.

Theorem exec_wnaf_loop_body_step le m n bit len w carry sign b base bs last :
  0<=n<2^256 -> 0<=bit<len -> len<=256 -> 2<=w<=31 -> -1<=last<bit ->
  (carry=0 \/ carry=1) -> (sign=1 \/ sign= -1) ->
  wnaf_loop_fields le bit len w carry sign b base last ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) -> b<>bs ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned ->
  Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  exists le' mf bit' carry' digit last' out,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_loop_body E0 le' mf out /\
    wnaf_loop_fields le' bit' len w carry' sign b base last' /\
    bit<bit'<=len /\ -1<=last'<bit' /\ (carry'=0 \/ carry'=1) /\
    scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of n)) /\
    (out=Out_normal \/ out=Out_continue) /\
    n/2^bit+carry=digit+2^(bit'-bit)*(n/2^bit'+carry') /\
    ((digit=0 /\ mf=m /\ last'=last) \/
      (digit mod 2=1 /\ -2^(w-1)<digit<2^(w-1) /\
        Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (sign*digit)))=Some mf /\ last'=bit)).
Proof.
  intros N Bit Len W Last Carry Sign Fields Storage Separate Base Max Writable.
  destruct Fields as (HB & HL & HW & HC & HS & HP & HLast).
  assert (Fields : wnaf_loop_fields le bit len w carry sign b base last) by
    (repeat split;assumption).
  destruct (zeq ((n/2^bit) mod 2) carry) as [Same|Different].
  - exists (PTree.set _bit (Vint (Int.repr (bit+1))) (PTree.set _t'2 (Vint (Int.repr carry)) le)),
      m,(bit+1),carry,0,last,Out_continue.
    split.
    + rewrite wnaf_dispatch_source;eapply exec_Sseq_2;[|discriminate].
      apply exec_wnaf_dispatch_skip with (n:=n);try assumption;lia.
    + split;[apply wnaf_skip_fields;exact Fields|].
      split;[lia|];split;[lia|];split;[exact Carry|];split;[exact Storage|].
      split;[right;reflexivity|];split.
      * replace (bit+1-bit) with 1 by lia;change (2^1) with 2;rewrite Z.add_0_l.
        apply wnaf_skip_value;try assumption;lia.
      * left;repeat split;reflexivity.
  - pose (lr:=PTree.set _t'2 (Vint (Int.repr ((n/2^bit) mod 2))) le).
    assert (Read : Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_dispatch E0 lr m Out_normal)
      by (apply exec_wnaf_dispatch_nonzero with (carry:=carry);try assumption;lia).
    assert (RF : wnaf_loop_fields lr bit len w carry sign b base last).
    { unfold wnaf_loop_fields,lr;repeat split;rewrite PTree.gso by discriminate;assumption. }
    destruct (exec_wnaf_nonzero_body lr m n bit len w carry sign b base bs last
      N Bit Len W Carry Different Sign RF Storage Base Max Writable)
      as (mf & Exec & Store & Final & NewCarry & Digit & Odd & Weighted).
    pose (width:=Z.min w (len-bit)).
    destruct (wnaf_window_bounds bit len w Bit Len W) as (Width & End & Advance).
    exists (wnaf_nonzero_temps lr n bit len w carry),mf,(bit+width),
      (wnaf_carry (wnaf_word n bit width carry) w),
      (wnaf_digit (wnaf_word n bit width carry) w),bit,Out_normal.
    split.
    + rewrite wnaf_dispatch_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
        [exact Read|exact Exec].
    + split;[exact Final|];split;[exact Advance|];split;[unfold width;lia|].
      split;[exact NewCarry|];split.
      * eapply wnaf_scalar_store_preserved;[exact Store|exact Separate|exact Storage].
      * split;[left;reflexivity|];split.
        -- replace (bit+width-bit) with width by lia;exact Weighted.
        -- right;split;[exact Odd|];split;[exact Digit|];split;[exact Store|reflexivity].
Qed.
