(** The original wNAF digit arithmetic/store, not a public jet theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs
  ClightBigstep Maps Memory Values Events Globalenvs.
Require Import C.jet_sx_exec C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
  C.jet_secp_fe_b32 C.jet_secp_fe_math C.jet_secp_scalar_bits_var
  C.jet_secp_curve_statements C.jet_secp_fns C.jet_secp_scalar_get_b32_storage
  C.jet_secp_scalar_get_b32_numeric.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition wnaf_word n bit width carry := (n/2^bit) mod 2^width+carry.
Definition wnaf_carry word w := word/2^(w-1).
Definition wnaf_digit word w := word-wnaf_carry word w*2^w.

Lemma wnaf_word_bounds n bit width carry : 0<=bit -> 1<=width ->
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry ->
  0<wnaf_word n bit width carry<2^width /\ wnaf_word n bit width carry mod 2=1.
Proof.
  intros Bit Width Carry Different.
  pose proof (Z.mod_pos_bound (n/2^bit) (2^width) ltac:(apply Z.pow_pos_nonneg;lia)) as Window.
  pose proof (Z.mod_pos_bound (n/2^bit) 2 ltac:(lia)) as Low.
  assert (LSB : ((n/2^bit) mod 2^width) mod 2=(n/2^bit) mod 2).
  { change 2 with (2^1);apply mod_mod_pow;lia. }
  assert (Power : 2^width mod 2=0).
  { replace width with ((width-1)+1) at 1 by lia.
    rewrite Z.pow_add_r by lia;change (2^1) with 2;apply Z.mod_mul;lia. }
  unfold wnaf_word;destruct Carry as [C|C];subst carry.
  - rewrite Z.add_0_r;assert (LowOne : (n/2^bit) mod 2=1) by lia.
    assert ((n/2^bit) mod 2^width<>0) by (intro E;rewrite E in LSB;cbn in LSB;lia).
    split;[lia|lia].
  - assert (LowZero : (n/2^bit) mod 2=0) by lia.
    split.
    + split;[lia|].
      assert ((n/2^bit) mod 2^width<>2^width-1).
      { intro E;rewrite E in LSB;rewrite Zminus_mod,Power in LSB;cbn in LSB;lia. }
      lia.
    + rewrite Z.add_mod,LSB,LowZero by lia;reflexivity.
Qed.

Lemma wnaf_digit_bounds word w : 2<=w -> 0<word<2^w -> word mod 2=1 ->
  (wnaf_carry word w=0 \/ wnaf_carry word w=1) /\
  -2^(w-1)<wnaf_digit word w<2^(w-1) /\ wnaf_digit word w mod 2=1.
Proof.
  intros Width Word Odd.
  assert (Power : 2^w=2*2^(w-1)) by
    (replace w with (1+(w-1)) at 1 by lia;rewrite Z.pow_add_r by lia;reflexivity).
  assert (Half : 0<2^(w-1)) by (apply Z.pow_pos_nonneg;lia).
  assert (C : 0<=wnaf_carry word w<2).
  { unfold wnaf_carry;split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;nia]. }
  assert (Even : 2^(w-1) mod 2=0).
  { replace (w-1) with ((w-2)+1) at 1 by lia.
    rewrite Z.pow_add_r by lia;change (2^1) with 2;apply Z.mod_mul;lia. }
  assert (Cases : wnaf_carry word w=0 \/ wnaf_carry word w=1) by lia.
  split;[exact Cases|].
  unfold wnaf_digit;destruct Cases as [Case|Case];rewrite Case.
  - rewrite Z.mul_0_l,Z.sub_0_r;split;[|exact Odd].
    assert (word<2^(w-1)).
    { pose proof (Z.div_mod word (2^(w-1)) ltac:(lia)) as D.
      pose proof (Z.mod_pos_bound word (2^(w-1)) Half) as R.
      unfold wnaf_carry in Case;rewrite Case in D;lia. }
    lia.
  - rewrite Z.mul_1_l.
    pose proof (Z.div_mod word (2^(w-1)) ltac:(lia)) as D.
    pose proof (Z.mod_pos_bound word (2^(w-1)) Half) as R.
    unfold wnaf_carry in Case;rewrite Case in D.
    assert (word<>2^(w-1)) by (intro E;rewrite E,Even in Odd;discriminate).
    split;[lia|].
    rewrite Zminus_mod,Odd,Power,Z.mul_mod,Even by lia;reflexivity.
Qed.

Lemma wnaf_step_preserves_value n bit width w carry :
  0<=bit -> 1<=width<=w -> 2<=w -> (carry=0 \/ carry=1) ->
  (n/2^bit) mod 2<>carry ->
  n/2^bit+carry=
    wnaf_digit (wnaf_word n bit width carry) w+
    2^width*(n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) w).
Proof.
  intros Bit Width W Carry Different.
  destruct (wnaf_word_bounds n bit width carry Bit ltac:(lia) Carry Different) as (Word & Odd).
  assert (Power : 2^width<=2^w) by (apply Z.pow_le_mono_r;lia).
  destruct (wnaf_digit_bounds (wnaf_word n bit width carry) w W ltac:(lia) Odd)
    as (Cases & Digit & Parity).
  assert (Cancel : wnaf_carry (wnaf_word n bit width carry) w*(2^w-2^width)=0).
  { destruct (zeq width w) as [->|Less];[ring|].
    assert (Upper : 2^width<=2^(w-1)) by (apply Z.pow_le_mono_r;lia).
    assert (Zero : wnaf_carry (wnaf_word n bit width carry) w=0).
    { unfold wnaf_carry;apply Z.div_small;lia. }
    rewrite Zero;ring. }
  rewrite <-div_div_pow by lia.
  pose proof (Z.div_mod (n/2^bit) (2^width) ltac:(apply Z.pow_nonzero;lia)) as D.
  unfold wnaf_digit,wnaf_word in *;nia.
Qed.

Lemma wnaf_mask1 x : Int.and x Int.one=Int.repr (Int.unsigned x mod 2).
Proof.
  rewrite <-(Int.repr_unsigned (Int.and x Int.one));f_equal.
  change (Int.unsigned (Int.and x (Int.repr (two_p 1-1)))=Int.unsigned x mod 2).
  rewrite <-Int.zero_ext_and by lia.
  apply Int.zero_ext_mod;change (0<=1<32);lia.
Qed.

Lemma wnaf_power_bound w : 0<=w<=31 -> 0<2^w<=2147483648.
Proof.
  intro W;split;[apply Z.pow_pos_nonneg;lia|].
  change 2147483648 with (2^31);apply Z.pow_le_mono_r;lia.
Qed.

Lemma wnaf_machine_carry word w : 2<=w<=31 -> 0<=word<2^w ->
  Int.and (Int.shr (Int.repr word) (Int.sub (Int.repr w) Int.one)) Int.one=
    Int.repr (wnaf_carry word w).
Proof.
  intros W Word.
  assert (Amount : Int.sub (Int.repr w) Int.one=Int.repr (w-1)).
  { unfold Int.sub;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity. }
  assert (Signed : Int.signed (Int.repr word)=word).
  { apply Int.signed_repr;pose proof (wnaf_power_bound w ltac:(lia)).
    change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia. }
  assert (Half : 0<2^(w-1)) by (apply Z.pow_pos_nonneg;lia).
  assert (Power : 2^w=2*2^(w-1)) by
    (replace w with (1+(w-1)) at 1 by lia;rewrite Z.pow_add_r by lia;reflexivity).
  assert (Carry : 0<=wnaf_carry word w<2).
  { unfold wnaf_carry;split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;nia]. }
  rewrite Amount,wnaf_mask1,Int.shr_div_two_p,Signed.
  rewrite (Int.unsigned_repr (w-1)) by (change Int.max_unsigned with 4294967295;lia).
  rewrite two_p_equiv.
  change (Int.repr (Int.unsigned (Int.repr (wnaf_carry word w)) mod 2)=Int.repr (wnaf_carry word w)).
  rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia).
  rewrite Z.mod_small by exact Carry;reflexivity.
Qed.

Lemma wnaf_machine_digit word w : 2<=w<=31 -> 0<=word<2^w ->
  Int.sub (Int.repr word) (Int.shl (Int.repr (wnaf_carry word w)) (Int.repr w))=
    Int.repr (wnaf_digit word w).
Proof.
  intros W Word;pose proof (wnaf_power_bound w ltac:(lia)) as Power.
  assert (Half : 0<2^(w-1)) by (apply Z.pow_pos_nonneg;lia).
  assert (Twice : 2^w=2*2^(w-1)) by
    (replace w with (1+(w-1)) at 1 by lia;rewrite Z.pow_add_r by lia;reflexivity).
  assert (Carry : 0<=wnaf_carry word w<2).
  { unfold wnaf_carry;split;[apply Z.div_pos;lia|apply Z.div_lt_upper_bound;nia]. }
  rewrite Int.shl_mul_two_p,Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia).
  rewrite two_p_equiv;unfold Int.mul,Int.sub.
  rewrite (Int.unsigned_repr word) by (change Int.max_unsigned with 4294967295;lia).
  rewrite (Int.unsigned_repr (wnaf_carry word w)) by (change Int.max_unsigned with 4294967295;lia).
  rewrite (Int.unsigned_repr (2^w)) by (change Int.max_unsigned with 4294967295;lia).
  rewrite (Int.unsigned_repr (wnaf_carry word w*2^w)) by
    (change Int.max_unsigned with 4294967295;nia).
  reflexivity.
Qed.

Definition wnaf_statements := fst (split_statement_last (fn_body f_secp256k1_ecmult_wnaf)).
Definition wnaf_loop := nth 11 wnaf_statements Sskip.
Definition wnaf_loop_body := match wnaf_loop with
  | Sloop (Ssequence _ body) Sskip=>body | _=>Sskip end.
Definition wnaf_loop_statements := fst (split_statement_last wnaf_loop_body).
Definition wnaf_word_add := match nth 3 wnaf_loop_statements Sskip with
  | Ssequence _ add=>add | _=>Sskip end.
Definition wnaf_carry_set := nth 4 wnaf_loop_statements Sskip.
Definition wnaf_digit_set := nth 5 wnaf_loop_statements Sskip.
Definition wnaf_digit_store := nth 6 wnaf_loop_statements Sskip.
Definition wnaf_digit_stage := Ssequence wnaf_word_add
  (Ssequence wnaf_carry_set (Ssequence wnaf_digit_set wnaf_digit_store)).

Lemma wnaf_loop_source : fn_body f_secp256k1_ecmult_wnaf=
  statement_sequence (firstn 11 wnaf_statements)
    (Ssequence wnaf_loop (snd (split_statement_last (fn_body f_secp256k1_ecmult_wnaf)))).
Proof. reflexivity. Qed.
Lemma wnaf_loop_body_source : wnaf_loop=
  Swhile (Ebinop Olt (Etempvar _bit tint) (Etempvar _len tint) tint) wnaf_loop_body.
Proof. reflexivity. Qed.
Lemma wnaf_digit_sources :
  wnaf_word_add=Sset _word (Ebinop Oadd (Etempvar _t'3 tuint) (Etempvar _carry tint) tuint) /\
  wnaf_carry_set=Sset _carry (Ebinop Oand
    (Ebinop Oshr (Etempvar _word tint)
      (Ebinop Osub (Etempvar _w tint) (Econst_int Int.one tint) tint) tint)
    (Econst_int Int.one tint) tint) /\
  wnaf_digit_set=Sset _word (Ebinop Osub (Etempvar _word tint)
    (Ebinop Oshl (Etempvar _carry tint) (Etempvar _w tint) tint) tint) /\
  wnaf_digit_store=Sassign (Ederef (Ebinop Oadd (Etempvar _wnaf (tptr tint))
    (Etempvar _bit tint) (tptr tint)) tint)
    (Ebinop Omul (Etempvar _sign tint) (Etempvar _word tint) tint).
Proof. repeat split;reflexivity. Qed.

Local Opaque secp_ge wnaf_word_add wnaf_carry_set wnaf_digit_set wnaf_digit_store.

Lemma exec_wnaf_digit_add e le m window carry :
  le!_t'3=Some (Vint window) -> le!_carry=Some (Vint carry) ->
  Clight2.exec_stmt secp_ge e le m wnaf_word_add E0
    (PTree.set _word (Vint (Int.add window carry)) le) m Out_normal.
Proof.
  intros HW HC;rewrite (proj1 wnaf_digit_sources);apply exec_Sset.
  eapply eval_Ebinop;[apply eval_Etempvar;exact HW|apply eval_Etempvar;exact HC|reflexivity].
Qed.

Lemma exec_wnaf_carry_set e le m word w :
  le!_word=Some (Vint (Int.repr word)) -> le!_w=Some (Vint (Int.repr w)) ->
  2<=w<=31 -> 0<=word<2^w ->
  Clight2.exec_stmt secp_ge e le m wnaf_carry_set E0
    (PTree.set _carry (Vint (Int.repr (wnaf_carry word w))) le) m Out_normal.
Proof.
  intros HW WW Width Word.
  assert (Amount : Int.sub (Int.repr w) Int.one=Int.repr (w-1)).
  { unfold Int.sub;rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);reflexivity. }
  assert (Shift : Int.ltu (Int.sub (Int.repr w) Int.one) Int.iwordsize=true).
  { rewrite Amount;unfold Int.ltu;change (Int.unsigned Int.iwordsize) with 32.
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);apply zlt_true;lia. }
  rewrite (proj1 (proj2 wnaf_digit_sources));apply exec_Sset.
  rewrite <-wnaf_machine_carry by assumption.
  eapply eval_Ebinop with (v1:=Vint (Int.shr (Int.repr word) (Int.sub (Int.repr w) Int.one)))
    (v2:=Vint Int.one).
  - eapply eval_Ebinop.
    + apply eval_Etempvar;exact HW.
    + eapply eval_Ebinop;[apply eval_Etempvar;exact WW|constructor|reflexivity].
    + change ((if Int.ltu (Int.sub (Int.repr w) Int.one) Int.iwordsize then
        Some (Vint (Int.shr (Int.repr word) (Int.sub (Int.repr w) Int.one))) else None)=
        Some (Vint (Int.shr (Int.repr word) (Int.sub (Int.repr w) Int.one)))).
      rewrite Shift;reflexivity.
  - constructor.
  - reflexivity.
Qed.

Lemma exec_wnaf_digit_set e le m word w :
  le!_word=Some (Vint (Int.repr word)) -> le!_w=Some (Vint (Int.repr w)) ->
  le!_carry=Some (Vint (Int.repr (wnaf_carry word w))) ->
  2<=w<=31 -> 0<=word<2^w ->
  Clight2.exec_stmt secp_ge e le m wnaf_digit_set E0
    (PTree.set _word (Vint (Int.repr (wnaf_digit word w))) le) m Out_normal.
Proof.
  intros HW WW HC Width Word.
  assert (Shift : Int.ltu (Int.repr w) Int.iwordsize=true).
  { unfold Int.ltu;change (Int.unsigned Int.iwordsize) with 32.
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295;lia);apply zlt_true;lia. }
  rewrite (proj1 (proj2 (proj2 wnaf_digit_sources)));apply exec_Sset.
  rewrite <-wnaf_machine_digit by assumption.
  eapply eval_Ebinop with (v1:=Vint (Int.repr word))
    (v2:=Vint (Int.shl (Int.repr (wnaf_carry word w)) (Int.repr w))).
  - apply eval_Etempvar;exact HW.
  - eapply eval_Ebinop.
    + apply eval_Etempvar;exact HC.
    + apply eval_Etempvar;exact WW.
    + change ((if Int.ltu (Int.repr w) Int.iwordsize then
        Some (Vint (Int.shl (Int.repr (wnaf_carry word w)) (Int.repr w))) else None)=
        Some (Vint (Int.shl (Int.repr (wnaf_carry word w)) (Int.repr w)))).
      rewrite Shift;reflexivity.
  - reflexivity.
Qed.

Lemma exec_wnaf_digit_store e le m b base bit sign digit mf :
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_bit=Some (Vint (Int.repr bit)) ->
  le!_sign=Some (Vint (Int.repr sign)) -> le!_word=Some (Vint (Int.repr digit)) ->
  0<=bit<256 -> 0<=base -> base+4*bit<=Ptrofs.max_unsigned ->
  -2147483648<=sign<=2147483647 -> -2147483648<=digit<=2147483647 ->
  Mem.store Mint32 m b (base+4*bit) (Vint (Int.repr (sign*digit)))=Some mf ->
  Clight2.exec_stmt secp_ge e le m wnaf_digit_store E0 le mf Out_normal.
Proof.
  intros Ptr Bit Sign Digit Bounds Base Max SBound DBound Store.
  assert (IS : Int.signed (Int.repr bit)=bit) by
    (apply Int.signed_repr;change Int.min_signed with (-2147483648);
     change Int.max_signed with 2147483647;lia).
  rewrite (proj2 (proj2 (proj2 wnaf_digit_sources))).
  eapply exec_Sassign with (loc:=b) (ofs:=Ptrofs.repr (base+4*bit))
    (v2:=Vint (Int.repr (sign*digit))) (v:=Vint (Int.repr (sign*digit))).
  - apply eval_Ederef;eapply eval_Ebinop.
    + apply eval_Etempvar;exact Ptr.
    + apply eval_Etempvar;exact Bit.
    + change (Some (Vptr b (Ptrofs.add (Ptrofs.repr base)
        (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.repr (Int.signed (Int.repr bit))))))=
        Some (Vptr b (Ptrofs.repr (base+4*bit)))).
      rewrite IS;unfold Ptrofs.add,Ptrofs.mul.
      rewrite (Ptrofs.unsigned_repr 4) by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr bit) by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr (4*bit)) by (change Ptrofs.max_unsigned with 18446744073709551615;lia).
      rewrite (Ptrofs.unsigned_repr base) by
        (change Ptrofs.max_unsigned with 18446744073709551615 in *;lia);reflexivity.
  - eapply eval_Ebinop.
    + apply eval_Etempvar;exact Sign.
    + apply eval_Etempvar;exact Digit.
    + change (Some (Vint (Int.mul (Int.repr sign) (Int.repr digit)))=
        Some (Vint (Int.repr (sign*digit)))).
      rewrite Int.mul_signed,!Int.signed_repr by
        (change Int.min_signed with (-2147483648);change Int.max_signed with 2147483647;lia).
      reflexivity.
  - reflexivity.
  - apply assign_loc_value with (chunk:=Mint32);[reflexivity|].
    cbn [Mem.storev];rewrite Ptrofs.unsigned_repr;[exact Store|lia].
Qed.

Definition wnaf_digit_final le word w := PTree.set _word (Vint (Int.repr (wnaf_digit word w)))
  (PTree.set _carry (Vint (Int.repr (wnaf_carry word w)))
    (PTree.set _word (Vint (Int.repr word)) le)).

Theorem exec_wnaf_digit_stage e le m n bit width w carry b base sign :
  0<=bit<256 -> 1<=width<=w -> 2<=w<=31 ->
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry -> (sign=1 \/ sign= -1) ->
  le!_t'3=Some (Vint (Int.repr ((n/2^bit) mod 2^width))) ->
  le!_carry=Some (Vint (Int.repr carry)) -> le!_w=Some (Vint (Int.repr w)) ->
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_bit=Some (Vint (Int.repr bit)) ->
  le!_sign=Some (Vint (Int.repr sign)) ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned ->
  Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  exists mf,
    Clight2.exec_stmt secp_ge e le m wnaf_digit_stage E0
      (wnaf_digit_final le (wnaf_word n bit width carry) w) mf Out_normal /\
    Mem.store Mint32 m b (base+4*bit)
      (Vint (Int.repr (sign*wnaf_digit (wnaf_word n bit width carry) w)))=Some mf /\
    Mem.load Mint32 mf b (base+4*bit)=
      Some (Vint (Int.repr (sign*wnaf_digit (wnaf_word n bit width carry) w))) /\
    (wnaf_carry (wnaf_word n bit width carry) w=0 \/ wnaf_carry (wnaf_word n bit width carry) w=1) /\
    -2^(w-1)<wnaf_digit (wnaf_word n bit width carry) w<2^(w-1) /\
    wnaf_digit (wnaf_word n bit width carry) w mod 2=1 /\
    n/2^bit+carry=wnaf_digit (wnaf_word n bit width carry) w+
      2^width*(n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) w).
Proof.
  intros Bit Width W Carry Different Sign HT HC HW HP HB HS Base Max Writable.
  destruct (wnaf_word_bounds n bit width carry ltac:(lia) ltac:(lia) Carry Different) as (Word & Odd).
  assert (Power : 2^width<=2^w) by (apply Z.pow_le_mono_r;lia).
  destruct (wnaf_digit_bounds (wnaf_word n bit width carry) w ltac:(lia) ltac:(lia) Odd)
    as (NewCarry & Digit & NewOdd).
  assert (Half : 0<2^(w-1)<=1073741824).
  { split;[apply Z.pow_pos_nonneg;lia|].
    change 1073741824 with (2^30);apply Z.pow_le_mono_r;lia. }
  destruct (Mem.valid_access_store m Mint32 b (base+4*bit)
    (Vint (Int.repr (sign*wnaf_digit (wnaf_word n bit width carry) w))) Writable) as (mf & Store).
  assert (Added : Int.add (Int.repr ((n/2^bit) mod 2^width)) (Int.repr carry)=
    Int.repr (wnaf_word n bit width carry)).
  { pose proof (Z.mod_pos_bound (n/2^bit) (2^width) ltac:(apply Z.pow_pos_nonneg;lia)) as Window.
    pose proof (wnaf_power_bound w ltac:(lia)) as Big.
    unfold Int.add;rewrite !Int.unsigned_repr by
      (change Int.max_unsigned with 4294967295;destruct Carry;nia);reflexivity. }
  exists mf;split.
  - unfold wnaf_digit_stage,wnaf_digit_final.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
      (le1:=PTree.set _word (Vint (Int.repr (wnaf_word n bit width carry))) le).
    + rewrite <-Added;apply exec_wnaf_digit_add;assumption.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
        (le1:=PTree.set _carry (Vint (Int.repr (wnaf_carry (wnaf_word n bit width carry) w)))
          (PTree.set _word (Vint (Int.repr (wnaf_word n bit width carry))) le)).
      * apply exec_wnaf_carry_set;try assumption;try lia.
        -- apply PTree.gss.
        -- rewrite PTree.gso by discriminate;exact HW.
      * eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m)
          (le1:=wnaf_digit_final le (wnaf_word n bit width carry) w).
        -- apply exec_wnaf_digit_set;try assumption;try lia.
           ++ rewrite PTree.gso by discriminate;apply PTree.gss.
           ++ rewrite !PTree.gso by discriminate;exact HW.
           ++ apply PTree.gss.
        -- apply exec_wnaf_digit_store with (b:=b) (base:=base) (bit:=bit)
             (sign:=sign) (digit:=wnaf_digit (wnaf_word n bit width carry) w);
             try assumption;try lia;unfold wnaf_digit_final.
           ++ rewrite !PTree.gso by discriminate;exact HP.
           ++ rewrite !PTree.gso by discriminate;exact HB.
           ++ rewrite !PTree.gso by discriminate;exact HS.
           ++ apply PTree.gss.
  - split;[exact Store|];split.
    + rewrite (Mem.load_store_same _ _ _ _ _ _ Store);reflexivity.
    + repeat split;try assumption;try lia.
      apply wnaf_step_preserves_value;try assumption;lia.
Qed.

Definition wnaf_window_call := match nth 3 wnaf_loop_statements Sskip with
  | Ssequence call _=>call | _=>Sskip end.
Definition wnaf_window_digit := Ssequence (Ssequence wnaf_window_call wnaf_word_add)
  (Ssequence wnaf_carry_set (Ssequence wnaf_digit_set wnaf_digit_store)).
Definition wnaf_after_digit := statement_sequence (skipn 7 wnaf_loop_statements)
  (snd (split_statement_last wnaf_loop_body)).
Definition wnaf_env bs := PTree.set _s (bs,Tstruct __5826 noattr) empty_env.

Lemma wnaf_window_call_source : wnaf_window_call=
  curve_call _secp256k1_scalar_get_bits_var f_secp256k1_scalar_get_bits_var (Some _t'3)
    [Eaddrof (Evar _s (Tstruct __5826 noattr)) (tptr (Tstruct __5826 noattr));
      Etempvar _bit tint;Etempvar _now tint].
Proof. reflexivity. Qed.
Lemma wnaf_loop_digit_source : wnaf_loop_body=
  statement_sequence (firstn 3 wnaf_loop_statements)
    (Ssequence (Ssequence wnaf_window_call wnaf_word_add)
      (Ssequence wnaf_carry_set (Ssequence wnaf_digit_set
        (Ssequence wnaf_digit_store wnaf_after_digit)))).
Proof. reflexivity. Qed.

Lemma exec_wnaf_seq_pair e le m a b c le1 m1 le2 m2 out :
  Clight2.exec_stmt secp_ge e le m a E0 le1 m1 Out_normal ->
  Clight2.exec_stmt secp_ge e le1 m1 (Ssequence b c) E0 le2 m2 out ->
  Clight2.exec_stmt secp_ge e le m (Ssequence (Ssequence a b) c) E0 le2 m2 out.
Proof.
  intros A BC;inversion BC;subst.
  - match goal with H : ?t1 ** ?t2=E0 |- _ =>
      destruct (Eapp_E0_inv t1 t2 H) as [-> ->] end.
    eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
    + eassumption.
  - eapply exec_Sseq_2.
    + eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);eassumption.
    + assumption.
Qed.

Theorem exec_wnaf_window_digit le m n bit width w carry b base sign bs :
  0<=n<2^256 -> 0<=bit<256 -> 1<=width<=w -> 2<=w<=31 -> bit+width<=256 ->
  (carry=0 \/ carry=1) -> (n/2^bit) mod 2<>carry -> (sign=1 \/ sign= -1) ->
  le!_now=Some (Vint (Int.repr width)) ->
  le!_carry=Some (Vint (Int.repr carry)) -> le!_w=Some (Vint (Int.repr w)) ->
  le!_wnaf=Some (Vptr b (Ptrofs.repr base)) -> le!_bit=Some (Vint (Int.repr bit)) ->
  le!_sign=Some (Vint (Int.repr sign)) ->
  scalar_at m bs 0 (map Int64.repr (scalar_limbs_of n)) ->
  0<=base -> base+4*bit<=Ptrofs.max_unsigned ->
  Mem.valid_access m Mint32 b (base+4*bit) Writable ->
  exists mf,
    Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_window_digit E0
      (wnaf_digit_final (PTree.set _t'3 (Vint (Int.repr ((n/2^bit) mod 2^width))) le)
        (wnaf_word n bit width carry) w) mf Out_normal /\
    Mem.store Mint32 m b (base+4*bit)
      (Vint (Int.repr (sign*wnaf_digit (wnaf_word n bit width carry) w)))=Some mf /\
    Mem.load Mint32 mf b (base+4*bit)=
      Some (Vint (Int.repr (sign*wnaf_digit (wnaf_word n bit width carry) w))) /\
    (wnaf_carry (wnaf_word n bit width carry) w=0 \/ wnaf_carry (wnaf_word n bit width carry) w=1) /\
    -2^(w-1)<wnaf_digit (wnaf_word n bit width carry) w<2^(w-1) /\
    wnaf_digit (wnaf_word n bit width carry) w mod 2=1 /\
    n/2^bit+carry=wnaf_digit (wnaf_word n bit width carry) w+
      2^width*(n/2^(bit+width)+wnaf_carry (wnaf_word n bit width carry) w).
Proof.
  intros N Bit Width W End Carry Different Sign HNow HC HW HP HB HS Storage Base Max Writable.
  pose (lr:=PTree.set _t'3 (Vint (Int.repr ((n/2^bit) mod 2^width))) le).
  assert (Read : Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_window_call E0 lr m Out_normal).
  { rewrite wnaf_window_call_source;unfold lr.
    eapply exec_curve_call with (vargs:=[Vptr bs Ptrofs.zero;Vint (Int.repr bit);Vint (Int.repr width)])
      (v:=Vint (Int.repr ((n/2^bit) mod 2^width))).
    - unfold secp_pure;repeat (first [left;reflexivity|right]).
    - reflexivity.
    - eapply eval_Econs.
      + apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
      + reflexivity.
      + eapply eval_Econs;[apply eval_Etempvar;exact HB|reflexivity|].
        eapply eval_Econs;[apply eval_Etempvar;exact HNow|reflexivity|constructor].
    - exact (eval_scalar_get_bits_var_slice m bs 0 n bit width N Bit ltac:(lia) End Storage). }
  assert (LC : lr!_carry=Some (Vint (Int.repr carry))) by
    (unfold lr;rewrite PTree.gso by discriminate;exact HC).
  assert (LW : lr!_w=Some (Vint (Int.repr w))) by
    (unfold lr;rewrite PTree.gso by discriminate;exact HW).
  assert (LP : lr!_wnaf=Some (Vptr b (Ptrofs.repr base))) by
    (unfold lr;rewrite PTree.gso by discriminate;exact HP).
  assert (LB : lr!_bit=Some (Vint (Int.repr bit))) by
    (unfold lr;rewrite PTree.gso by discriminate;exact HB).
  assert (LS : lr!_sign=Some (Vint (Int.repr sign))) by
    (unfold lr;rewrite PTree.gso by discriminate;exact HS).
  destruct (exec_wnaf_digit_stage (wnaf_env bs) lr m n bit width w carry b base sign
    Bit Width W Carry Different Sign ltac:(unfold lr;apply PTree.gss)
    LC LW LP LB LS Base Max Writable)
    as (mf & Exec & Store & Load & NewCarry & Digit & Odd & Weighted).
  exists mf;split.
  - unfold wnaf_window_digit;eapply exec_wnaf_seq_pair;[exact Read|exact Exec].
  - split;[exact Store|];split;[exact Load|];split;[exact NewCarry|];
      split;[exact Digit|];split;assumption.
Qed.
