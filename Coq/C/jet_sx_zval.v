(** Integer reading of symbolic expressions: [zval] is the unsigned
    mathematical value of an expression computed without wrap-around, and
    the interval analysis [zb] checks, from bounds on the variables, that no
    operation wraps, so that the machine value equals [zval]. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Maps Values Memory.
Require Import C.jet_sx_expr.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 300.

Definition b2z (b : bool) : Z := if b then 1 else 0.
Definition zcmp (c : comparison) (a b : Z) : bool :=
  match c with
  | Ceq => Z.eqb a b | Cne => negb (Z.eqb a b)
  | Clt => Z.ltb a b | Cle => negb (Z.ltb b a)
  | Cgt => Z.ltb b a | Cge => negb (Z.ltb a b)
  end.
Definition zop (o : bop) (a b : Z) : Z :=
  match o with
  | Badd => a + b | Bsub => a - b | Bmul => a * b
  | Band => Z.land a b | Bor => Z.lor a b | Bxor => Z.lxor a b
  end.

Fixpoint zval (ρ : nat -> Z) (x : sx) : Z :=
  match x with
  | XI i | XIc i => Int.unsigned i
  | XL l | XLc l => Int64.unsigned l
  | XLv n => ρ n
  | XIb o a b | XLb o a b => zop o (zval ρ a) (zval ρ b)
  | XIsh Hshl a k | XLsh Hshl a k => zval ρ a * 2 ^ k
  | XIsh _ a k | XLsh _ a k => zval ρ a / 2 ^ k
  | XIcmp c _ a b | XLcmp c _ a b => b2z (zcmp c (zval ρ a) (zval ρ b))
  | XI2L _ a => zval ρ a
  | XL2I a => zval ρ a mod 2 ^ 32
  | XIcast I8 Unsigned a => zval ρ a mod 2 ^ 8
  | XIcast I16 Unsigned a => zval ρ a mod 2 ^ 16
  | XIcast _ _ a => zval ρ a
  | XInz a | XLnz a => b2z (negb (Z.eqb (zval ρ a) 0))
  | XIz a | XLz a => b2z (Z.eqb (zval ρ a) 0)
  | _ => 0
  end.

Definition M32 : Z := 4294967295.
Definition M64 : Z := 18446744073709551615.

(** Bound of a bitwise or/xor of two values below [h]. *)
Definition orb_hi (ha hb : Z) : Z := 2 ^ (Z.log2 (Z.max ha hb) + 1) - 1.

Definition zb_op (mx : Z) (o : bop) (la ha lb hb : Z) : option (Z * Z) :=
  match o with
  | Badd => if Z.leb (ha + hb) mx then Some (la + lb, ha + hb) else None
  | Bsub => if Z.leb 0 (la - hb) then Some (la - hb, ha - lb) else None
  | Bmul => if Z.leb (ha * hb) mx then Some (Z.max 0 la * Z.max 0 lb, ha * hb) else None
  | Band => Some (0, Z.min ha hb)
  | Bor | Bxor => if Z.leb (orb_hi ha hb) mx then Some (0, orb_hi ha hb) else None
  end.

Definition zb_sh (w : Z) (mx : Z) (o : shop) (la ha k : Z) : option (Z * Z) :=
  if Z.leb 0 k && Z.ltb k w then
    match o with
    | Hshl => if Z.leb (ha * 2 ^ k) mx then Some (la * 2 ^ k, ha * 2 ^ k) else None
    | Hshru => Some (la / 2 ^ k, ha / 2 ^ k)
    | Hshr => if Z.ltb ha (2 ^ (w - 1)) then Some (la / 2 ^ k, ha / 2 ^ k) else None
    end
  else None.

Fixpoint zb (bnd : nat -> Z * Z) (x : sx) : option (Z * Z) :=
  match x with
  | XIc i => Some (Int.unsigned i, Int.unsigned i)
  | XLc l => Some (Int64.unsigned l, Int64.unsigned l)
  | XLv n => Some (bnd n)
  | XIb o a b =>
      if isk KI a && isk KI b then
        match zb bnd a, zb bnd b with
        | Some (la, ha), Some (lb, hb) => zb_op M32 o la ha lb hb
        | _, _ => None
        end
      else None
  | XLb o a b =>
      if isk KL a && isk KL b then
        match zb bnd a, zb bnd b with
        | Some (la, ha), Some (lb, hb) => zb_op M64 o la ha lb hb
        | _, _ => None
        end
      else None
  | XIsh o a k =>
      if isk KI a then
        match zb bnd a with Some (la, ha) => zb_sh 32 M32 o la ha k | None => None end
      else None
  | XLsh o a k =>
      if isk KL a then
        match zb bnd a with Some (la, ha) => zb_sh 64 M64 o la ha k | None => None end
      else None
  | XIcmp c sg a b =>
      if isk KI a && isk KI b then
        match zb bnd a, zb bnd b with
        | Some (la, ha), Some (lb, hb) =>
            match sg with
            | Unsigned => Some (0, 1)
            | Signed => if Z.ltb ha (2 ^ 31) && Z.ltb hb (2 ^ 31) then Some (0, 1) else None
            end
        | _, _ => None
        end
      else None
  | XLcmp c sg a b =>
      if isk KL a && isk KL b then
        match zb bnd a, zb bnd b with
        | Some (la, ha), Some (lb, hb) =>
            match sg with
            | Unsigned => Some (0, 1)
            | Signed => if Z.ltb ha (2 ^ 63) && Z.ltb hb (2 ^ 63) then Some (0, 1) else None
            end
        | _, _ => None
        end
      else None
  | XI2L sg a =>
      if isk KI a then
        match zb bnd a with
        | Some (la, ha) =>
            match sg with
            | Unsigned => Some (la, ha)
            | Signed => if Z.ltb ha (2 ^ 31) then Some (la, ha) else None
            end
        | None => None
        end
      else None
  | XL2I a =>
      if isk KL a then
        match zb bnd a with
        | Some (la, ha) => if Z.leb ha M32 then Some (la, ha) else Some (0, M32)
        | None => None
        end
      else None
  | XIcast I8 Unsigned a =>
      if isk KI a then match zb bnd a with Some _ => Some (0, 255) | None => None end else None
  | XIcast I16 Unsigned a =>
      if isk KI a then match zb bnd a with Some _ => Some (0, 65535) | None => None end else None
  | XInz a | XIz a =>
      if isk KI a then match zb bnd a with Some _ => Some (0, 1) | None => None end else None
  | XLnz a | XLz a =>
      if isk KL a then match zb bnd a with Some _ => Some (0, 1) | None => None end else None
  | _ => None
  end.

(** ** Arithmetic facts *)
Lemma land_range a b n : 0 <= a < 2 ^ n -> 0 <= b -> 0 <= n -> 0 <= Z.land a b < 2 ^ n.
Proof.
  intros Ha Hb Hn. assert (H0 : 0 <= Z.land a b) by (apply Z.land_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec (Z.land a b) 0) as [->|Hne]; [lia|].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_land a b ltac:(lia) Hb).
  assert (Z.log2 a < n) by (apply Z.log2_lt_pow2; [|lia]; destruct (Z.eq_dec a 0); [subst; rewrite Z.land_0_l in Hne; congruence|lia]).
  lia.
Qed.

Lemma lor_range a b h : 0 <= a <= h -> 0 <= b <= h -> 0 <= Z.lor a b <= 2 ^ (Z.log2 h + 1) - 1.
Proof.
  intros Ha Hb. assert (H0 : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [->|Hne].
  { pose proof (Z.log2_nonneg h). assert (0 < 2 ^ (Z.log2 h + 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
  assert (Z.lor a b < 2 ^ (Z.log2 h + 1)); [|lia].
  apply Z.log2_lt_pow2; [lia|].
  rewrite Z.log2_lor by lia.
  pose proof (Z.log2_le_mono a h ltac:(lia)). pose proof (Z.log2_le_mono b h ltac:(lia)). lia.
Qed.

Lemma lxor_range a b h : 0 <= a <= h -> 0 <= b <= h -> 0 <= Z.lxor a b <= 2 ^ (Z.log2 h + 1) - 1.
Proof.
  intros Ha Hb. assert (H0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact H0|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [->|Hne].
  { pose proof (Z.log2_nonneg h). assert (0 < 2 ^ (Z.log2 h + 1)) by (apply Z.pow_pos_nonneg; lia). lia. }
  assert (Z.lxor a b < 2 ^ (Z.log2 h + 1)); [|lia].
  apply Z.log2_lt_pow2; [lia|].
  pose proof (Z.log2_lxor a b ltac:(lia) ltac:(lia)).
  pose proof (Z.log2_le_mono a h ltac:(lia)). pose proof (Z.log2_le_mono b h ltac:(lia)). lia.
Qed.

Lemma op64_sound o (a b : int64) la ha lb hb lo hi :
  zb_op M64 o la ha lb hb = Some (lo, hi) ->
  la <= Int64.unsigned a <= ha -> lb <= Int64.unsigned b <= hb ->
  Int64.unsigned (lop o a b) = zop o (Int64.unsigned a) (Int64.unsigned b) /\
  lo <= zop o (Int64.unsigned a) (Int64.unsigned b) <= hi.
Proof.
  intros H Ha Hb. pose proof (Int64.unsigned_range a) as Ra. pose proof (Int64.unsigned_range b) as Rb.
  change Int64.modulus with 18446744073709551616 in *. unfold M64 in H.
  destruct o; simpl in *.
  - destruct (Z.leb (ha + hb) 18446744073709551615) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst. unfold Int64.add. rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). lia.
  - destruct (Z.leb 0 (la - hb)) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst. unfold Int64.sub. rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). lia.
  - destruct (Z.leb (ha * hb) 18446744073709551615) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    assert (Int64.unsigned a * Int64.unsigned b <= ha * hb) by (apply Z.mul_le_mono_nonneg; lia).
    assert (Z.max 0 la * Z.max 0 lb <= Int64.unsigned a * Int64.unsigned b) by (apply Z.mul_le_mono_nonneg; lia).
    assert (0 <= Int64.unsigned a * Int64.unsigned b) by (apply Z.mul_nonneg_nonneg; lia).
    unfold Int64.mul. rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    split; [reflexivity|]. lia.
  - inversion H; subst.
    pose proof (land_range (Int64.unsigned a) (Int64.unsigned b) 64 ltac:(change (2^64) with 18446744073709551616; lia) ltac:(lia) ltac:(lia)) as Hr.
    change (2 ^ 64) with 18446744073709551616 in Hr.
    assert (E : Int64.unsigned (Int64.and a b) = Z.land (Int64.unsigned a) (Int64.unsigned b)).
    { unfold Int64.and. apply Int64.unsigned_repr. change Int64.max_unsigned with 18446744073709551615. lia. }
    split; [exact E|]. rewrite <- E.
    pose proof (Int64.and_le a b). pose proof (Int64.and_le b a). rewrite (Int64.and_commut b a) in H1.
    pose proof (Int64.unsigned_range (Int64.and a b)). lia.
  - destruct (Z.leb (orb_hi ha hb) 18446744073709551615) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    pose proof (lor_range (Int64.unsigned a) (Int64.unsigned b) (Z.max ha hb) ltac:(lia) ltac:(lia)) as Hr.
    unfold orb_hi in *.
    unfold Int64.or. rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). lia.
  - destruct (Z.leb (orb_hi ha hb) 18446744073709551615) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    pose proof (lxor_range (Int64.unsigned a) (Int64.unsigned b) (Z.max ha hb) ltac:(lia) ltac:(lia)) as Hr.
    unfold orb_hi in *.
    unfold Int64.xor. rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). lia.
Qed.

Lemma op32_sound o (a b : int) la ha lb hb lo hi :
  zb_op M32 o la ha lb hb = Some (lo, hi) ->
  la <= Int.unsigned a <= ha -> lb <= Int.unsigned b <= hb ->
  Int.unsigned (iop o a b) = zop o (Int.unsigned a) (Int.unsigned b) /\
  lo <= zop o (Int.unsigned a) (Int.unsigned b) <= hi.
Proof.
  intros H Ha Hb. pose proof (Int.unsigned_range a) as Ra. pose proof (Int.unsigned_range b) as Rb.
  change Int.modulus with 4294967296 in *. unfold M32 in H.
  destruct o; simpl in *.
  - destruct (Z.leb (ha + hb) 4294967295) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst. unfold Int.add. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia). lia.
  - destruct (Z.leb 0 (la - hb)) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst. unfold Int.sub. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia). lia.
  - destruct (Z.leb (ha * hb) 4294967295) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    assert (Int.unsigned a * Int.unsigned b <= ha * hb) by (apply Z.mul_le_mono_nonneg; lia).
    assert (Z.max 0 la * Z.max 0 lb <= Int.unsigned a * Int.unsigned b) by (apply Z.mul_le_mono_nonneg; lia).
    assert (0 <= Int.unsigned a * Int.unsigned b) by (apply Z.mul_nonneg_nonneg; lia).
    unfold Int.mul. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    split; [reflexivity|]. lia.
  - inversion H; subst.
    pose proof (land_range (Int.unsigned a) (Int.unsigned b) 32 ltac:(change (2^32) with 4294967296; lia) ltac:(lia) ltac:(lia)) as Hr.
    change (2 ^ 32) with 4294967296 in Hr.
    assert (E : Int.unsigned (Int.and a b) = Z.land (Int.unsigned a) (Int.unsigned b)).
    { unfold Int.and. apply Int.unsigned_repr. change Int.max_unsigned with 4294967295. lia. }
    split; [exact E|]. rewrite <- E.
    pose proof (Int.and_le a b). pose proof (Int.and_le b a). rewrite (Int.and_commut b a) in H1.
    pose proof (Int.unsigned_range (Int.and a b)). lia.
  - destruct (Z.leb (orb_hi ha hb) 4294967295) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    pose proof (lor_range (Int.unsigned a) (Int.unsigned b) (Z.max ha hb) ltac:(lia) ltac:(lia)) as Hr.
    unfold orb_hi in *.
    unfold Int.or. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia). lia.
  - destruct (Z.leb (orb_hi ha hb) 4294967295) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    pose proof (lxor_range (Int.unsigned a) (Int.unsigned b) (Z.max ha hb) ltac:(lia) ltac:(lia)) as Hr.
    unfold orb_hi in *.
    unfold Int.xor. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia). lia.
Qed.

Lemma pow2_pos k : 0 <= k -> 0 < 2 ^ k.
Proof. intros. apply Z.pow_pos_nonneg; lia. Qed.

Lemma sh64_sound o (a : int64) la ha k lo hi :
  zb_sh 64 M64 o la ha k = Some (lo, hi) -> la <= Int64.unsigned a <= ha ->
  Int64.unsigned (lsh o a k) =
    match o with Hshl => Int64.unsigned a * 2 ^ k | _ => Int64.unsigned a / 2 ^ k end /\
  lo <= match o with Hshl => Int64.unsigned a * 2 ^ k | _ => Int64.unsigned a / 2 ^ k end <= hi.
Proof.
  unfold zb_sh, M64. intros H Ha. pose proof (Int64.unsigned_range a) as Ra.
  change Int64.modulus with 18446744073709551616 in *.
  destruct (Z.leb 0 k && Z.ltb k 64) eqn:K; [|discriminate].
  apply andb_true_iff in K. destruct K as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
  assert (Hk : Int64.unsigned (Int64.repr k) = k)
    by (apply Int64.unsigned_repr; change Int64.max_unsigned with 18446744073709551615; lia).
  pose proof (pow2_pos k K1) as Hp.
  assert (Hp64 : 2 ^ k <= 2 ^ 63) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 63) with 9223372036854775808 in Hp64.
  destruct o; simpl.
  - destruct (Z.leb (ha * 2 ^ k) 18446744073709551615) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    assert (Int64.unsigned a * 2 ^ k <= ha * 2 ^ k) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (la * 2 ^ k <= Int64.unsigned a * 2 ^ k) by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite Int64.shl_mul_two_p, Hk, two_p_equiv. unfold Int64.mul.
    rewrite (Int64.unsigned_repr (2 ^ k)) by (change Int64.max_unsigned with 18446744073709551615; lia).
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; nia). lia.
  - destruct (Z.ltb ha (2 ^ (64 - 1))) eqn:L; [|discriminate]. apply Z.ltb_lt in L.
    change (2 ^ (64 - 1)) with 9223372036854775808 in L.
    inversion H; subst.
    rewrite Int64.shr_div_two_p, Hk, two_p_equiv.
    rewrite Int64.signed_eq_unsigned by (change Int64.max_signed with 9223372036854775807; lia).
    assert (0 <= Int64.unsigned a / 2 ^ k <= Int64.unsigned a) by
      (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; nia]).
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    split; [reflexivity|]. split; apply Z.div_le_mono; lia.
  - inversion H; subst.
    rewrite Int64.shru_div_two_p, Hk, two_p_equiv.
    assert (0 <= Int64.unsigned a / 2 ^ k <= Int64.unsigned a) by
      (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; nia]).
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
    split; [reflexivity|]. split; apply Z.div_le_mono; lia.
Qed.

Lemma sh32_sound o (a : int) la ha k lo hi :
  zb_sh 32 M32 o la ha k = Some (lo, hi) -> la <= Int.unsigned a <= ha ->
  Int.unsigned (ish o a k) =
    match o with Hshl => Int.unsigned a * 2 ^ k | _ => Int.unsigned a / 2 ^ k end /\
  lo <= match o with Hshl => Int.unsigned a * 2 ^ k | _ => Int.unsigned a / 2 ^ k end <= hi.
Proof.
  unfold zb_sh, M32. intros H Ha. pose proof (Int.unsigned_range a) as Ra.
  change Int.modulus with 4294967296 in *.
  destruct (Z.leb 0 k && Z.ltb k 32) eqn:K; [|discriminate].
  apply andb_true_iff in K. destruct K as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2.
  assert (Hk : Int.unsigned (Int.repr k) = k)
    by (apply Int.unsigned_repr; change Int.max_unsigned with 4294967295; lia).
  pose proof (pow2_pos k K1) as Hp.
  assert (Hp32 : 2 ^ k <= 2 ^ 31) by (apply Z.pow_le_mono_r; lia).
  change (2 ^ 31) with 2147483648 in Hp32.
  destruct o; simpl.
  - destruct (Z.leb (ha * 2 ^ k) 4294967295) eqn:L; [|discriminate]. apply Z.leb_le in L.
    inversion H; subst.
    assert (Int.unsigned a * 2 ^ k <= ha * 2 ^ k) by (apply Z.mul_le_mono_nonneg_r; lia).
    assert (la * 2 ^ k <= Int.unsigned a * 2 ^ k) by (apply Z.mul_le_mono_nonneg_r; lia).
    rewrite Int.shl_mul_two_p, Hk, two_p_equiv. unfold Int.mul.
    rewrite (Int.unsigned_repr (2 ^ k)) by (change Int.max_unsigned with 4294967295; lia).
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; nia). lia.
  - destruct (Z.ltb ha (2 ^ (32 - 1))) eqn:L; [|discriminate]. apply Z.ltb_lt in L.
    change (2 ^ (32 - 1)) with 2147483648 in L.
    inversion H; subst.
    rewrite Int.shr_div_two_p, Hk, two_p_equiv.
    rewrite Int.signed_eq_unsigned by (change Int.max_signed with 2147483647; lia).
    assert (0 <= Int.unsigned a / 2 ^ k <= Int.unsigned a) by
      (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; nia]).
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    split; [reflexivity|]. split; apply Z.div_le_mono; lia.
  - inversion H; subst.
    rewrite Int.shru_div_two_p, Hk, two_p_equiv.
    assert (0 <= Int.unsigned a / 2 ^ k <= Int.unsigned a) by
      (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; nia]).
    rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    split; [reflexivity|]. split; apply Z.div_le_mono; lia.
Qed.

Lemma cmpu64_zcmp c a b : Int64.cmpu c a b = zcmp c (Int64.unsigned a) (Int64.unsigned b).
Proof.
  unfold Int64.cmpu, Int64.eq, Int64.ltu, zcmp.
  destruct c;
    repeat match goal with |- context[zeq ?x ?y] => destruct (zeq x y) end;
    repeat match goal with |- context[zlt ?x ?y] => destruct (zlt x y) end; simpl;
    repeat match goal with |- context[Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end;
    repeat match goal with |- context[Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; simpl; try reflexivity; lia.
Qed.

Lemma cmpu32_zcmp c a b : Int.cmpu c a b = zcmp c (Int.unsigned a) (Int.unsigned b).
Proof.
  unfold Int.cmpu, Int.eq, Int.ltu, zcmp.
  destruct c;
    repeat match goal with |- context[zeq ?x ?y] => destruct (zeq x y) end;
    repeat match goal with |- context[zlt ?x ?y] => destruct (zlt x y) end; simpl;
    repeat match goal with |- context[Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end;
    repeat match goal with |- context[Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; simpl; try reflexivity; lia.
Qed.

Lemma cmp64_zcmp c a b :
  Int64.unsigned a < 2 ^ 63 -> Int64.unsigned b < 2 ^ 63 ->
  Int64.cmp c a b = zcmp c (Int64.unsigned a) (Int64.unsigned b).
Proof.
  change (2 ^ 63) with 9223372036854775808. intros Ha Hb.
  unfold Int64.cmp, Int64.eq, Int64.lt, zcmp.
  rewrite !(Int64.signed_eq_unsigned a), !(Int64.signed_eq_unsigned b)
    by (change Int64.max_signed with 9223372036854775807; lia).
  destruct c;
    repeat match goal with |- context[zeq ?x ?y] => destruct (zeq x y) end;
    repeat match goal with |- context[zlt ?x ?y] => destruct (zlt x y) end; simpl;
    repeat match goal with |- context[Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end;
    repeat match goal with |- context[Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; simpl; try reflexivity; lia.
Qed.

Lemma cmp32_zcmp c a b :
  Int.unsigned a < 2 ^ 31 -> Int.unsigned b < 2 ^ 31 ->
  Int.cmp c a b = zcmp c (Int.unsigned a) (Int.unsigned b).
Proof.
  change (2 ^ 31) with 2147483648. intros Ha Hb.
  unfold Int.cmp, Int.eq, Int.lt, zcmp.
  rewrite !(Int.signed_eq_unsigned a), !(Int.signed_eq_unsigned b)
    by (change Int.max_signed with 2147483647; lia).
  destruct c;
    repeat match goal with |- context[zeq ?x ?y] => destruct (zeq x y) end;
    repeat match goal with |- context[zlt ?x ?y] => destruct (zlt x y) end; simpl;
    repeat match goal with |- context[Z.eqb ?x ?y] => destruct (Z.eqb_spec x y) end;
    repeat match goal with |- context[Z.ltb ?x ?y] => destruct (Z.ltb_spec x y) end; simpl; try reflexivity; lia.
Qed.

Lemma b2i_unsigned b : Int.unsigned (b2i b) = b2z b.
Proof. destruct b; reflexivity. Qed.
Lemma b2z_range b : 0 <= b2z b <= 1.
Proof. destruct b; simpl; lia. Qed.

Section ZB.
Variables (ρ : nat -> int64) (bnd : nat -> Z * Z) (β : nat -> block * Z).
Hypothesis Hb : forall n, fst (bnd n) <= Int64.unsigned (ρ n) <= snd (bnd n).
Definition zrho (n : nat) : Z := Int64.unsigned (ρ n).

Definition zgood (x : sx) : Prop :=
  match ktop x with
  | KI => Int.unsigned (ii (den ρ β x)) = zval zrho x
  | KL => Int64.unsigned (il (den ρ β x)) = zval zrho x
  | _ => True
  end.

Lemma zgood_KI a : isk KI a = true -> zgood a -> Int.unsigned (ii (den ρ β a)) = zval zrho a.
Proof. unfold isk, zgood. intros K. apply kind_eqb_eq in K. rewrite K. auto. Qed.
Lemma zgood_KL a : isk KL a = true -> zgood a -> Int64.unsigned (il (den ρ β a)) = zval zrho a.
Proof. unfold isk, zgood. intros K. apply kind_eqb_eq in K. rewrite K. auto. Qed.

Theorem zb_sound x : forall lo hi, zb bnd x = Some (lo, hi) -> zgood x /\ lo <= zval zrho x <= hi.
Proof.
  induction x; intros lo hi H; simpl in H; try discriminate.
  - (* XIc *) inversion H; subst. split; [reflexivity|simpl; lia].
  - (* XLc *) inversion H; subst. split; [reflexivity|simpl; lia].
  - (* XLv *) inversion H as [H1]. pose proof (Hb n) as Hn. rewrite H1 in Hn. split; [reflexivity|exact Hn].
  - (* XIb *)
    destruct (isk KI x1) eqn:K1; [|discriminate]. destruct (isk KI x2) eqn:K2; [|discriminate]. simpl in H.
    destruct (zb bnd x1) as [[la ha]|]; [|discriminate]. destruct (zb bnd x2) as [[lb hb]|]; [|discriminate].
    destruct (IHx1 _ _ eq_refl) as [G1 B1]. destruct (IHx2 _ _ eq_refl) as [G2 B2].
    pose proof (zgood_KI _ K1 G1) as E1. pose proof (zgood_KI _ K2 G2) as E2.
    rewrite <- E1 in B1. rewrite <- E2 in B2.
    destruct (op32_sound o _ _ _ _ _ _ _ _ H B1 B2) as [E B]. rewrite E1, E2 in E, B.
    split; [exact E|exact B].
  - (* XLb *)
    destruct (isk KL x1) eqn:K1; [|discriminate]. destruct (isk KL x2) eqn:K2; [|discriminate]. simpl in H.
    destruct (zb bnd x1) as [[la ha]|]; [|discriminate]. destruct (zb bnd x2) as [[lb hb]|]; [|discriminate].
    destruct (IHx1 _ _ eq_refl) as [G1 B1]. destruct (IHx2 _ _ eq_refl) as [G2 B2].
    pose proof (zgood_KL _ K1 G1) as E1. pose proof (zgood_KL _ K2 G2) as E2.
    rewrite <- E1 in B1. rewrite <- E2 in B2.
    destruct (op64_sound o _ _ _ _ _ _ _ _ H B1 B2) as [E B]. rewrite E1, E2 in E, B.
    split; [exact E|exact B].
  - (* XIsh *)
    destruct (isk KI x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KI _ K1 G1) as E1. rewrite <- E1 in B1.
    destruct (sh32_sound o _ _ _ _ _ _ H B1) as [E B]. rewrite E1 in E, B.
    split; [unfold zgood; simpl; rewrite E|]; destruct o; assumption || reflexivity.
  - (* XLsh *)
    destruct (isk KL x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KL _ K1 G1) as E1. rewrite <- E1 in B1.
    destruct (sh64_sound o _ _ _ _ _ _ H B1) as [E B]. rewrite E1 in E, B.
    split; [unfold zgood; simpl; rewrite E|]; destruct o; assumption || reflexivity.
  - (* XIcmp *)
    destruct (isk KI x1) eqn:K1; [|discriminate]. destruct (isk KI x2) eqn:K2; [|discriminate]. simpl in H.
    destruct (zb bnd x1) as [[la ha]|]; [|discriminate]. destruct (zb bnd x2) as [[lb hb]|]; [|discriminate].
    destruct (IHx1 _ _ eq_refl) as [G1 B1]. destruct (IHx2 _ _ eq_refl) as [G2 B2].
    pose proof (zgood_KI _ K1 G1) as E1. pose proof (zgood_KI _ K2 G2) as E2.
    assert (EC : icmp c sg (ii (den ρ β x1)) (ii (den ρ β x2)) = zcmp c (zval zrho x1) (zval zrho x2) /\
                 lo = 0 /\ hi = 1).
    { rewrite <- E1, <- E2. destruct sg.
      - match type of H with (if ?cc then _ else _) = _ => destruct cc eqn:L; [|discriminate] end.
        apply andb_true_iff in L. destruct L as [L1 L2]. apply Z.ltb_lt in L1, L2.
        inversion H; subst. split; [|auto]. simpl. apply cmp32_zcmp.
        + eapply Z.le_lt_trans; [rewrite E1; exact (proj2 B1)|exact L1].
        + eapply Z.le_lt_trans; [rewrite E2; exact (proj2 B2)|exact L2].
      - inversion H; subst. split; [|auto]. apply cmpu32_zcmp. }
    destruct EC as (EC & H0).
    destruct H0; subst. split.
    + unfold zgood. simpl. rewrite b2i_unsigned, EC. reflexivity.
    + simpl. apply b2z_range.
  - (* XLcmp *)
    destruct (isk KL x1) eqn:K1; [|discriminate]. destruct (isk KL x2) eqn:K2; [|discriminate]. simpl in H.
    destruct (zb bnd x1) as [[la ha]|]; [|discriminate]. destruct (zb bnd x2) as [[lb hb]|]; [|discriminate].
    destruct (IHx1 _ _ eq_refl) as [G1 B1]. destruct (IHx2 _ _ eq_refl) as [G2 B2].
    pose proof (zgood_KL _ K1 G1) as E1. pose proof (zgood_KL _ K2 G2) as E2.
    assert (EC : lcmp c sg (il (den ρ β x1)) (il (den ρ β x2)) = zcmp c (zval zrho x1) (zval zrho x2) /\
                 lo = 0 /\ hi = 1).
    { rewrite <- E1, <- E2. destruct sg.
      - match type of H with (if ?cc then _ else _) = _ => destruct cc eqn:L; [|discriminate] end.
        apply andb_true_iff in L. destruct L as [L1 L2]. apply Z.ltb_lt in L1, L2.
        inversion H; subst. split; [|auto]. simpl. apply cmp64_zcmp.
        + eapply Z.le_lt_trans; [rewrite E1; exact (proj2 B1)|exact L1].
        + eapply Z.le_lt_trans; [rewrite E2; exact (proj2 B2)|exact L2].
      - inversion H; subst. split; [|auto]. apply cmpu64_zcmp. }
    destruct EC as (EC & H0).
    destruct H0; subst. split.
    + unfold zgood. simpl. rewrite b2i_unsigned, EC. reflexivity.
    + simpl. apply b2z_range.
  - (* XI2L *)
    destruct (isk KI x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KI _ K1 G1) as E1.
    pose proof (Int.unsigned_range (ii (den ρ β x))) as R. change Int.modulus with 4294967296 in R.
    destruct sg.
    + match type of H with (if ?cc then _ else _) = _ => destruct cc eqn:L; [|discriminate] end.
      apply Z.ltb_lt in L.
      change (2 ^ 31) with 2147483648 in L. inversion H; subst. split; [|exact B1].
      unfold zgood. simpl. rewrite Int.signed_eq_unsigned by (change Int.max_signed with 2147483647; lia).
      rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). exact E1.
    + inversion H; subst. split; [|exact B1].
      unfold zgood. simpl.
      rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia). exact E1.
  - (* XL2I *)
    destruct (isk KL x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KL _ K1 G1) as E1.
    pose proof (Int64.unsigned_range (il (den ρ β x))) as R.
    assert (EL : Int.unsigned (Int64.loword (il (den ρ β x))) = zval zrho x mod 2 ^ 32).
    { unfold Int64.loword. rewrite Int.unsigned_repr_eq, E1. reflexivity. }
    split; [exact EL|]. simpl. rewrite E1 in R.
    match type of H with (if ?cc then _ else _) = _ => destruct cc eqn:L end.
    + apply Z.leb_le in L. unfold M32 in L. inversion H; subst.
      change (Z.pow_pos 2 32) with 4294967296.
      rewrite Z.mod_small by (change Int64.modulus with 18446744073709551616 in R; lia). exact B1.
    + inversion H; subst. pose proof (Z.mod_pos_bound (zval zrho x) (2 ^ 32) ltac:(reflexivity)).
      unfold M32. change (Z.pow_pos 2 32) with 4294967296. change (2 ^ 32) with 4294967296 in H0. lia.
  - (* XIcast *)
    destruct sz; try discriminate; destruct sg; try discriminate; simpl in H;
      (destruct (isk KI x) eqn:K1; [|discriminate]);
      (destruct (zb bnd x) as [[la ha]|]; [|discriminate]);
      destruct (IHx _ _ eq_refl) as [G1 B1]; pose proof (zgood_KI _ K1 G1) as E1; inversion H; subst.
    + split.
      * unfold zgood. simpl. rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). rewrite E1. reflexivity.
      * simpl. pose proof (Z.mod_pos_bound (zval zrho x) 256 ltac:(reflexivity)).
        change (Z.pow_pos 2 8) with 256. lia.
    + split.
      * unfold zgood. simpl. rewrite Int.zero_ext_mod by (change Int.zwordsize with 32; lia). rewrite E1. reflexivity.
      * simpl. pose proof (Z.mod_pos_bound (zval zrho x) 65536 ltac:(reflexivity)).
        change (Z.pow_pos 2 16) with 65536. lia.
  - (* XInz *)
    destruct (isk KI x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KI _ K1 G1) as E1. inversion H; subst.
    split; [|simpl; apply b2z_range].
    unfold zgood. simpl. rewrite b2i_unsigned. f_equal. f_equal.
    unfold Int.eq. rewrite E1. change (Int.unsigned Int.zero) with 0.
    destruct (zeq (zval zrho x) 0); destruct (Z.eqb_spec (zval zrho x) 0); try reflexivity; contradiction.
  - (* XLnz *)
    destruct (isk KL x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KL _ K1 G1) as E1. inversion H; subst.
    split; [|simpl; apply b2z_range].
    unfold zgood. simpl. rewrite b2i_unsigned. f_equal. f_equal.
    unfold Int64.eq. rewrite E1. change (Int64.unsigned Int64.zero) with 0.
    destruct (zeq (zval zrho x) 0); destruct (Z.eqb_spec (zval zrho x) 0); try reflexivity; contradiction.
  - (* XIz *)
    destruct (isk KI x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KI _ K1 G1) as E1. inversion H; subst.
    split; [|simpl; apply b2z_range].
    unfold zgood. simpl. rewrite b2i_unsigned. f_equal.
    unfold Int.eq. rewrite E1. change (Int.unsigned Int.zero) with 0.
    destruct (zeq (zval zrho x) 0); destruct (Z.eqb_spec (zval zrho x) 0); try reflexivity; contradiction.
  - (* XLz *)
    destruct (isk KL x) eqn:K1; [|discriminate].
    destruct (zb bnd x) as [[la ha]|]; [|discriminate].
    destruct (IHx _ _ eq_refl) as [G1 B1]. pose proof (zgood_KL _ K1 G1) as E1. inversion H; subst.
    split; [|simpl; apply b2z_range].
    unfold zgood. simpl. rewrite b2i_unsigned. f_equal.
    unfold Int64.eq. rewrite E1. change (Int64.unsigned Int64.zero) with 0.
    destruct (zeq (zval zrho x) 0); destruct (Z.eqb_spec (zval zrho x) 0); try reflexivity; contradiction.
Qed.
End ZB.
