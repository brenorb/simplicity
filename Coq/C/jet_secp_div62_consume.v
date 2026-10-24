(** Consume the actual count/shift prefix's delayed division. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.divstep C.jet_secp_div62_numeric C.jet_secp_div62_transition
  C.jet_secp_div62_count C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma div62_shl_repr a z : 0<=z<=62 ->
  Int64.shl (Int64.repr a) (Int64.repr z)=Int64.repr(a*2^z).
Proof.
  intro Z;rewrite Int64.shl_mul_two_p,Int64.unsigned_repr by
    (change (0<=z<=18446744073709551615);lia).
  rewrite two_p_equiv;apply div62_repr_mul.
Qed.

Lemma div62_shru_repr a z : 0<=z<=62 ->
  Int64.shru (Int64.repr a) (Int64.repr z)=Int64.repr((a/2^z) mod 2^(64-z)).
Proof.
  intro Z;unfold Int64.shru;rewrite (Int64.unsigned_repr z) by
    (change (0<=z<=18446744073709551615);lia).
  rewrite Int64.unsigned_repr_eq,Z.shiftr_div_pow2 by lia.
  change Int64.modulus with (2^64).
  replace (2^64) with (2^z*2^(64-z)) by (rewrite <- Z.pow_add_r by lia;f_equal;lia).
  rewrite Zaux.Zdiv_mod_mult by (apply Z.pow_nonneg;lia);reflexivity.
Qed.

Lemma div62_shift_pending b pending z : 0<=pending<=z -> z<=62 ->
  Int64.shru (Int64.repr(b*2^pending)) (Int64.repr z)=
    Int64.repr((b/2^(z-pending)) mod 2^(64-z)).
Proof.
  intros P Z;rewrite div62_shru_repr by lia.
  replace (2^z) with (2^pending*2^(z-pending)) by
    (rewrite <- Z.pow_add_r by lia;f_equal;lia).
  rewrite (Z.mul_comm (2^pending) (2^(z-pending))),Zdiv_mult_cancel_r by
    (apply Z.pow_nonzero;lia);reflexivity.
Qed.

Lemma div62_halving_divides st b precision h : 0<=h<=precision ->
  eqm (2^precision) b (g st) -> (2^h|b) -> (2^h|g st).
Proof.
  intros H EQ Div;pose proof (eqm_2_pow_le h precision b (g st) H EQ) as Small.
  unfold eqm in Small;apply Zmod_divide;[apply Z.pow_nonzero;lia|].
  rewrite <- Small;apply Zdivide_mod;exact Div.
Qed.

Lemma div62_shift_approximation st a b precision pending z :
  0<=pending<=z -> z<=62 -> z-pending<=precision -> precision+pending<=64 ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) -> (2^(z-pending)|b) ->
  eqm (2^(precision-(z-pending))) a (f(fst(stepN (Z.to_nat(z-pending)) st))) /\
  eqm (2^(precision-(z-pending))) ((b/2^(z-pending)) mod 2^(64-z))
    (g(fst(stepN (Z.to_nat(z-pending)) st))).
Proof.
  intros P Z Precision Fits A B Div.
  assert (GD : (2^(z-pending)|g st)) by (apply (div62_halving_divides st b precision);assumption || lia).
  assert (GDN : (2^Z.of_nat(Z.to_nat(z-pending))|g st)) by (rewrite Z2Nat.id by lia;exact GD).
  rewrite fHs,gHs by exact GDN;rewrite Z2Nat.id by lia.
  split.
  - apply (eqm_2_pow_le _ precision);[lia|exact A].
  - unfold eqm.
    assert (Truncate : eqm (2^(precision-(z-pending)))
      ((b/2^(z-pending)) mod 2^(64-z)) (b/2^(z-pending))).
    { apply (eqm_2_pow_le _ (64-z));[lia|].
      unfold eqm;rewrite Z.mod_mod by (apply Z.pow_nonzero;lia);reflexivity. }
    unfold eqm in Truncate;rewrite Truncate.
    apply div62_divide_congruent;[lia|].
    rewrite <- (Z_div_exact_full_2 (g st) (2^(z-pending))
      ltac:(apply Z.pow_nonzero;lia) ltac:(apply Zdivide_mod;exact GD));exact B.
Qed.

Definition div62_sentinel_word g i := Int64.or g (Int64.shl Int64.mone (Int64.repr i)).
Definition div62_sentinel_count g i := Z_ctz (Int64.unsigned (div62_sentinel_word g i)).

Lemma div62_sentinel_bits g i bit : 0<=i<=62 -> 0<=bit<64 ->
  Int64.testbit (div62_sentinel_word g i) bit=
    (if zlt bit i then Int64.testbit g bit else true).
Proof.
  intros I Bit;unfold div62_sentinel_word;rewrite Int64.bits_or,Int64.bits_shl by
    (change Int64.zwordsize with 64;lia).
  rewrite Int64.unsigned_repr by (change (0<=i<=18446744073709551615);lia).
  destruct (zlt bit i);[apply Bool.orb_false_r|].
  rewrite Int64.bits_mone by (change Int64.zwordsize with 64;lia).
  apply Bool.orb_true_r.
Qed.

Lemma div62_sentinel_nonzero g i : 0<=i<=62 -> Int64.unsigned(div62_sentinel_word g i)<>0.
Proof.
  intros I Zero;pose proof (div62_sentinel_bits g i i I ltac:(lia)) as Bit.
  unfold Int64.testbit in Bit;rewrite Zero,Z.bits_0 in Bit.
  destruct (zlt i i);[lia|discriminate].
Qed.

Lemma div62_sentinel_count_bound g i : 0<=i<=62 -> 0<=div62_sentinel_count g i<=i.
Proof.
  intro I;split;[apply Z_ctz_non_neg|].
  destruct (Z_le_gt_dec (div62_sentinel_count g i) i) as [LE|GT];[assumption|].
  pose proof (Z_ctz_testbit_false (Int64.unsigned(div62_sentinel_word g i)) i
    ltac:(change (i<div62_sentinel_count g i);lia)) as FalseBit.
  change (Int64.testbit (div62_sentinel_word g i) i=false) in FalseBit.
  rewrite div62_sentinel_bits in FalseBit by lia;destruct (zlt i i);[lia|discriminate].
Qed.

Lemma div62_sentinel_low_bits g i bit : 0<=i<=62 -> 0<=bit<div62_sentinel_count g i ->
  Int64.testbit g bit=false.
Proof.
  intros I Bit;pose proof (div62_sentinel_count_bound g i I) as Bound.
  pose proof (Z_ctz_testbit_false (Int64.unsigned(div62_sentinel_word g i)) bit
    ltac:(change (bit<div62_sentinel_count g i);lia)) as FalseBit.
  change (Int64.testbit (div62_sentinel_word g i) bit=false) in FalseBit.
  rewrite div62_sentinel_bits in FalseBit by lia;destruct (zlt bit i);[exact FalseBit|lia].
Qed.

Lemma div62_sentinel_divides g i : 0<=i<=62 ->
  (2^div62_sentinel_count g i | Int64.unsigned g).
Proof.
  intro I;pose proof (div62_sentinel_count_bound g i I) as Bound.
  apply Zmod_divide;[apply Z.pow_nonzero;lia|].
  apply Z.bits_inj_0;intro bit;destruct (Z_le_gt_dec 0 bit) as [Positive|Negative].
  - destruct (Z_lt_ge_dec bit (div62_sentinel_count g i)) as [Low|High].
    + rewrite Z.mod_pow2_bits_low by lia;apply (div62_sentinel_low_bits g i bit);assumption || lia.
    + apply Z.mod_pow2_bits_high;lia.
  - apply Z.testbit_neg_r;lia.
Qed.

Lemma div62_sentinel_first_bit g i : 0<=i<=62 -> div62_sentinel_count g i<i ->
  Int64.testbit g (div62_sentinel_count g i)=true.
Proof.
  intros I Nonexit;pose proof (div62_sentinel_count_bound g i I) as Bound.
  pose proof (Z_ctz_testbit_true (Int64.unsigned(div62_sentinel_word g i))
    (div62_sentinel_nonzero g i I)) as TrueBit.
  change (Int64.testbit (div62_sentinel_word g i) (div62_sentinel_count g i)=true) in TrueBit.
  rewrite div62_sentinel_bits in TrueBit by lia.
  destruct (zlt (div62_sentinel_count g i) i);[exact TrueBit|lia].
Qed.

Lemma div62_sentinel_consumes_pending b pending i : 0<=pending<=i -> i<=62 ->
  pending<=div62_sentinel_count (Int64.repr(b*2^pending)) i.
Proof.
  intros P I;pose proof (div62_sentinel_count_bound (Int64.repr(b*2^pending)) i ltac:(lia)) as Bound.
  destruct (Z_le_gt_dec pending (div62_sentinel_count (Int64.repr(b*2^pending)) i));[assumption|].
  pose proof (div62_sentinel_first_bit (Int64.repr(b*2^pending)) i ltac:(lia) ltac:(lia)) as Bit.
  rewrite Int64.testbit_repr in Bit by (change Int64.zwordsize with 64;lia).
  rewrite Z.mul_pow2_bits_low in Bit by lia;discriminate.
Qed.

Lemma div62_sentinel_unwrapped b pending i : 0<=pending<=i -> i<=62 ->
  (2^(div62_sentinel_count (Int64.repr(b*2^pending)) i-pending)|b).
Proof.
  intros P I;set (z:=div62_sentinel_count (Int64.repr(b*2^pending)) i).
  pose proof (div62_sentinel_count_bound (Int64.repr(b*2^pending)) i ltac:(lia)) as Bound.
  pose proof (div62_sentinel_consumes_pending b pending i P I) as Consumes.
  fold z in Bound,Consumes.
  assert (Div : (2^z|b*2^pending)).
  { apply Zmod_divide;[apply Z.pow_nonzero;lia|].
    rewrite <- div62_repr64_lowbits by lia.
    apply Zdivide_mod;apply div62_sentinel_divides;lia. }
  apply (proj1 (Z.mul_divide_cancel_r (2^(z-pending)) b (2^pending) ltac:(apply Z.pow_nonzero;lia))).
  replace (2^(z-pending)*2^pending) with (2^z) by (rewrite <- Z.pow_add_r by lia;f_equal;lia).
  exact Div.
Qed.

Lemma div62_sentinel_odd_quotient b pending i : 0<=pending<=i -> i<=62 ->
  let z:=div62_sentinel_count (Int64.repr(b*2^pending)) i in z<i ->
  Zodd ((b/2^(z-pending)) mod 2^(64-z)).
Proof.
  intros P I z Nonexit.
  pose proof (div62_sentinel_count_bound (Int64.repr(b*2^pending)) i ltac:(lia)) as Bound.
  pose proof (div62_sentinel_consumes_pending b pending i P I) as Consumes.
  fold z in Bound,Consumes.
  pose proof (div62_sentinel_first_bit (Int64.repr(b*2^pending)) i ltac:(lia) Nonexit) as Bit.
  rewrite Int64.testbit_repr in Bit by (change Int64.zwordsize with 64;lia).
  rewrite Z.mul_pow2_bits in Bit by lia;fold z in Bit.
  apply Zodd_bool_iff;rewrite <- Z.bit0_odd,Z.mod_pow2_bits_low,Z.div_pow2_bits by lia.
  replace (0+(z-pending)) with (z-pending) by lia;exact Bit.
Qed.

Definition div62_sentinel_expr := Ebinop Oor (Etempvar _g tulong)
  (Ebinop Oshl (Econst_long Int64.mone tulong) (Etempvar _i tint) tulong) tulong.
Lemma div62_sentinel_source : div62_loop_body=
  Ssequence Sskip (Ssequence
    (Ssequence (Scall (Some _t'1)
      (Evar _secp256k1_ctz64_var (Tfunction (Tcons tulong Tnil) tint cc_default)) [div62_sentinel_expr])
      div62_copy_count) div62_after_count).
Proof. reflexivity. Qed.

Lemma eval_div62_sentinel e le m g i : 0<=i<=62 ->
  le!_g=Some(Vlong g) -> le!_i=Some(Vint(Int.repr i)) ->
  eval_expr secp_ge e le m div62_sentinel_expr (Vlong(div62_sentinel_word g i)).
Proof.
  intros I G Index;unfold div62_sentinel_expr,div62_sentinel_word.
  eapply eval_Ebinop with (v2:=Vlong(Int64.shl Int64.mone (Int64.repr i))).
  - apply eval_Etempvar;exact G.
  - eapply eval_Ebinop;[apply eval_Econst_long|apply eval_Etempvar;exact Index|].
    change ((if Int.ltu (Int.repr i) Int64.iwordsize' then
      Some (Vlong (Int64.shl Int64.mone (Int64.repr (Int.unsigned (Int.repr i))))) else None)=
      Some(Vlong(Int64.shl Int64.mone (Int64.repr i)))).
    rewrite div62_count_shift_guard by exact I.
    rewrite Int.unsigned_repr by (change (0<=i<=4294967295);lia);reflexivity.
  - reflexivity.
Qed.

Definition div62_expected_count (le : temp_env) i :=
  match le!_g with Some(Vlong g)=>div62_sentinel_count g i | _=>0 end.

Theorem exec_div62_consume e le m st matrix precision pending i :
  0<=pending<=i -> i<=62 -> i-pending<=precision -> precision+pending<=64 ->
  div62_pending_matrix le matrix pending -> div62_pending_fg le st precision pending ->
  le!_eta=Some(Vlong(Int64.repr(eta st+pending))) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_zeros=Some(Vint(Int.repr(div62_expected_count le i))) ->
  let z:=div62_expected_count le i in let h:=z-pending in
  exists lef,
    Clight2.exec_stmt secp_ge e le m div62_count_prefix E0 lef m (div62_count_outcome i z) /\
    div62_pending_matrix lef (Trans.mul (Trans.transN (Z.to_nat h) st) matrix) 0 /\
    div62_pending_fg lef (fst(stepN (Z.to_nat h) st)) (precision-h) 0 /\
    lef!_eta=Some(Vlong(Int64.repr(eta (fst(stepN (Z.to_nat h) st))))) /\
    lef!_i=Some(Vint(Int.repr(i-z))) /\ (z=i \/ Zodd(g(fst(stepN (Z.to_nat h) st)))).
Proof.
  intros Pending I Precision Fits (u & v & MU & MV & U & V & Q & R)
    (a & b & A & B & F & G) Eta Index Zeros.
  assert (Count : div62_expected_count le i=div62_sentinel_count (Int64.repr(b*2^pending)) i)
    by (unfold div62_expected_count;rewrite G;reflexivity).
  rewrite Count in Zeros |- *;cbn zeta.
  set (z:=div62_sentinel_count (Int64.repr(b*2^pending)) i).
  pose proof (div62_sentinel_count_bound (Int64.repr(b*2^pending)) i ltac:(lia)) as Z.
  pose proof (div62_sentinel_consumes_pending b pending i Pending I) as Consumes.
  pose proof (div62_sentinel_unwrapped b pending i Pending I) as Div.
  fold z in Z,Consumes,Div.
  assert (GD : (2^Z.of_nat(Z.to_nat(z-pending))|g st)).
  { rewrite Z2Nat.id by lia;apply (div62_halving_divides st b precision);assumption || lia. }
  assert (Power : 2^z=2^pending*2^(z-pending)) by
    (rewrite <- Z.pow_add_r by lia;f_equal;lia).
  assert (US : Int64.shl (Int64.repr u) (Int64.repr z)=Int64.repr(2^(z-pending)*Trans.u matrix)).
  { rewrite div62_shl_repr,MU,Power by lia;f_equal;ring. }
  assert (VS : Int64.shl (Int64.repr v) (Int64.repr z)=Int64.repr(2^(z-pending)*Trans.v matrix)).
  { rewrite div62_shl_repr,MV,Power by lia;f_equal;ring. }
  set (lef:=div62_count_temps le (Int64.repr(b*2^pending)) (Int64.repr u) (Int64.repr v)
    (eta st+pending) i z).
  exists lef;split.
  - unfold lef;apply exec_div62_count_prefix;assumption || lia.
  - split.
    + rewrite Trans.transHs by exact GD;rewrite Z2Nat.id by lia.
      unfold div62_pending_matrix;exists (2^(z-pending)*Trans.u matrix),(2^(z-pending)*Trans.v matrix).
      repeat apply conj;cbn [Trans.mul Trans.u Trans.v Trans.q Trans.r];try ring.
      * unfold lef,div62_count_temps;repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;now rewrite US.
      * unfold lef,div62_count_temps;repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;now rewrite VS.
      * unfold lef,div62_count_temps;rewrite !PTree.gso by discriminate.
        replace (0*Trans.u matrix+1*Trans.q matrix) with (Trans.q matrix) by ring;exact Q.
      * unfold lef,div62_count_temps;rewrite !PTree.gso by discriminate.
        replace (0*Trans.v matrix+1*Trans.r matrix) with (Trans.r matrix) by ring;exact R.
    + pose proof (div62_shift_approximation st a b precision pending z ltac:(lia) ltac:(lia)
        ltac:(lia) Fits A B Div) as (AN & BN).
      split.
      * unfold div62_pending_fg;exists a,((b/2^(z-pending)) mod 2^(64-z)).
        split;[exact AN|];split;[exact BN|];split.
        -- unfold lef,div62_count_temps;rewrite !PTree.gso by discriminate;exact F.
        -- unfold lef,div62_count_temps;repeat rewrite PTree.gso by discriminate;rewrite PTree.gss.
           rewrite div62_shift_pending by lia;rewrite Z.pow_0_r,Z.mul_1_r;reflexivity.
      * split.
        -- unfold lef,div62_count_temps;rewrite PTree.gso by discriminate;rewrite PTree.gss.
           rewrite etaHs by exact GD;rewrite Z2Nat.id by lia;f_equal;f_equal;f_equal;ring.
        -- split;[unfold lef,div62_count_temps;apply PTree.gss|].
           destruct (Z.eq_dec z i) as [->|NE];[now left|right].
           assert (Odd : Zodd ((b/2^(z-pending)) mod 2^(64-z))) by
             (apply (div62_sentinel_odd_quotient b pending i Pending I);lia).
           apply Zodd_equiv;apply (div62_odd_congruent
             (g(fst(stepN (Z.to_nat(z-pending)) st))) ((b/2^(z-pending)) mod 2^(64-z))
             (precision-(z-pending)));[lia| |exact Odd].
           unfold eqm in *;symmetry;exact BN.
Qed.
