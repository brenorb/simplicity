(** Relate the actual cancellation coefficient to a batch of canonical
    divsteps, allowing the low-bit approximation used by the C loop. *)
From Coq Require Import ZArith Lia.
From compcert Require Import Coqlib Integers Clight ClightBigstep Maps Memory Values Events.
Require Import C.extraMath C.modinv C.divstep C.jet_secp_div62_cancel C.jet_secp_div62_limit C.jet_secp_div62_numeric.
Require Import C.jet_secp_div62_count C.jet_secp_div62_branch C.jet_secp_linkage C.jets_secp.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma div62_odd_congruent a b precision : 1<=precision -> eqm (2^precision) a b -> Zodd b -> Z.Odd a.
Proof.
  intros P EQ Odd;pose proof (eqm_2_pow_le 1 precision a b ltac:(lia) EQ) as Small.
  change (a mod 2=b mod 2) in Small.
  assert (OB : Z.odd b=true) by (apply Zodd_bool_iff;exact Odd).
  rewrite !Zmod_odd,OB in Small;destruct (Z.odd a) eqn:OA;[apply Z.odd_spec;exact OA|discriminate].
Qed.

Lemma div62_coefficient_congruent a b F G k precision :
  0<=k<=precision -> eqm (2^precision) a F -> eqm (2^precision) b G ->
  (modInv (-a) (2^k)*b) mod 2^k=(modInv (-F) (2^k)*G) mod 2^k.
Proof.
  intros K A B;change (eqm (2^k) (modInv (-a) (2^k)*b) (modInv (-F) (2^k)*G)).
  apply Zmult_eqm.
  - pose proof (eqm_2_pow_le k precision a F K A) as Small.
    rewrite (modInv_eqm _ _ _ (Zopp_eqm _ _ _ Small));reflexivity.
  - apply (eqm_2_pow_le k precision b G K B).
Qed.

Theorem div62_positive_transition st i a b precision :
  0<=eta st<=745 -> 1<=i<=62 ->
  div62_cancel_bits false (eta st) i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  let k:=div62_cancel_bits false (eta st) i in
  let w:=Int.unsigned(div62_w_word false (Int64.repr a) (Int64.repr b) (div62_mask false (eta st) i)) in
  Trans.transN (Z.to_nat k) st={|Trans.u:=2^k;Trans.v:=0;Trans.q:=w;Trans.r:=1|} /\
  eta (fst(stepN (Z.to_nat k) st))=eta st-k.
Proof.
  intros Eta I P A B;cbn zeta.
  pose proof (div62_cancel_bits_bound false (eta st) i Eta I) as K.
  assert (Odd : Z.Odd a) by (apply (div62_odd_congruent a (f st) precision);[lia|exact A|apply oddF]).
  assert (W : Int.unsigned(div62_w_word false (Int64.repr a) (Int64.repr b) (div62_mask false (eta st) i))=
    (modInv (-(f st)) (2^div62_cancel_bits false (eta st) i)*g st) mod 2^div62_cancel_bits false (eta st) i).
  { rewrite div62_w_unsigned by assumption;apply (div62_coefficient_congruent _ _ _ _ _ precision);assumption || lia. }
  assert (Limit : div62_cancel_bits false (eta st) i<=1+eta st) by
    (unfold div62_cancel_bits,div62_limit;lia).
  split.
  - rewrite Trans.transSs by (unfold eta in *;try rewrite Z2Nat.id by lia;lia).
    rewrite Z2Nat.id by lia;rewrite W;reflexivity.
  - rewrite etaSs by (try rewrite Z2Nat.id by lia;lia).
    rewrite Z2Nat.id by lia;reflexivity.
Qed.

Theorem div62_negative_transition st i a b precision :
  -745<=eta st<0 -> 1<=i<=62 -> Zodd(g st) ->
  div62_cancel_bits true (-eta st) i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  let k:=div62_cancel_bits true (-eta st) i in
  let w:=Int.unsigned(div62_w_word true (Int64.repr b) (Int64.repr (-a)) (div62_mask true (-eta st) i)) in
  Trans.transN (Z.to_nat k) st={|Trans.u:=0;Trans.v:=2^k;Trans.q:= -1;Trans.r:=w|} /\
  eta (fst(stepN (Z.to_nat k) st))= -eta st-k.
Proof.
  intros Eta I OddG P A B;cbn zeta.
  pose proof (div62_cancel_bits_bound true (-eta st) i ltac:(lia) I) as K.
  assert (Odd : Z.Odd b) by (apply (div62_odd_congruent b (g st) precision);[lia|exact B|exact OddG]).
  assert (W : Int.unsigned(div62_w_word true (Int64.repr b) (Int64.repr (-a)) (div62_mask true (-eta st) i))=
    (modInv (-(g st)) (2^div62_cancel_bits true (-eta st) i)*(-f st)) mod 2^div62_cancel_bits true (-eta st) i).
  { rewrite div62_w_unsigned by (assumption || lia).
    apply (div62_coefficient_congruent _ _ _ _ _ precision);[lia|exact B|now apply Zopp_eqm]. }
  assert (Limit : div62_cancel_bits true (-eta st) i<=1-eta st) by
    (unfold div62_cancel_bits,div62_limit;lia).
  split.
  - rewrite Trans.transDs by (assumption || (unfold eta in *;try rewrite Z2Nat.id by lia;lia)).
    rewrite Z2Nat.id by lia;rewrite W;reflexivity.
  - rewrite etaDs by (assumption || (try rewrite Z2Nat.id by lia;lia)).
    rewrite Z2Nat.id by lia;reflexivity.
Qed.

Lemma div62_fg_transition st k w (neg : bool) : 0<=k ->
  Trans.transN (Z.to_nat k) st=
    (if neg then {|Trans.u:=0;Trans.v:=2^k;Trans.q:= -1;Trans.r:=w|}
     else {|Trans.u:=2^k;Trans.v:=0;Trans.q:=w;Trans.r:=1|}) ->
  f (fst(stepN (Z.to_nat k) st))=(if neg then g st else f st) /\
  2^k*g (fst(stepN (Z.to_nat k) st))=
    (if neg then -f st else g st)+(if neg then g st else f st)*w.
Proof.
  intros K Matrix;pose proof (Trans.transN_step (Z.to_nat k) st) as FG.
  rewrite Matrix,Z2Nat.id in FG by exact K.
  pose proof (f_equal Trans.x FG) as F;pose proof (f_equal Trans.y FG) as G.
  destruct neg;cbn [Trans.scale Trans.ap Trans.fg Trans.x Trans.y Trans.u Trans.v Trans.q Trans.r] in F,G |- *;
    split;[apply (Z.mul_reg_l _ _ (2^k));[apply Z.pow_nonzero;lia|nia]|nia|
           apply (Z.mul_reg_l _ _ (2^k));[apply Z.pow_nonzero;lia|nia]|nia].
Qed.

Lemma div62_divide_congruent a b precision k : 0<=k<=precision ->
  eqm (2^precision) a (2^k*b) -> eqm (2^(precision-k)) (a/2^k) b.
Proof.
  intros Range EQ;unfold eqm in *.
  replace (2^precision) with (2^k*2^(precision-k)) in EQ by
    (rewrite <- Z.pow_add_r by lia;f_equal;lia).
  rewrite <- Zaux.Zdiv_mod_mult by (apply Z.pow_nonneg;lia).
  rewrite EQ,Zmult_mod_distr_l.
  rewrite (Z.mul_comm (2^k) (b mod 2^(precision-k))),Z.div_mul by (apply Z.pow_nonzero;lia).
  reflexivity.
Qed.

Theorem div62_positive_approximation st i a b precision :
  0<=eta st<=745 -> 1<=i<=62 ->
  div62_cancel_bits false (eta st) i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  let k:=div62_cancel_bits false (eta st) i in
  let w:=Int.unsigned(div62_w_word false (Int64.repr a) (Int64.repr b) (div62_mask false (eta st) i)) in
  eqm (2^(precision-k)) a (f (fst(stepN (Z.to_nat k) st))) /\
  eqm (2^(precision-k)) ((b+a*w)/2^k) (g (fst(stepN (Z.to_nat k) st))) /\
  b+a*w=2^k*((b+a*w)/2^k).
Proof.
  intros Eta I P A B;cbn zeta.
  pose proof (div62_cancel_bits_bound false (eta st) i Eta I) as K.
  destruct (div62_positive_transition st i a b precision Eta I P A B) as [Matrix EtaNext].
  destruct (div62_fg_transition st (div62_cancel_bits false (eta st) i) _ false ltac:(lia) Matrix) as [F G].
  split.
  - rewrite F;apply (eqm_2_pow_le _ precision);[lia|exact A].
  - split.
    + apply div62_divide_congruent;[lia|].
      rewrite G.
      apply Zplus_eqm;[exact B|apply Zmult_eqm;[exact A|reflexivity]].
    + apply Z_div_exact_full_2;[apply Z.pow_nonzero;lia|].
      apply Zdivide_mod.
      pose proof (div62_cancellation false (eta st) i a b Eta I
        (div62_odd_congruent a (f st) precision ltac:(lia) A (oddF st))) as Cancel.
      exact (proj1 (proj2 Cancel)).
Qed.

Definition div62_continuation_w (neg : bool) eta i a b :=
  Int.unsigned (div62_w_word neg (if neg then Int64.repr b else Int64.repr a)
    (if neg then Int64.neg (Int64.repr a) else Int64.repr b)
    (div62_mask neg (if neg then -eta else eta) i)).
Definition div62_continuation_matrix (neg : bool) eta i a b :=
  let k:=div62_cancel_bits neg (if neg then -eta else eta) i in
  let w:=div62_continuation_w neg eta i a b in
  if neg then {|Trans.u:=0;Trans.v:=2^k;Trans.q:= -1;Trans.r:=w|}
  else {|Trans.u:=2^k;Trans.v:=0;Trans.q:=w;Trans.r:=1|}.

Definition div62_pending_matrix (le : temp_env) (matrix : Trans.M2x2) pending :=
  exists u v, Trans.u matrix=u*2^pending /\ Trans.v matrix=v*2^pending /\
    le!_u=Some(Vlong(Int64.repr u)) /\ le!_v=Some(Vlong(Int64.repr v)) /\
    le!_q=Some(Vlong(Int64.repr(Trans.q matrix))) /\
    le!_r=Some(Vlong(Int64.repr(Trans.r matrix))).

Lemma div62_continued_matrix le neg eta i a b matrix :
  le!_u=Some(Vlong(Int64.repr(Trans.u matrix))) -> le!_v=Some(Vlong(Int64.repr(Trans.v matrix))) ->
  le!_q=Some(Vlong(Int64.repr(Trans.q matrix))) -> le!_r=Some(Vlong(Int64.repr(Trans.r matrix))) ->
  div62_pending_matrix
    (div62_continued_temps le neg eta i (Int64.repr a) (Int64.repr b)
      (Int64.repr(Trans.u matrix)) (Int64.repr(Trans.v matrix))
      (Int64.repr(Trans.q matrix)) (Int64.repr(Trans.r matrix)))
    (Trans.mul (div62_continuation_matrix neg eta i a b) matrix)
    (div62_cancel_bits neg (if neg then -eta else eta) i).
Proof.
  intros U V Q R;unfold div62_pending_matrix,div62_continuation_matrix;destruct neg.
  - exists (Trans.q matrix),(Trans.r matrix).
    repeat apply conj;cbn [Trans.mul Trans.u Trans.v Trans.q Trans.r];try ring.
    all: unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
      div62_branch_entry,div62_swap_temps,div62_limit_temp;
      repeat rewrite PTree.gso by discriminate;rewrite PTree.gss;
      try reflexivity;
      unfold div62_w_long,div62_continuation_w;
      rewrite Int64.neg_repr,!div62_repr_mul,!div62_repr_add;
      f_equal;f_equal;f_equal;ring.
  - exists (Trans.u matrix),(Trans.v matrix).
    repeat apply conj;cbn [Trans.mul Trans.u Trans.v Trans.q Trans.r];try ring.
    all: unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
      div62_branch_entry,div62_swap_temps,div62_limit_temp;
      repeat rewrite PTree.gso by discriminate;
      first [assumption|rewrite PTree.gss;unfold div62_w_long,div62_continuation_w;
        rewrite !div62_repr_mul,!div62_repr_add;f_equal;f_equal;f_equal;ring].
Qed.

Theorem div62_negative_approximation st i a b precision :
  -745<=eta st<0 -> 1<=i<=62 -> Zodd(g st) ->
  div62_cancel_bits true (-eta st) i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  let k:=div62_cancel_bits true (-eta st) i in
  let w:=Int.unsigned(div62_w_word true (Int64.repr b) (Int64.repr (-a)) (div62_mask true (-eta st) i)) in
  eqm (2^(precision-k)) b (f (fst(stepN (Z.to_nat k) st))) /\
  eqm (2^(precision-k)) ((-a+b*w)/2^k) (g (fst(stepN (Z.to_nat k) st))) /\
  -a+b*w=2^k*((-a+b*w)/2^k).
Proof.
  intros Eta I OddG P A B;cbn zeta.
  pose proof (div62_cancel_bits_bound true (-eta st) i ltac:(lia) I) as K.
  destruct (div62_negative_transition st i a b precision Eta I OddG P A B) as [Matrix EtaNext].
  destruct (div62_fg_transition st (div62_cancel_bits true (-eta st) i) _ true ltac:(lia) Matrix) as [F G].
  split.
  - rewrite F;apply (eqm_2_pow_le _ precision);[lia|exact B].
  - split.
    + apply div62_divide_congruent;[lia|].
      rewrite G;apply Zplus_eqm;[now apply Zopp_eqm|apply Zmult_eqm;[exact B|reflexivity]].
    + apply Z_div_exact_full_2;[apply Z.pow_nonzero;lia|].
      apply Zdivide_mod.
      pose proof (div62_cancellation true (-eta st) i b (-a) ltac:(lia) I
        (div62_odd_congruent b (g st) precision ltac:(lia) B OddG)) as Cancel.
      exact (proj1 (proj2 Cancel)).
Qed.

Definition div62_sign eta := if zlt eta 0 then true else false.
Definition div62_branch_width st i :=
  div62_cancel_bits (div62_sign (eta st)) (if div62_sign (eta st) then -eta st else eta st) i.

Theorem div62_branch_transition st i a b precision :
  -745<=eta st<=745 -> 1<=i<=62 -> Zodd(g st) -> div62_branch_width st i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  Trans.transN (Z.to_nat(div62_branch_width st i)) st=
    div62_continuation_matrix (div62_sign (eta st)) (eta st) i a b /\
  eta (fst(stepN (Z.to_nat(div62_branch_width st i)) st))+div62_branch_width st i=
    (if div62_sign (eta st) then -eta st else eta st).
Proof.
  intros Bound I OddG P A B;unfold div62_branch_width,div62_sign in *;destruct (zlt (eta st) 0) as [LT|GE].
  - destruct (div62_negative_transition st i a b precision ltac:(lia) I OddG P A B) as [Matrix EtaNext].
    split;[unfold div62_continuation_matrix,div62_continuation_w;rewrite Int64.neg_repr;exact Matrix|lia].
  - destruct (div62_positive_transition st i a b precision ltac:(lia) I P A B) as [Matrix EtaNext].
    split;[exact Matrix|lia].
Qed.

Definition div62_pending_fg (le : temp_env) st precision pending :=
  exists a b, eqm (2^precision) a (f st) /\ eqm (2^precision) b (g st) /\
    le!_f=Some(Vlong(Int64.repr a)) /\ le!_g=Some(Vlong(Int64.repr(b*2^pending))).

Lemma div62_continued_fg le st i a b precision matrix :
  -745<=eta st<=745 -> 1<=i<=62 -> Zodd(g st) -> div62_branch_width st i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  le!_f=Some(Vlong(Int64.repr a)) -> le!_g=Some(Vlong(Int64.repr b)) ->
  div62_pending_fg
    (div62_continued_temps le (div62_sign (eta st)) (eta st) i (Int64.repr a) (Int64.repr b)
      (Int64.repr(Trans.u matrix)) (Int64.repr(Trans.v matrix))
      (Int64.repr(Trans.q matrix)) (Int64.repr(Trans.r matrix)))
    (fst(stepN (Z.to_nat(div62_branch_width st i)) st))
    (precision-div62_branch_width st i) (div62_branch_width st i).
Proof.
  intros Bound I OddG P A B F G.
  unfold div62_branch_width,div62_sign in *;destruct (zlt (eta st) 0) as [LT|GE].
  - destruct (div62_negative_approximation st i a b precision ltac:(lia) I OddG P A B) as (AN & BN & Exact).
    unfold div62_pending_fg;exists b,((-a+b*Int.unsigned(div62_w_word true
      (Int64.repr b) (Int64.repr(-a)) (div62_mask true (-eta st) i)))/2^div62_cancel_bits true (-eta st) i).
    split;[exact AN|];split;[exact BN|];split.
    + unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
        div62_branch_entry,div62_swap_temps,div62_limit_temp;
        repeat rewrite PTree.gso by discriminate;apply PTree.gss.
    + unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
        div62_branch_entry,div62_swap_temps,div62_limit_temp;
        repeat rewrite PTree.gso by discriminate;rewrite PTree.gss.
      unfold div62_w_long;rewrite Int64.neg_repr,div62_repr_mul,div62_repr_add.
      f_equal;f_equal;f_equal;rewrite Exact at 1;ring.
  - destruct (div62_positive_approximation st i a b precision ltac:(lia) I P A B) as (AN & BN & Exact).
    unfold div62_pending_fg;exists a,((b+a*Int.unsigned(div62_w_word false
      (Int64.repr a) (Int64.repr b) (div62_mask false (eta st) i)))/2^div62_cancel_bits false (eta st) i).
    split;[exact AN|];split;[exact BN|];split.
    + unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
        div62_branch_entry,div62_swap_temps,div62_limit_temp;
        repeat rewrite PTree.gso by discriminate;exact F.
    + unfold div62_continued_temps,div62_cancel_temps,div62_limit_temps,
        div62_branch_entry,div62_swap_temps,div62_limit_temp;
        repeat rewrite PTree.gso by discriminate;rewrite PTree.gss.
      unfold div62_w_long;rewrite div62_repr_mul,div62_repr_add.
      f_equal;f_equal;f_equal;rewrite Exact at 1;ring.
Qed.

Theorem exec_div62_transition_matrix e le m st i a b precision matrix :
  -745<=eta st<=745 -> 1<=i<=62 -> Zodd(g st) -> div62_branch_width st i<=precision ->
  eqm (2^precision) a (f st) -> eqm (2^precision) b (g st) ->
  le!_eta=Some(Vlong(Int64.repr(eta st))) -> le!_i=Some(Vint(Int.repr i)) ->
  le!_f=Some(Vlong(Int64.repr a)) -> le!_g=Some(Vlong(Int64.repr b)) ->
  le!_u=Some(Vlong(Int64.repr(Trans.u matrix))) -> le!_v=Some(Vlong(Int64.repr(Trans.v matrix))) ->
  le!_q=Some(Vlong(Int64.repr(Trans.q matrix))) -> le!_r=Some(Vlong(Int64.repr(Trans.r matrix))) ->
  exists lef,
    Clight2.exec_stmt secp_ge e le m div62_after_count_prefix E0 lef m Out_normal /\
    div62_pending_matrix lef
      (Trans.mul (Trans.transN (Z.to_nat(div62_branch_width st i)) st) matrix) (div62_branch_width st i) /\
    div62_pending_fg lef (fst(stepN (Z.to_nat(div62_branch_width st i)) st))
      (precision-div62_branch_width st i) (div62_branch_width st i) /\
    lef!_eta=Some(Vlong(Int64.repr(eta (fst(stepN (Z.to_nat(div62_branch_width st i)) st))+
      div62_branch_width st i))) /\ lef!_i=Some(Vint(Int.repr i)).
Proof.
  intros Bound I OddG P A B Eta Index F G U V Q R.
  destruct (div62_branch_transition st i a b precision Bound I OddG P A B) as [Matrix EtaNext].
  set (lef:=div62_continued_temps le (div62_sign (eta st)) (eta st) i (Int64.repr a) (Int64.repr b)
    (Int64.repr(Trans.u matrix)) (Int64.repr(Trans.v matrix))
    (Int64.repr(Trans.q matrix)) (Int64.repr(Trans.r matrix))).
  exists lef;split.
  - unfold lef,div62_sign;now apply exec_div62_nonexit.
  - split.
    + rewrite Matrix;unfold lef,div62_branch_width;now apply div62_continued_matrix.
    + split.
      * unfold lef;now apply div62_continued_fg.
      * split.
        -- rewrite EtaNext;unfold lef,div62_continued_temps,div62_cancel_temps,div62_limit_temps,
          div62_branch_entry,div62_swap_temps,div62_limit_temp,div62_sign.
           destruct (zlt (eta st) 0);repeat rewrite PTree.gso by discriminate.
           ++ rewrite PTree.gss,Int64.neg_repr;reflexivity.
           ++ exact Eta.
        -- unfold lef;rewrite div62_continued_temps_outside;[exact Index|].
           cbn [List.In];intuition discriminate.
Qed.
