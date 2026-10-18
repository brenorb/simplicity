(** Proved oracles for the original 128-bit helpers called by
    [secp256k1_fe_mul_inner].  Each oracle names the two result words of a
    helper by fresh variables whose meaning is the 128-bit integer update of
    the helper.  [mul], [accum_mul] and [accum_u64] are executed by the pure
    symbolic executor on their actual bodies (with [umul128] inlined); the
    resulting terms are checked against the helper's canonical result before
    the fresh names are introduced.  Soundness is a theorem over the real
    Clight calls; no helper behaviour is assumed. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem C.jet_sx_pure C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns.
Require Import C.jet_secp_symbolic_substitution C.jet_parallel_fe_mul_sx.
Require Import C.jet_secp_umul128_exec C.jet_secp_umul128_numeric.
Require Import C.jet_secp_u128_mul_exec C.jet_secp_u128_accum_mul_exec C.jet_secp_u128_accum_mul_numeric.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.

(** Event tags. *)
Definition tMUL : nat := 101.
Definition tACC : nat := 102.
Definition tADD : nat := 103.
Definition tSHR52 : nat := 104.
Definition tSHR64 : nat := 105.

Definition u128_sem (tag : nat) (vs : list Z) : option Z :=
  if Nat.eqb tag tMUL then match vs with [x; y] => Some (x * y) | _ => None end
  else if Nat.eqb tag tACC then
    match vs with [l; h; x; y] => Some ((h * 2 ^ 64 + l + x * y) mod 2 ^ 128) | _ => None end
  else if Nat.eqb tag tADD then
    match vs with [l; h; x] => Some ((h * 2 ^ 64 + l + x) mod 2 ^ 128) | _ => None end
  else if Nat.eqb tag tSHR52 then
    match vs with [l; h] => Some ((h * 2 ^ 64 + l) / 2 ^ 52) | _ => None end
  else if Nat.eqb tag tSHR64 then
    match vs with [l; h] => Some ((h * 2 ^ 64 + l) / 2 ^ 64) | _ => None end
  else None.

Definition uv (rho : nat -> int64) (x : sx) : Z := Int64.unsigned (lv rho x).

(** Meaning of an event: the two fresh words are the low and high words of
    the 128-bit result. *)
Definition u128_evok (rho : nat -> int64) (ev : event) : Prop :=
  ecnt ev = 2%nat /\
  exists v, u128_sem (etag ev) (map (uv rho) (eargs ev)) = Some v /\ 0 <= v < 2 ^ 128 /\
    Int64.unsigned (rho (ebase ev)) = v mod 2 ^ 64 /\
    Int64.unsigned (rho (S (ebase ev))) = v / 2 ^ 64.

Definition u128_inv : (nat -> int64) -> list event -> mem -> Prop := fun _ _ _ => True.
Definition u128_ext : block -> Prop := fun _ => False.

(** ** Cell replacement helpers *)
Lemma find_set_cell_other cs d d' ch ch' v :
  d <> d' -> find_cell (set_cell cs d ch v) d' ch' = find_cell cs d' ch'.
Proof.
  intros Hd. induction cs as [|c cs IH]; cbn; [reflexivity|].
  destruct (cell_at c d ch) eqn:E.
  - unfold cell_at in E. apply andb_true_iff in E as [E1 _]. apply Z.eqb_eq in E1.
    cbn. unfold cell_at at 1. cbn [cofs].
    destruct (Z.eqb d d') eqn:F; [apply Z.eqb_eq in F; contradiction|].
    unfold cell_at. rewrite E1, F. reflexivity.
  - cbn. destruct (cell_at c d' ch'); [reflexivity|exact IH].
Qed.

Lemma xload_xreplace_other regs r d d' x regs' :
  xreplace regs r d Mint64 x = Some regs' -> d <> d' ->
  xload regs' r d' tulong = xload regs r d' tulong.
Proof.
  unfold xreplace. intros H Hd.
  destruct (nth_error regs r) as [reg|] eqn:HR; [|discriminate].
  destruct (find_cell (rcells reg) d Mint64); [|discriminate].
  inversion H; subst regs'. unfold xload. change (access_mode tulong) with (By_value Mint64).
  rewrite (upd_same _ _ _ _ HR). cbn [rcells]. rewrite find_set_cell_other by exact Hd.
  rewrite HR. reflexivity.
Qed.

Lemma int64_eq_unsigned a b : Int64.unsigned a = Int64.unsigned b -> a = b.
Proof.
  intros H. rewrite <- (Int64.repr_unsigned a), <- (Int64.repr_unsigned b), H. reflexivity.
Qed.

Lemma den_fresh_long rho beta n x :
  isk KL x = true -> rho n = lv rho x -> den rho beta (XLv n) = den rho beta x.
Proof.
  intros HK HE. cbn [den]. rewrite (den_KL rho beta x HK), lv_den, HE. reflexivity.
Qed.

(** ** The inner-run oracle *)
Definition u128_inner (fd : function) (xs : list sx) (regs : list region) : option res :=
  xfun (genv_cenv secp_ge) [] (int_table u128_mul_functions) 300 fd xs regs [] 0.

Definition sigma4 (X Y L H : sx) (n : nat) : sx :=
  match n with 0 => X | 1 => Y | 2 => L | 3 => H | _ => XLc Int64.zero end%nat.

Definition orc_inner (tag : nat) (fd : function) (lo_c hi_c : sx)
    (mk : list sx -> list region -> option (nat * (nat -> sx) * list sx)) : oracle :=
  fun base log xs regs =>
  match mk xs regs with
  | Some (r, sigma, eargs) =>
    match u128_inner fd xs regs with
    | Some (RDone st ONormal) =>
      match slog st, (stemps st)!1%positive with
      | [], None =>
        match xload (sregs st) r 0 tulong, xload (sregs st) r 8 tulong with
        | Some lo, Some hi =>
          if sx_beq lo (sx_subst sigma lo_c) && sx_beq hi (sx_subst sigma hi_c)
             && isk KL lo && isk KL hi then
            match xreplace (sregs st) r 0 Mint64 (XLv base) with
            | Some r1 =>
              match xreplace r1 r 8 Mint64 (XLv (S base)) with
              | Some r2 => Some (r2, None, tag, 2%nat, eargs)
              | None => None end
            | None => None end
          else None
        | _, _ => None end
      | _, _ => None end
    | _ => None end
  | None => None end.

(** Semantic obligation of a kind: the canonical result words under the
    argument substitution are the two words of the 128-bit update. *)
Definition inner_sem_ok (tag : nat) (lo_c hi_c : sx)
    (mk : list sx -> list region -> option (nat * (nat -> sx) * list sx)) : Prop :=
  forall xs regs r sigma eargs, mk xs regs = Some (r, sigma, eargs) ->
  long_subst sigma /\
  forall rho, exists v, u128_sem tag (map (uv rho) eargs) = Some v /\ 0 <= v < 2 ^ 128 /\
    Int64.unsigned (lv (fun n => lv rho (sigma n)) lo_c) = v mod 2 ^ 64 /\
    Int64.unsigned (lv (fun n => lv rho (sigma n)) hi_c) = v / 2 ^ 64.

Lemma u128_inner_pure fd xs regs st rho beta m :
  u128_inner fd xs regs = Some (RDone st ONormal) -> slog st = [] ->
  rep rho beta regs m ->
  exists m' vres,
    ClightBigstep.eval_funcall function_entry2 secp_ge m (Internal fd)
      (map (den rho (lay beta)) xs) E0 m' vres /\
    rep rho beta (sregs st) m' /\
    match (stemps st)!1%positive with
    | Some x => vres = den rho (lay beta) x | None => vres = Vundef end /\
    map rshape (sregs st) = map rshape regs /\
    lframe (fun b o => ~ foot beta (map rshape regs) b o) m m'.
Proof.
  intros HRun HLog HRep.
  destruct (xfun_pure secp_ge u128_mul_functions u128_mul_functions_ok 300 fd xs regs 0
    (RDone st ONormal) HRun ltac:(cbn [leaves_log_nil]; rewrite HLog; reflexivity) rho beta m HRep)
    as (m' & vres & HCall & HFinal & HRet & HShape & HFrame).
  exists m', vres. cbn [rsel fst] in HFinal, HRet, HShape. auto.
Qed.

Theorem orc_inner_ok tag fd lo_c hi_c mk :
  inner_sem_ok tag lo_c hi_c mk ->
  oracle_ok secp_ge u128_evok u128_inv u128_ext fd (orc_inner tag fd lo_c hi_c mk).
Proof.
  intros HSem base xs regs regs' v tag' cnt eargs' log rho beta m HRun HRep _ _ _ HEv.
  unfold orc_inner in HRun.
  destruct (mk xs regs) as [[[r sigma] ea]|] eqn:HMk; [|discriminate].
  destruct (u128_inner fd xs regs) as [[st [] | ? ? ?]|] eqn:HIn; try discriminate.
  destruct (slog st) as [|? ?] eqn:HLog; [|discriminate].
  destruct ((stemps st)!1%positive) eqn:HRet; [discriminate|].
  destruct (xload (sregs st) r 0 tulong) as [lo|] eqn:HLo; [|discriminate].
  destruct (xload (sregs st) r 8 tulong) as [hi|] eqn:HHi; [|discriminate].
  destruct (sx_beq lo (sx_subst sigma lo_c) && sx_beq hi (sx_subst sigma hi_c)
    && isk KL lo && isk KL hi) eqn:HChk; [|discriminate].
  apply andb_true_iff in HChk as [HChk HKH]. apply andb_true_iff in HChk as [HChk HKL].
  apply andb_true_iff in HChk as [HBL HBH].
  apply sx_beq_true in HBL. apply sx_beq_true in HBH.
  destruct (xreplace (sregs st) r 0 Mint64 (XLv base)) as [r1|] eqn:HR1; [|discriminate].
  destruct (xreplace r1 r 8 Mint64 (XLv (S base))) as [r2|] eqn:HR2; [|discriminate].
  inversion HRun; subst regs' v tag' cnt eargs'; clear HRun.
  destruct (HSem xs regs r sigma ea HMk) as [HLong HVal].
  destruct (HVal rho) as (w & HW & HWR & HWL & HWH).
  destruct HEv as (_ & w' & HW' & _ & HBL' & HBH'). cbn [etag eargs ebase] in HW', HBL', HBH'.
  rewrite HW in HW'. inversion HW'; subst w'; clear HW'.
  assert (HLoV : rho base = lv rho lo).
  { apply int64_eq_unsigned. rewrite HBL', HBL, lv_sx_subst by exact HLong. symmetry; exact HWL. }
  assert (HHiV : rho (S base) = lv rho hi).
  { apply int64_eq_unsigned. rewrite HBH', HBH, lv_sx_subst by exact HLong. symmetry; exact HWH. }
  destruct (u128_inner_pure fd xs regs st rho beta m HIn HLog HRep)
    as (m' & vres & HCall & HFinal & HVres & HShape & HFrame).
  rewrite HRet in HVres.
  assert (HRep1 : rep rho beta r1 m').
  { apply (rep_replace rho beta (sregs st) m' r 0 lo (XLv base) r1 HFinal HLo);
      [apply den_fresh_long; assumption|reflexivity|exact HR1]. }
  assert (HRep2 : rep rho beta r2 m').
  { apply (rep_replace rho beta r1 m' r 8 hi (XLv (S base)) r2 HRep1);
      [rewrite (xload_xreplace_other _ _ _ _ _ _ HR1) by lia; exact HHi
      |apply den_fresh_long; assumption|reflexivity|exact HR2]. }
  exists m', vres. split; [exact HCall|]. split; [exact HRep2|]. split; [exact I|].
  split; [rewrite (xreplace_shape _ _ _ _ _ _ HR2), (xreplace_shape _ _ _ _ _ _ HR1); exact HShape|].
  split; [exact HVres|].
  eapply lframe_implies; [exact HFrame|].
  intros b o (HV & HF & HE) _. exact HF.
Qed.

(** ** The three kinds executed through their bodies *)
Definition add64_lo : sx := XLb Badd (XLv 2) (XLv 0).
Definition add64_hi : sx :=
  XLb Badd (XLv 3) (XI2L Signed (XLcmp Clt Unsigned (XLb Badd (XLv 2) (XLv 0)) (XLv 0))).

Definition mk_mul (xs : list sx) (regs : list region) :=
  match xs with
  | [XP r 0; X; Y] =>
      if isk KL X && isk KL Y
      then Some (r, sigma4 X Y (XLc Int64.zero) (XLc Int64.zero), [X; Y]) else None
  | _ => None end.
Definition mk_acc (xs : list sx) (regs : list region) :=
  match xs with
  | [XP r 0; X; Y] =>
      match xload regs r 0 tulong, xload regs r 8 tulong with
      | Some L, Some H =>
          if isk KL X && isk KL Y && isk KL L && isk KL H
          then Some (r, sigma4 X Y L H, [L; H; X; Y]) else None
      | _, _ => None end
  | _ => None end.
Definition mk_add64 (xs : list sx) (regs : list region) :=
  match xs with
  | [XP r 0; X] =>
      match xload regs r 0 tulong, xload regs r 8 tulong with
      | Some L, Some H =>
          if isk KL X && isk KL L && isk KL H
          then Some (r, sigma4 X (XLc Int64.zero) L H, [L; H; X]) else None
      | _, _ => None end
  | _ => None end.

Definition orc_mul := orc_inner tMUL f_secp256k1_u128_mul umul128_lo umul128_hi mk_mul.
Definition orc_acc := orc_inner tACC f_secp256k1_u128_accum_mul accum_mul_lo accum_mul_hi mk_acc.
Definition orc_add64 := orc_inner tADD f_secp256k1_u128_accum_u64 add64_lo add64_hi mk_add64.

Lemma sigma4_long X Y L H :
  isk KL X = true -> isk KL Y = true -> isk KL L = true -> isk KL H = true ->
  long_subst (sigma4 X Y L H).
Proof. intros HX HY HL HH n. do 4 (destruct n as [|n]; [assumption|]). reflexivity. Qed.

Lemma uns_range x : 0 <= Int64.unsigned x < 2 ^ 64.
Proof. exact (Int64.unsigned_range x). Qed.

Lemma two_word_split v : 0 <= v < 2 ^ 128 ->
  0 <= v mod 2 ^ 64 < 2 ^ 64 /\ 0 <= v / 2 ^ 64 < 2 ^ 64.
Proof.
  intros Hv. split; [apply Z.mod_pos_bound; lia|].
  split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia].
Qed.

Ltac mk_cases H :=
  repeat match type of H with
  | context [match ?x with _ => _ end] =>
      let E := fresh "E" in destruct x eqn:E; try discriminate
  end.
Ltac bool_split :=
  repeat match goal with
  | H : _ && _ = true |- _ => apply andb_true_iff in H; destruct H
  end.

Lemma mk_mul_inv xs regs r sigma eargs : mk_mul xs regs = Some (r, sigma, eargs) ->
  exists X Y, eargs = [X; Y] /\ sigma = sigma4 X Y (XLc Int64.zero) (XLc Int64.zero) /\
    isk KL X = true /\ isk KL Y = true.
Proof.
  unfold mk_mul. intros H. mk_cases H. inversion H; subst. bool_split.
  do 2 eexists. split; [reflexivity|]. split; [reflexivity|]. repeat split; assumption.
Qed.
Lemma mk_acc_inv xs regs r sigma eargs : mk_acc xs regs = Some (r, sigma, eargs) ->
  exists X Y L H, eargs = [L; H; X; Y] /\ sigma = sigma4 X Y L H /\
    isk KL X = true /\ isk KL Y = true /\ isk KL L = true /\ isk KL H = true.
Proof.
  unfold mk_acc. intros H. mk_cases H. inversion H; subst. bool_split.
  do 4 eexists. split; [reflexivity|]. split; [reflexivity|]. repeat split; assumption.
Qed.
Lemma mk_add64_inv xs regs r sigma eargs : mk_add64 xs regs = Some (r, sigma, eargs) ->
  exists X L H, eargs = [L; H; X] /\ sigma = sigma4 X (XLc Int64.zero) L H /\
    isk KL X = true /\ isk KL L = true /\ isk KL H = true.
Proof.
  unfold mk_add64. intros H. mk_cases H. inversion H; subst. bool_split.
  do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. repeat split; assumption.
Qed.

Lemma lv_umul_lo rho : lv rho umul128_lo = umul128_lo_machine (rho 0%nat) (rho 1%nat).
Proof. unfold lv; rewrite umul128_lo_den; reflexivity. Qed.
Lemma lv_umul_hi rho : lv rho umul128_hi = umul128_hi_machine (rho 0%nat) (rho 1%nat).
Proof. unfold lv; rewrite umul128_hi_den; reflexivity. Qed.
Lemma lv_acc_lo rho : lv rho accum_mul_lo = accum_mul_lo_machine rho.
Proof. unfold lv; rewrite accum_mul_lo_den; reflexivity. Qed.
Lemma lv_acc_hi rho : lv rho accum_mul_hi = accum_mul_hi_machine rho.
Proof. unfold lv; rewrite accum_mul_hi_den; reflexivity. Qed.

Lemma mul_sem_ok : inner_sem_ok tMUL umul128_lo umul128_hi mk_mul.
Proof.
  intros xs regs r sigma eargs HMk.
  destruct (mk_mul_inv _ _ _ _ _ HMk) as (X & Y & -> & -> & HX & HY).
  split; [apply sigma4_long; auto|].
  intros rho. exists (uv rho X * uv rho Y).
  pose proof (uns_range (lv rho X)) as RX. pose proof (uns_range (lv rho Y)) as RY.
  unfold uv in *.
  split; [reflexivity|]. split; [nia|].
  destruct (umul128_unsigned_outputs (lv rho X) (lv rho Y)) as [HH HL].
  rewrite lv_umul_lo, lv_umul_hi. cbn [sigma4].
  rewrite HL, HH. split; reflexivity.
Qed.

Lemma acc_sem_ok : inner_sem_ok tACC accum_mul_lo accum_mul_hi mk_acc.
Proof.
  intros xs regs r sigma eargs HMk.
  destruct (mk_acc_inv _ _ _ _ _ HMk) as (X & Y & L & H & -> & -> & HX & HY & HL & HH).
  split; [apply sigma4_long; auto|].
  intros rho. set (rho' := fun n => lv rho (sigma4 X Y L H n)).
  pose proof (accum_mul_numeric_value rho') as HV.
  exists ((uv rho H * 2 ^ 64 + uv rho L + uv rho X * uv rho Y) mod 2 ^ 128).
  split; [reflexivity|]. split; [apply Z.mod_pos_bound; lia|].
  rewrite lv_acc_lo, lv_acc_hi.
  change (Int64.modulus) with (2 ^ 64) in HV.
  change (2 ^ 64 * 2 ^ 64) with (2 ^ 128) in HV.
  change (Int64.unsigned (rho' 3%nat)) with (uv rho H) in HV.
  change (Int64.unsigned (rho' 2%nat)) with (uv rho L) in HV.
  change (Int64.unsigned (rho' 0%nat)) with (uv rho X) in HV.
  change (Int64.unsigned (rho' 1%nat)) with (uv rho Y) in HV.
  rewrite <- HV.
  pose proof (uns_range (accum_mul_lo_machine rho')) as R1.
  pose proof (uns_range (accum_mul_hi_machine rho')) as R2.
  split.
  - rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Lemma add64_carry_value L H X :
  let lo := Int64.add L X in
  let hi := Int64.add H (Int64.repr (Int.signed (if Int64.ltu lo X then Int.one else Int.zero))) in
  Int64.unsigned hi * 2 ^ 64 + Int64.unsigned lo =
    (Int64.unsigned H * 2 ^ 64 + Int64.unsigned L + Int64.unsigned X) mod 2 ^ 128.
Proof.
  intros lo hi.
  pose proof (uns_range L) as RL. pose proof (uns_range H) as RH. pose proof (uns_range X) as RX.
  assert (HLo : Int64.unsigned lo = (Int64.unsigned L + Int64.unsigned X) mod 2 ^ 64).
  { unfold lo. rewrite Int64.add_unsigned, Int64.unsigned_repr_eq. reflexivity. }
  assert (HC : Int.signed (if Int64.ltu lo X then Int.one else Int.zero) =
    (Int64.unsigned L + Int64.unsigned X) / 2 ^ 64).
  { unfold Int64.ltu. rewrite HLo.
    destruct (Z_lt_dec (Int64.unsigned L + Int64.unsigned X) (2 ^ 64)) as [HS|HS].
    - rewrite Z.mod_small by lia. rewrite Z.div_small by lia.
      destruct (zlt (Int64.unsigned L + Int64.unsigned X) (Int64.unsigned X)); [lia|reflexivity].
    - assert (HM : (Int64.unsigned L + Int64.unsigned X) mod 2 ^ 64 =
        Int64.unsigned L + Int64.unsigned X - 2 ^ 64).
      { rewrite <- (Z.mod_add _ (-1)) by lia. apply Z.mod_small. lia. }
      assert (HD : (Int64.unsigned L + Int64.unsigned X) / 2 ^ 64 = 1).
      { symmetry. apply Z.div_unique with (Int64.unsigned L + Int64.unsigned X - 2 ^ 64); lia. }
      rewrite HM, HD. destruct (zlt _ (Int64.unsigned X)); [reflexivity|lia]. }
  assert (HHi : Int64.unsigned hi =
    (Int64.unsigned H + (Int64.unsigned L + Int64.unsigned X) / 2 ^ 64) mod 2 ^ 64).
  { unfold hi. rewrite Int64.add_unsigned, Int64.unsigned_repr_eq. f_equal. f_equal.
    rewrite HC. apply Int64.unsigned_repr.
    assert (0 <= (Int64.unsigned L + Int64.unsigned X) / 2 ^ 64 <= 1).
    { split; [apply Z.div_pos; lia|]. apply Z.lt_succ_r. apply Z.div_lt_upper_bound; lia. }
    change Int64.max_unsigned with (2 ^ 64 - 1). lia. }
  rewrite HHi, HLo.
  pose proof (accum_mul_two_limb_mod (2 ^ 64) (Int64.unsigned H) (Int64.unsigned L)
    (Int64.unsigned X) ltac:(lia)) as HT.
  rewrite (Z.div_small (Int64.unsigned X)) in HT by lia.
  rewrite (Z.mod_small (Int64.unsigned X)) in HT by lia.
  rewrite Z.add_0_r in HT. change (2 ^ 64 * 2 ^ 64) with (2 ^ 128) in HT. exact HT.
Qed.

Lemma lv_add64_lo rho : lv rho add64_lo = Int64.add (rho 2%nat) (rho 0%nat).
Proof. reflexivity. Qed.
Lemma lv_add64_hi rho : lv rho add64_hi = Int64.add (rho 3%nat)
  (Int64.repr (Int.signed (if Int64.ltu (Int64.add (rho 2%nat) (rho 0%nat)) (rho 0%nat)
    then Int.one else Int.zero))).
Proof. reflexivity. Qed.

Lemma add64_sem_ok : inner_sem_ok tADD add64_lo add64_hi mk_add64.
Proof.
  intros xs regs r sigma eargs HMk.
  destruct (mk_add64_inv _ _ _ _ _ HMk) as (X & L & H & -> & -> & HX & HL & HH).
  split; [apply sigma4_long; auto|].
  intros rho.
  pose proof (add64_carry_value (lv rho L) (lv rho H) (lv rho X)) as HV. cbv zeta in HV.
  exists ((uv rho H * 2 ^ 64 + uv rho L + uv rho X) mod 2 ^ 128).
  split; [reflexivity|]. split; [apply Z.mod_pos_bound; lia|].
  unfold uv. rewrite <- HV. rewrite lv_add64_lo, lv_add64_hi. cbn [sigma4].
  match goal with |- context [Int64.unsigned ?h * 2 ^ 64 + Int64.unsigned ?l] =>
    pose proof (uns_range l) as R1; pose proof (uns_range h) as R2 end.
  split.
  - rewrite Z.add_comm, Z.mod_add by lia. rewrite Z.mod_small by lia. reflexivity.
  - rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Theorem orc_mul_ok :
  oracle_ok secp_ge u128_evok u128_inv u128_ext f_secp256k1_u128_mul orc_mul.
Proof. apply orc_inner_ok, mul_sem_ok. Qed.
Theorem orc_acc_ok :
  oracle_ok secp_ge u128_evok u128_inv u128_ext f_secp256k1_u128_accum_mul orc_acc.
Proof. apply orc_inner_ok, acc_sem_ok. Qed.
Theorem orc_add64_ok :
  oracle_ok secp_ge u128_evok u128_inv u128_ext f_secp256k1_u128_accum_u64 orc_add64.
Proof. apply orc_inner_ok, add64_sem_ok. Qed.
Print Assumptions orc_mul_ok.
Print Assumptions orc_acc_ok.
Print Assumptions orc_add64_ok.
