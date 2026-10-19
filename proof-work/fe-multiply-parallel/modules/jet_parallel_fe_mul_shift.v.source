(** Proved fresh-word oracle for the original [secp256k1_u128_rshift] at the
    two counts used by [secp256k1_fe_mul_inner] (52 and 64).  The count 52
    takes the [0 < n < 64] branch, executed here through its actual statements;
    the count 64 reuses the existing checked execution of its branch. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Events Values Globalenvs.
Require Import C.jet_exec C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_u128_shift64_expr C.jet_secp_u128_shift64_body C.jet_secp_u128_shift64_rep.
Require Import C.jet_secp_fe_math C.jet_parallel_fe_mul_oracle.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.

Definition u128_shift_temps b n :=
  PTree.set jets_secp._n (Vint n)
    (PTree.set jets_secp._r (Vptr b Ptrofs.zero)
      (create_undef_temps (fn_temps f_secp256k1_u128_rshift))).
Lemma u128_shift_entry m b n :
  function_entry2 secp_ge f_secp256k1_u128_rshift
    [Vptr b Ptrofs.zero; Vint n] m empty_env (u128_shift_temps b n) m.
Proof.
  constructor.
  - cbn; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - constructor.
  - reflexivity.
Qed.

(** Machine words written by the [0 < n < 64] branch at n = 52. *)
Definition shift52_lo (l h : int64) : int64 :=
  Int64.or (Int64.shl (Int64.mul (Int64.repr 1) h) (Int64.repr 12)) (Int64.shru l (Int64.repr 52)).
Definition shift52_hi (h : int64) : int64 := Int64.shru h (Int64.repr 52).

Definition u128_shift52_branch :=
  match fn_body f_secp256k1_u128_rshift with
  | Ssequence _ (Sifthenelse _ _ (Sifthenelse _ s _)) => s | _ => Sskip
  end.
Definition u128_shift_test0 :=
  match fn_body f_secp256k1_u128_rshift with
  | Ssequence _ (Sifthenelse _ _ (Sifthenelse c _ _)) => c | _ => Econst_int Int.zero tint
  end.
Lemma u128_shift52_actual_body : fn_body f_secp256k1_u128_rshift =
  Ssequence (Sloop Sskip Sbreak)
    (Sifthenelse u128_shift_test u128_shift64_then
      (Sifthenelse u128_shift_test0 u128_shift52_branch Sskip)).
Proof. reflexivity. Qed.

Lemma u128_shift52_branch_eq : u128_shift52_branch =
  Ssequence
    (Ssequence (Sset jets_secp._t'2 (u128_field jets_secp._hi))
      (Ssequence (Sset jets_secp._t'3 (u128_field jets_secp._lo))
        (Sassign (u128_field jets_secp._lo)
          (Ebinop Oor
            (Ebinop Oshl
              (Ebinop Omul (Econst_int (Int.repr 1) tuint) (Etempvar jets_secp._t'2 tulong) tulong)
              (Ebinop Osub (Econst_int (Int.repr 64) tint) (Etempvar jets_secp._n tuint) tuint) tulong)
            (Ebinop Oshr (Etempvar jets_secp._t'3 tulong) (Etempvar jets_secp._n tuint) tulong)
            tulong))))
    (Ssequence (Sset jets_secp._t'1 (u128_field jets_secp._hi))
      (Sassign (u128_field jets_secp._hi)
        (Ebinop Oshr (Etempvar jets_secp._t'1 tulong) (Etempvar jets_secp._n tuint) tulong))).
Proof. reflexivity. Qed.

Lemma eval_u128_lo m le b value :
  le!jets_secp._r = Some (Vptr b Ptrofs.zero) ->
  Mem.load Mint64 m b 0 = Some (Vlong value) ->
  eval_expr secp_ge empty_env le m (u128_field jets_secp._lo) (Vlong value).
Proof.
  intros HT HL. eapply eval_Elvalue.
  - eapply u128_field_lvalue; [exact HT|left; split; reflexivity].
  - apply deref_loc_value with (chunk := Mint64).
    + reflexivity.
    + change (Mem.load Mint64 m b 0 = Some (Vlong value)); exact HL.
Qed.

Theorem exec_u128_shift52_body m m1 mf le b l h :
  le!jets_secp._r = Some (Vptr b Ptrofs.zero) ->
  le!jets_secp._n = Some (Vint (Int.repr 52)) ->
  Mem.load Mint64 m b 0 = Some (Vlong l) ->
  Mem.load Mint64 m b 8 = Some (Vlong h) ->
  Mem.store Mint64 m b 0 (Vlong (shift52_lo l h)) = Some m1 ->
  Mem.store Mint64 m1 b 8 (Vlong (shift52_hi h)) = Some mf ->
  exists le', Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_u128_rshift)
    E0 le' mf Out_normal.
Proof.
  intros HR HN HL HH HS1 HS2.
  set (le1 := PTree.set jets_secp._t'2 (Vlong h) le).
  set (le2 := PTree.set jets_secp._t'3 (Vlong l) le1).
  set (le3 := PTree.set jets_secp._t'1 (Vlong h) le2).
  assert (HR1 : le1!jets_secp._r = Some (Vptr b Ptrofs.zero)) by (unfold le1; rewrite PTree.gso by discriminate; exact HR).
  assert (HR2 : le2!jets_secp._r = Some (Vptr b Ptrofs.zero)) by (unfold le2; rewrite PTree.gso by discriminate; exact HR1).
  assert (HR3 : le3!jets_secp._r = Some (Vptr b Ptrofs.zero)) by (unfold le3; rewrite PTree.gso by discriminate; exact HR2).
  assert (HN2 : le2!jets_secp._n = Some (Vint (Int.repr 52))).
  { unfold le2, le1; rewrite !PTree.gso by discriminate; exact HN. }
  assert (HN3 : le3!jets_secp._n = Some (Vint (Int.repr 52))).
  { unfold le3; rewrite PTree.gso by discriminate; exact HN2. }
  assert (HT2 : le2!jets_secp._t'2 = Some (Vlong h)).
  { unfold le2; rewrite PTree.gso by discriminate; apply PTree.gss. }
  assert (HT3 : le2!jets_secp._t'3 = Some (Vlong l)) by apply PTree.gss.
  assert (HT1 : le3!jets_secp._t'1 = Some (Vlong h)) by apply PTree.gss.
  assert (HH1 : Mem.load Mint64 m1 b 8 = Some (Vlong h)).
  { rewrite (Mem.load_store_other _ _ _ _ _ _ HS1); [exact HH|]. right; right; cbn; lia. }
  exists le3. rewrite u128_shift52_actual_body.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le).
  - change E0 with (E0 ** E0).
    eapply exec_Sloop_stop2 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le)
      (out1 := Out_normal) (out2 := Out_break); constructor.
  - eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
    + unfold u128_shift_test.
      eapply eval_Ebinop with (v1 := Vint (Int.repr 52)) (v2 := Vint (Int.repr 64)).
      * eapply eval_Etempvar; exact HN.
      * constructor.
      * vm_compute; reflexivity.
    + reflexivity.
    + eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true).
      * change u128_shift_test0 with
          (Ebinop Ogt (Etempvar jets_secp._n tuint) (Econst_int (Int.repr 0) tint) tint).
        eapply eval_Ebinop with (v1 := Vint (Int.repr 52)) (v2 := Vint (Int.repr 0)).
        -- eapply eval_Etempvar; exact HN.
        -- constructor.
        -- vm_compute; reflexivity.
      * reflexivity.
      * rewrite u128_shift52_branch_eq.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le2).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
           ++ apply exec_Sset. apply eval_u128_hi with (b := b); assumption.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
              ** apply exec_Sset. apply eval_u128_lo with (b := b); assumption.
              ** eapply exec_Sassign with (loc := b)
                   (ofs := Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) (bf := Full)
                   (v2 := Vlong (shift52_lo l h)) (v := Vlong (shift52_lo l h)).
                 --- apply u128_field_lvalue; [exact HR2|left; split; reflexivity].
                 --- eapply eval_Ebinop.
                     +++ eapply eval_Ebinop.
                         *** eapply eval_Ebinop; [constructor|eapply eval_Etempvar; exact HT2|reflexivity].
                         *** eapply eval_Ebinop; [constructor|eapply eval_Etempvar; exact HN2|reflexivity].
                         *** reflexivity.
                     +++ eapply eval_Ebinop.
                         *** eapply eval_Etempvar; exact HT3.
                         *** eapply eval_Etempvar; exact HN2.
                         *** reflexivity.
                     +++ reflexivity.
                 --- reflexivity.
                 --- apply assign_loc_value with (chunk := Mint64); [reflexivity|].
                     change (Mem.store Mint64 m b 0 (Vlong (shift52_lo l h)) = Some m1); exact HS1.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le3).
           ++ apply exec_Sset. apply eval_u128_hi with (b := b); assumption.
           ++ eapply exec_Sassign with (loc := b)
                (ofs := Ptrofs.add Ptrofs.zero (Ptrofs.repr 8)) (bf := Full)
                (v2 := Vlong (shift52_hi h)) (v := Vlong (shift52_hi h)).
              ** apply u128_field_lvalue; [exact HR3|right; split; reflexivity].
              ** eapply eval_Ebinop.
                 --- eapply eval_Etempvar; exact HT1.
                 --- eapply eval_Etempvar; exact HN3.
                 --- reflexivity.
              ** reflexivity.
              ** apply assign_loc_value with (chunk := Mint64); [reflexivity|].
                 change (Mem.store Mint64 m1 b 8 (Vlong (shift52_hi h)) = Some mf); exact HS2.
Qed.

(** Integer meaning of the written words. *)
Lemma uns_shl12 h : Int64.unsigned (Int64.shl h (Int64.repr 12)) =
  (Int64.unsigned h mod 2 ^ 52) * 2 ^ 12.
Proof.
  rewrite Int64.shl_mul_two_p. change (two_p (Int64.unsigned (Int64.repr 12))) with (2 ^ 12).
  unfold Int64.mul. rewrite Int64.unsigned_repr_eq.
  change (Int64.unsigned (Int64.repr (2 ^ 12))) with (2 ^ 12).
  change Int64.modulus with (2 ^ 52 * 2 ^ 12). apply Z.mul_mod_distr_r; lia.
Qed.
Lemma uns_shru l k : 0 <= k < 64 ->
  Int64.unsigned (Int64.shru l (Int64.repr k)) = Int64.unsigned l / 2 ^ k.
Proof.
  intros Hk. rewrite Int64.shru_div_two_p.
  assert (HK : Int64.unsigned (Int64.repr k) = k).
  { apply Int64.unsigned_repr. change Int64.max_unsigned with (2 ^ 64 - 1). lia. }
  rewrite HK, two_p_equiv.
  pose proof (Int64.unsigned_range l). change Int64.modulus with (2 ^ 64) in *.
  assert (1 <= 2 ^ k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (0 <= Int64.unsigned l / 2 ^ k <= Int64.unsigned l).
  { split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; nia]. }
  apply Int64.unsigned_repr. change Int64.max_unsigned with (2 ^ 64 - 1). lia.
Qed.

Lemma shift52_values l h :
  let v := (Int64.unsigned h * 2 ^ 64 + Int64.unsigned l) / 2 ^ 52 in
  Int64.unsigned (shift52_lo l h) = v mod 2 ^ 64 /\
  Int64.unsigned (shift52_hi h) = v / 2 ^ 64.
Proof.
  intros v.
  pose proof (Int64.unsigned_range l) as RL. pose proof (Int64.unsigned_range h) as RH.
  change Int64.modulus with (2 ^ 64) in RL, RH.
  assert (HV : v = Int64.unsigned h * 2 ^ 12 + Int64.unsigned l / 2 ^ 52).
  { unfold v. replace (Int64.unsigned h * 2 ^ 64 + Int64.unsigned l) with
      (Int64.unsigned l + (Int64.unsigned h * 2 ^ 12) * 2 ^ 52) by lia.
    rewrite Z.div_add by lia. lia. }
  assert (HU : 0 <= Int64.unsigned l / 2 ^ 52 < 2 ^ 12).
  { split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]. }
  pose proof (Z.div_mod (Int64.unsigned h) (2 ^ 52) ltac:(lia)) as DH.
  pose proof (Z.mod_pos_bound (Int64.unsigned h) (2 ^ 52) ltac:(lia)) as BH.
  assert (HDec : v = (Int64.unsigned h / 2 ^ 52) * 2 ^ 64 +
    (Int64.unsigned l / 2 ^ 52 + (Int64.unsigned h mod 2 ^ 52) * 2 ^ 12)) by lia.
  split.
  - unfold shift52_lo. rewrite Int64.mul_commut, Int64.mul_one.
    unfold Int64.or. rewrite uns_shl12, uns_shru by lia.
    rewrite Z.lor_comm, lor_shift_add by lia.
    rewrite Int64.unsigned_repr by (change Int64.max_unsigned with (2 ^ 64 - 1); lia).
    rewrite HDec.
    apply Z.mod_unique with (Int64.unsigned h / 2 ^ 52); [left; lia|lia].
  - unfold shift52_hi. rewrite uns_shru by lia.
    rewrite HDec.
    apply Z.div_unique with (Int64.unsigned l / 2 ^ 52 + (Int64.unsigned h mod 2 ^ 52) * 2 ^ 12);
      [left; lia|lia].
Qed.

(** ** The oracle *)
Definition shr_tag (n : int) : option nat :=
  if Int.eq n (Int.repr 52) then Some tSHR52
  else if Int.eq n (Int.repr 64) then Some tSHR64 else None.

Definition orc_shr : oracle := fun base log xs regs =>
  match xs with
  | [XP r 0; XIc n] =>
    match shr_tag n, nth_error regs r with
    | Some t, Some reg =>
      match rfree reg with
      | Some 16 =>
        match xload regs r 0 tulong, xload regs r 8 tulong with
        | Some L, Some H =>
          if isk KL L && isk KL H then
            match xstore regs r 0 Mint64 (XLv base) with
            | Some r1 =>
              match xstore r1 r 8 Mint64 (XLv (S base)) with
              | Some r2 => Some (r2, None, t, 2%nat, [L; H])
              | None => None end
            | None => None end
          else None
        | _, _ => None end
      | _ => None end
    | _, _ => None end
  | _ => None end.

Lemma orc_shr_inv base log xs regs regs' v tag cnt eargs :
  orc_shr base log xs regs = Some (regs', v, tag, cnt, eargs) ->
  exists r n reg L H r1, xs = [XP r 0; XIc n] /\ shr_tag n = Some tag /\
    nth_error regs r = Some reg /\ rfree reg = Some 16 /\
    xload regs r 0 tulong = Some L /\ xload regs r 8 tulong = Some H /\
    isk KL L = true /\ isk KL H = true /\
    xstore regs r 0 Mint64 (XLv base) = Some r1 /\
    xstore r1 r 8 Mint64 (XLv (S base)) = Some regs' /\
    v = None /\ cnt = 2%nat /\ eargs = [L; H].
Proof.
  unfold orc_shr. intros HO. mk_cases HO. inversion HO; subst. bool_split.
  do 6 eexists. repeat (split; [eassumption || reflexivity|]). repeat split; reflexivity.
Qed.

Lemma shr_tag_cases n t : shr_tag n = Some t ->
  (n = Int.repr 52 /\ t = tSHR52) \/ (n = Int.repr 64 /\ t = tSHR64).
Proof.
  unfold shr_tag. destruct (Int.eq n (Int.repr 52)) eqn:E1.
  - apply Int.same_if_eq in E1. intros H; inversion H; auto.
  - destruct (Int.eq n (Int.repr 64)) eqn:E2; [|discriminate].
    apply Int.same_if_eq in E2. intros H; inversion H; auto.
Qed.

Theorem orc_shr_ok :
  oracle_ok secp_ge u128_evok u128_inv u128_ext f_secp256k1_u128_rshift orc_shr.
Proof.
  intros base xs regs regs' v tag cnt eargs log rho beta m HRun HRep _ _ _ HEv.
  destruct (orc_shr_inv _ _ _ _ _ _ _ _ _ HRun)
    as (r & n & reg & L & H & r1 & -> & HTag & HR & HFree & HL & HH & HKL & HKH &
      HS1 & HS2 & -> & -> & ->).
  pose proof (rep_owned_region_base_zero rho beta regs m r reg 16 HRep HR HFree) as HBase.
  pose proof (xload_u64_defined_sound rho beta regs m r 0 L HRep HL) as HLoadL.
  pose proof (xload_u64_defined_sound rho beta regs m r 8 H HRep HH) as HLoadH.
  rewrite HBase in HLoadL, HLoadH. cbn [Z.add] in HLoadL, HLoadH.
  rewrite (den_KL rho (lay beta) L HKL), lv_den in HLoadL.
  rewrite (den_KL rho (lay beta) H HKH), lv_den in HLoadH.
  destruct (xstore_sound rho beta regs m r 0 Mint64 (XLv base) r1 HRep HS1)
    as (m1 & HM1 & _ & HRep1 & HU1).
  destruct (xstore_sound rho beta r1 m1 r 8 Mint64 (XLv (S base)) regs' HRep1 HS2)
    as (mf & HM2 & _ & HRep2 & HU2).
  pose proof (xstore_shape _ _ _ _ _ _ HS1) as HSh1. pose proof (xstore_shape _ _ _ _ _ _ HS2) as HSh2.
  rewrite HBase in HM1, HM2. cbn [Z.add den] in HM1, HM2.
  destruct HEv as (_ & w & HW & HWR & HWL & HWH). cbn [etag eargs ebase map] in HW, HWL, HWH.
  unfold uv in HW.
  assert (HCall : exists le', Clight2.exec_stmt secp_ge empty_env (u128_shift_temps (blk beta r) n) m
      (fn_body f_secp256k1_u128_rshift) E0 le' mf Out_normal).
  { destruct (shr_tag_cases n tag HTag) as [[-> ->]|[-> ->]].
    - change (Some ((Int64.unsigned (lv rho H) * 2 ^ 64 + Int64.unsigned (lv rho L)) / 2 ^ 52)
        = Some w) in HW. injection HW as HW. rewrite <- HW in HWL, HWH.
      destruct (shift52_values (lv rho L) (lv rho H)) as [V1 V2].
      assert (E1 : rho base = shift52_lo (lv rho L) (lv rho H)).
      { apply int64_eq_unsigned. rewrite V1. exact HWL. }
      assert (E2 : rho (S base) = shift52_hi (lv rho H)).
      { apply int64_eq_unsigned. rewrite V2. exact HWH. }
      rewrite E1 in HM1. rewrite E2 in HM2.
      eapply exec_u128_shift52_body; [reflexivity|reflexivity|exact HLoadL|exact HLoadH|exact HM1|exact HM2].
    - change (Some ((Int64.unsigned (lv rho H) * 2 ^ 64 + Int64.unsigned (lv rho L)) / 2 ^ 64)
        = Some w) in HW. injection HW as HW. rewrite <- HW in HWL, HWH.
      try change (Z.pow_pos 2 64) with (2 ^ 64) in HWL, HWH.
      pose proof (Int64.unsigned_range (lv rho L)) as RL.
      pose proof (Int64.unsigned_range (lv rho H)) as RH. change Int64.modulus with (2 ^ 64) in RL, RH.
      assert (HD : (Int64.unsigned (lv rho H) * 2 ^ 64 + Int64.unsigned (lv rho L)) / 2 ^ 64 =
        Int64.unsigned (lv rho H)).
      { rewrite Z.add_comm, Z.div_add by lia. rewrite Z.div_small by lia. lia. }
      rewrite HD in HWL, HWH.
      assert (E1 : rho base = lv rho H).
      { apply int64_eq_unsigned. rewrite HWL. apply Z.mod_small. lia. }
      assert (E2 : rho (S base) = Int64.zero).
      { apply int64_eq_unsigned. rewrite HWH, Z.div_small by lia. reflexivity. }
      rewrite E1 in HM1. rewrite E2 in HM2.
      eexists. apply exec_u128_shift64_body with (m1 := m1) (b := blk beta r);
        [reflexivity|reflexivity|exact HLoadH|exact HM1|exact HM2]. }
  destruct HCall as (le' & HExec).
  exists mf, Vundef. split.
  - cbn [map den]. fold (blk beta r) (bas beta r). rewrite HBase. cbn [Z.add].
    eapply eval_funcall_internal with (e := empty_env) (le1 := u128_shift_temps (blk beta r) n)
      (le2 := le') (m1 := m) (m2 := mf) (out := Out_normal).
    + apply u128_shift_entry.
    + exact HExec.
    + reflexivity.
    + reflexivity.
  - split; [exact HRep2|]. split; [exact I|]. split; [congruence|]. split; [reflexivity|].
    eapply lframe_trans.
    + eapply lframe_implies; [apply lframe_unchanged; exact HU1|].
      intros b o (_ & HF & _) _. exact HF.
    + rewrite HSh1 in HU2. eapply lframe_implies; [apply lframe_unchanged; exact HU2|].
      intros b o (_ & HF & _) _. exact HF.
Qed.
Print Assumptions exec_u128_shift52_body.
Print Assumptions orc_shr_ok.
