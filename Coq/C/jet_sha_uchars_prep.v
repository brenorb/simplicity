(** Preparation for [sha256_uchars]: the chunked form of the byte-absorbing
    model on machine bytes, the byte-level effect of the modelled [memcpy],
    and the [sha256_context] field accesses in the SHA translation unit. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word.
Require Import C.jet_exec C.jet_memcpy_model C.jet_read8s_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_ctx8_model.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

(** ** Absorbing machine bytes *)
Definition absorb_step_i (st : list int * list int) (x : int) : list int * list int :=
  let l' := fst st ++ [x] in
  if Nat.eqb (length l') 64
  then ([], SHA256.hash_block (snd st) (be_words l'))
  else (l', snd st).

Definition absorb_i (l regs bs : list int) : list int * list int :=
  fold_left absorb_step_i bs (l, regs).

Lemma absorb_i_map l regs bs :
  absorb_i (map word8_array_value l) regs (map word8_array_value bs) =
    (map word8_array_value (fst (absorb l regs bs)), snd (absorb l regs bs)).
Proof.
  revert l regs. induction bs as [|x bs IH]; intros l regs; [reflexivity|].
  unfold absorb_i, absorb in *. cbn [map fold_left].
  unfold absorb_step_i at 2, absorb_step at 2 4. cbn [fst snd].
  replace (map word8_array_value l ++ [word8_array_value x]) with (map word8_array_value (l ++ [x]))
    by (rewrite map_app; reflexivity).
  rewrite map_length.
  destruct (Nat.eqb (length (l ++ [x])) 64).
  - exact (IH [] _).
  - exact (IH (l ++ [x]) regs).
Qed.

Lemma absorb_i_app l regs b1 b2 :
  absorb_i l regs (b1 ++ b2) = absorb_i (fst (absorb_i l regs b1)) (snd (absorb_i l regs b1)) b2.
Proof.
  unfold absorb_i. rewrite fold_left_app.
  destruct (fold_left absorb_step_i b1 (l, regs)); reflexivity.
Qed.

Lemma absorb_i_small bs : forall l regs, (length l + length bs < 64)%nat ->
  absorb_i l regs bs = (l ++ bs, regs).
Proof.
  induction bs as [|x bs IH]; intros l regs HL.
  - unfold absorb_i. cbn. rewrite app_nil_r. reflexivity.
  - unfold absorb_i in *. cbn [fold_left]. unfold absorb_step_i at 2. cbn [fst snd].
    cbn [length] in HL.
    assert (HE : Nat.eqb (length (l ++ [x])) 64 = false)
      by (apply Nat.eqb_neq; rewrite app_length; cbn [length]; lia).
    rewrite HE, IH by (rewrite app_length; cbn [length]; lia).
    rewrite <- app_assoc. reflexivity.
Qed.

Lemma absorb_i_fill l regs b1 : (length l + length b1 = 64)%nat -> b1 <> [] ->
  absorb_i l regs b1 = ([], SHA256.hash_block regs (be_words (l ++ b1))).
Proof.
  intros HL Hne. destruct (exists_last Hne) as (b0 & x & ->).
  rewrite app_length in HL. cbn [length] in HL.
  rewrite absorb_i_app, (absorb_i_small b0 l regs) by lia. cbn [fst snd].
  unfold absorb_i. cbn [fold_left]. unfold absorb_step_i. cbn [fst snd].
  assert (HE : Nat.eqb (length ((l ++ b0) ++ [x])) 64 = true)
    by (apply Nat.eqb_eq; rewrite !app_length; cbn [length]; lia).
  rewrite HE, <- app_assoc. reflexivity.
Qed.

(** ** Byte-level effect of memcpy *)
Lemma loadbytes_byte m b ofs n bytes i :
  Mem.loadbytes m b ofs n = Some bytes -> 0 <= i < n ->
  Mem.loadbytes m b (ofs + i) 1 = Some [nth (Z.to_nat i) bytes Undef].
Proof.
  intros HL Hi.
  replace n with (i + (n - i)) in HL by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ HL ltac:(lia) ltac:(lia)) as (b1 & b2 & H1 & H2 & ->).
  replace (n - i) with (1 + (n - i - 1)) in H2 by lia.
  destruct (Mem.loadbytes_split _ _ _ _ _ _ H2 ltac:(lia) ltac:(lia)) as (b3 & b4 & H3 & H4 & ->).
  pose proof (Mem.loadbytes_length _ _ _ _ _ H1) as L1.
  pose proof (Mem.loadbytes_length _ _ _ _ _ H3) as L3.
  rewrite H3. f_equal.
  destruct b3 as [|mv [|? ?]]; cbn [length] in L3; try (change (Z.to_nat 1) with 1%nat in L3; lia).
  rewrite app_nth2 by lia. rewrite L1, Nat.sub_diag. reflexivity.
Qed.

Lemma memcpy_bytes_effect (Hmodel : memcpy_model) (ge : Senv.t) m bs os bd od (xs : list int) :
  let n := Z.of_nat (length xs) in
  0 < n -> Ptrofs.unsigned os + n <= Ptrofs.max_unsigned -> Ptrofs.unsigned od + n <= Ptrofs.max_unsigned ->
  (forall i, (i < length xs)%nat ->
     Mem.load Mint8unsigned m bs (Ptrofs.unsigned os + Z.of_nat i) = Some (Vint (nth i xs Int.zero))) ->
  Mem.range_perm m bd (Ptrofs.unsigned od) (Ptrofs.unsigned od + n) Cur Writable ->
  bs <> bd ->
  exists m',
    external_call (EF_external "memcpy" memcpy_sig) ge
      [Vptr bd od; Vptr bs os; Vlong (Int64.repr n)] m E0 (Vptr bd od) m' /\
    (forall i, (i < length xs)%nat ->
       Mem.load Mint8unsigned m' bd (Ptrofs.unsigned od + Z.of_nat i) = Some (Vint (nth i xs Int.zero))) /\
    (forall ch b ofs,
       (b <> bd \/ ofs + size_chunk ch <= Ptrofs.unsigned od \/ Ptrofs.unsigned od + n <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros n Hn Hos Hod HL HP Hne.
  assert (HR : Mem.range_perm m bs (Ptrofs.unsigned os) (Ptrofs.unsigned os + n) Cur Readable).
  { intros ofs Ho. pose proof (HL (Z.to_nat (ofs - Ptrofs.unsigned os)) ltac:(unfold n in Ho; lia)) as H.
    apply Mem.load_valid_access in H. destruct H as [H _].
    apply H. change (size_chunk Mint8unsigned) with 1. lia. }
  destruct (Mem.range_perm_loadbytes m bs (Ptrofs.unsigned os) n HR) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as HBL.
  assert (HSrcValid : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. apply (HR (Ptrofs.unsigned os)). lia. }
  assert (HDstValid : Mem.valid_block m bd).
  { eapply Mem.perm_valid_block. apply (HP (Ptrofs.unsigned od)). lia. }
  destruct (Hmodel ge m bd od bs os n bytes HSrcValid HDstValid HB HP ltac:(left; exact Hne)
    ltac:(change Int64.max_unsigned with 18446744073709551615;
          change Ptrofs.max_unsigned with 18446744073709551615 in Hos;
          pose proof (Ptrofs.unsigned_range os); lia)
    ltac:(lia) ltac:(lia)) as (m' & HS & HX).
  exists m'. split; [exact HX|]. split; [|split; [|split]].
  - intros i Hi.
    pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as HSame.
    rewrite HBL, Z2Nat.id in HSame by lia.
    pose proof (loadbytes_byte _ _ _ _ _ (Z.of_nat i) HSame ltac:(unfold n; lia)) as HD.
    pose proof (loadbytes_byte _ _ _ _ _ (Z.of_nat i) HB ltac:(unfold n; lia)) as HSrc.
    apply (Mem.loadbytes_load Mint8unsigned) in HD; [|exists (Ptrofs.unsigned od + Z.of_nat i); cbn; lia].
    apply (Mem.loadbytes_load Mint8unsigned) in HSrc; [|exists (Ptrofs.unsigned os + Z.of_nat i); cbn; lia].
    rewrite HD. rewrite <- (HL i Hi). symmetry. exact HSrc.
  - intros ch b ofs Hcond. eapply Mem.load_storebytes_other; [exact HS|].
    rewrite HBL, Z2Nat.id by lia. destruct Hcond as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; exact H].
  - intros b ofs k p Hp. eapply Mem.perm_storebytes_1; eauto.
  - intros b Hv. eapply Mem.storebytes_valid_block_1; eauto.
Qed.

(** ** Linkage *)
Lemma sha_memcpy_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _memcpy = Some (sha_symbol_block _memcpy).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_memcpy_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _memcpy) Ptrofs.zero) =
    Some (External (EF_external "memcpy" memcpy_sig)
      (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_compression_uchar_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_compression_uchar =
    Some (sha_symbol_block _sha256_compression_uchar).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_compression_uchar_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_compression_uchar) Ptrofs.zero) =
    Some (Internal f_sha256_compression_uchar).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_max_counter_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_max_counter = Some (sha_symbol_block _sha256_max_counter).
Proof. vm_compute; reflexivity. Qed.

(** ** Context fields *)
Inductive ctx_slot := SOutput | SCounter | SBlock | SOverflow.
Definition ctx_field k := match k with
  | SOutput => _output | SCounter => _counter | SBlock => _block | SOverflow => _overflow end.
Definition ctx_offset k : Z := match k with
  | SOutput => 0 | SCounter => 8 | SBlock => 16 | SOverflow => 80 end.
Definition ctx_field_type k := match k with
  | SOutput => tptr tuint | SCounter => tulong | SBlock => tarray tuchar 64 | SOverflow => tbool end.
Definition ctx_field_expr k id := Efield
  (Ederef (Etempvar id (tptr (Tstruct _sha256_context noattr))) (Tstruct _sha256_context noattr))
  (ctx_field k) (ctx_field_type k).

Lemma ctx_address base k : 0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (ctx_offset k))) = base + ctx_offset k.
Proof.
  intros HB HM. assert (HD : 0 <= ctx_offset k <= 80) by (destruct k; cbn; lia).
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr base) by lia.
  rewrite (Ptrofs.unsigned_repr (ctx_offset k)) by lia.
  apply Ptrofs.unsigned_repr; lia.
Qed.

Lemma eval_ctx_field_lvalue k id e le m bc base :
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_lvalue sha_ge e le m (ctx_field_expr k id)
    bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (ctx_offset k))) Full.
Proof.
  intros HP. eapply eval_Efield_struct.
  - eapply eval_Elvalue.
    + apply eval_Ederef. apply eval_Etempvar; exact HP.
    + apply deref_loc_copy; reflexivity.
  - reflexivity.
  - vm_compute; reflexivity.
  - destruct k; vm_compute; reflexivity.
Qed.

Lemma eval_ctx_field k id e le m bc base chunk v :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  access_mode (ctx_field_type k) = By_value chunk ->
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  Mem.load chunk m bc (base + ctx_offset k) = Some v ->
  eval_expr sha_ge e le m (ctx_field_expr k id) v.
Proof.
  intros HB HM HK HP HL. eapply eval_Elvalue.
  - apply eval_ctx_field_lvalue; exact HP.
  - apply deref_loc_value with (chunk := chunk); [exact HK|].
    unfold Mem.loadv. rewrite ctx_address by assumption; exact HL.
Qed.

Lemma eval_ctx_block id e le m bc base :
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_expr sha_ge e le m (ctx_field_expr SBlock id)
    (Vptr bc (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 16))).
Proof.
  intros HP. eapply eval_Elvalue; [apply eval_ctx_field_lvalue; exact HP|].
  apply deref_loc_reference; reflexivity.
Qed.

Lemma exec_ctx_assign k id e le m m' bc base chunk a v v' :
  0 <= base -> base + 88 <= Ptrofs.max_unsigned ->
  access_mode (ctx_field_type k) = By_value chunk ->
  le!id = Some (Vptr bc (Ptrofs.repr base)) ->
  eval_expr sha_ge e le m a v ->
  sem_cast v (typeof a) (ctx_field_type k) m = Some v' ->
  Mem.store chunk m bc (base + ctx_offset k) v' = Some m' ->
  Clight2.exec_stmt sha_ge e le m (Sassign (ctx_field_expr k id) a) E0 le m' Out_normal.
Proof.
  intros HB HM HK HP HA HC HS.
  eapply exec_Sassign; [apply eval_ctx_field_lvalue; exact HP|exact HA|exact HC|].
  eapply assign_loc_value; [exact HK|]. unfold Mem.storev.
  rewrite ctx_address by assumption. exact HS.
Qed.
