(** Execution of [sha256_fromMidstate] and [sha256_hash] in the SHA
    translation unit: a 256-bit midstate is absorbed as its 32 big-endian
    bytes.  [sha256_hash] is conditional on the explicit [memcpy_model]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_compress_call C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_be32_exec C.jet_sha_uchars_prep C.jet_sha_uchars_loop C.jet_sha_uchars_exec.
Require Import C.jet_sha_be64_exec C.jet_sha_be32_write.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Lemma sha_fromMidstate_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_fromMidstate = Some (sha_symbol_block _sha256_fromMidstate).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_fromMidstate_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_fromMidstate) Ptrofs.zero) =
    Some (Internal f_sha256_fromMidstate).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_hash_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_hash = Some (sha_symbol_block _sha256_hash).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_hash_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero) =
    Some (Internal f_sha256_hash).
Proof. vm_compute; reflexivity. Qed.

Definition fm_temps : list ident := [_t'8; _t'7; _t'6; _t'5; _t'4; _t'3; _t'2; _t'1].
Definition fm_temp (i : nat) : ident := nth i fm_temps _t'1.

Definition fm_pair (i : nat) : statement :=
  Ssequence
    (Sset (fm_temp i) (Ederef (Ebinop Oadd (Etempvar _midstate (tptr tuint))
      (Econst_int (Int.repr (Z.of_nat i)) tint) (tptr tuint)) tuint))
    (Scall None (Evar _WriteBE32 (Tfunction (Tcons (tptr tuchar) (Tcons tulong Tnil)) tvoid cc_default))
      [Ebinop Oadd (Etempvar _hash (tptr tuchar))
         (Ebinop Omul (Econst_int (Int.repr (Z.of_nat i)) tint) (Econst_int (Int.repr 4) tint) tint) (tptr tuchar);
       Etempvar (fm_temp i) tuint]).

Fixpoint fm_seq (i n : nat) : statement :=
  match n with
  | O => fm_pair i
  | S n' => Ssequence (fm_pair i) (fm_seq (S i) n')
  end.

Lemma fromMidstate_body : fn_body f_sha256_fromMidstate = fm_seq 0 7.
Proof. reflexivity. Qed.

Local Opaque sha_ge.

Lemma fm_temp_fresh i : (i < 8)%nat -> fm_temp i <> _midstate /\ fm_temp i <> _hash.
Proof. intros Hi. do 8 (destruct i as [|i]; [split; discriminate|]). lia. Qed.

Lemma ptr_word_index (o : ptrofs) (i : Z) : 0 <= i <= 1000 ->
  Ptrofs.unsigned o + 4 * i <= Ptrofs.max_unsigned ->
  Ptrofs.unsigned (Ptrofs.add o (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr i)))) =
    Ptrofs.unsigned o + 4 * i.
Proof.
  intros Hi HM. pose proof (Ptrofs.unsigned_range o) as HO.
  assert (HMU : Ptrofs.max_unsigned = 18446744073709551615) by reflexivity.
  assert (HI : Ptrofs.of_ints (Int.repr i) = Ptrofs.repr i).
  { unfold Ptrofs.of_ints. rewrite Int.signed_repr; [reflexivity|].
    change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia. }
  rewrite HI. unfold Ptrofs.mul. rewrite (Ptrofs.unsigned_repr 4), (Ptrofs.unsigned_repr i) by lia.
  unfold Ptrofs.add. rewrite (Ptrofs.unsigned_repr (4 * i)) by lia.
  apply Ptrofs.unsigned_repr. lia.
Qed.

Section FromMidstate.
Variables (bh bmid : block) (oh omid : ptrofs) (regs : list int).
Hypothesis Hne : bh <> bmid.
Hypothesis HohM : Ptrofs.unsigned oh + 32 <= Ptrofs.max_unsigned.
Hypothesis HomM : Ptrofs.unsigned omid + 32 <= Ptrofs.max_unsigned.

Definition fm_ok (m : mem) : Prop :=
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bmid (Ptrofs.unsigned omid + 4 * Z.of_nat j) = Some (Vint (nth j regs Int.zero))) /\
  Mem.range_perm m bh (Ptrofs.unsigned oh) (Ptrofs.unsigned oh + 32) Cur Writable.

Definition fm_word (j : nat) : list int := c_be32_bytes (Int64.repr (Int.unsigned (nth j regs Int.zero))).

Lemma fm_pair_exec i le m :
  (i < 8)%nat -> fm_ok m ->
  le!_midstate = Some (Vptr bmid omid) -> le!_hash = Some (Vptr bh oh) ->
  exists m',
    Clight2.exec_stmt sha_ge empty_env le m (fm_pair i) E0
      (PTree.set (fm_temp i) (Vint (nth i regs Int.zero)) le) m' Out_normal /\
    (forall q, (q < 4)%nat ->
       Mem.load Mint8unsigned m' bh (Ptrofs.unsigned oh + 4 * Z.of_nat i + Z.of_nat q) =
         Some (Vint (nth q (fm_word i) Int.zero))) /\
    (forall ch b ofs,
       (b <> bh \/ ofs + size_chunk ch <= Ptrofs.unsigned oh + 4 * Z.of_nat i \/
        Ptrofs.unsigned oh + 4 * Z.of_nat i + 4 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hi [HR HP] Hmid Hhash.
  destruct (fm_temp_fresh i Hi) as [N1 N2].
  set (w := nth i regs Int.zero).
  set (le1 := PTree.set (fm_temp i) (Vint w) le).
  set (op := Ptrofs.add oh (Ptrofs.mul (Ptrofs.repr 1)
    (Ptrofs.of_ints (Int.repr (4 * Z.of_nat i))))).
  assert (Hop : Ptrofs.unsigned op = Ptrofs.unsigned oh + 4 * Z.of_nat i) by (apply ptr_byte_offset; lia).
  destruct (eval_sha_WriteBE32 m bh op (Int64.repr (Int.unsigned w)) ltac:(rewrite Hop; lia))
    as (m' & HW & HB & HF & HPm & HV).
  { intros ofs Ho. apply HP. rewrite Hop in Ho. lia. }
  exists m'. split; [|split; [|split; [|split; [exact HPm|exact HV]]]].
  - unfold fm_pair. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
    + apply exec_Sset. eapply eval_Elvalue.
      * eapply eval_Ederef. eapply eval_Ebinop; [apply eval_Etempvar; exact Hmid|apply eval_Econst_int|reflexivity].
      * eapply deref_loc_value; [reflexivity|]. unfold Mem.loadv.
        rewrite ptr_word_index by lia. apply HR. exact Hi.
    + change le1 with (set_opttemp None Vundef le1) at 2.
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _WriteBE32) Ptrofs.zero)
        (vargs := [Vptr bh op; Vlong (Int64.repr (Int.unsigned w))]) (f := Internal f_WriteBE32).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_WriteBE32_symbol]|].
        apply deref_loc_reference; reflexivity.
      * assert (HMul : Int.mul (Int.repr (Z.of_nat i)) (Int.repr 4) = Int.repr (4 * Z.of_nat i)).
        { unfold Int.mul. rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
          f_equal. lia. }
        eapply eval_Econs.
        -- eapply eval_Ebinop; [apply eval_Etempvar; unfold le1; rewrite PTree.gso by auto; exact Hhash| |].
           ++ eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Econst_int|reflexivity].
           ++ cbn. rewrite HMul. reflexivity.
        -- reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
      * exact sha_WriteBE32_funct.
      * reflexivity.
      * exact HW.
  - intros q Hq. rewrite <- Hop. apply HB. exact Hq.
  - intros ch b ofs Hc. apply HF. rewrite Hop. exact Hc.
Qed.

Lemma fm_seq_exec n : forall i le m,
  (i + n = 7)%nat -> fm_ok m ->
  le!_midstate = Some (Vptr bmid omid) -> le!_hash = Some (Vptr bh oh) ->
  exists le' m',
    Clight2.exec_stmt sha_ge empty_env le m (fm_seq i n) E0 le' m' Out_normal /\
    (forall j q, (i <= j < 8)%nat -> (q < 4)%nat ->
       Mem.load Mint8unsigned m' bh (Ptrofs.unsigned oh + 4 * Z.of_nat j + Z.of_nat q) =
         Some (Vint (nth q (fm_word j) Int.zero))) /\
    (forall ch b ofs,
       (b <> bh \/ ofs + size_chunk ch <= Ptrofs.unsigned oh + 4 * Z.of_nat i \/
        Ptrofs.unsigned oh + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  induction n as [|n IH]; intros i le m Hin Hok Hmid Hhash.
  - destruct (fm_pair_exec i le m ltac:(lia) Hok Hmid Hhash) as (m' & HE & HB & HF & HP & HV).
    exists (PTree.set (fm_temp i) (Vint (nth i regs Int.zero)) le), m'.
    split; [exact HE|]. split.
    { intros j q Hj Hq. assert (j = i) by lia. subst j. apply HB. exact Hq. }
    split; [|split; [exact HP|exact HV]].
    intros ch b ofs Hc. apply HF. destruct Hc as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; lia].
  - destruct (fm_pair_exec i le m ltac:(lia) Hok Hmid Hhash) as (m1 & HE & HB & HF & HP & HV).
    destruct (fm_temp_fresh i ltac:(lia)) as [N1 N2].
    assert (Hok1 : fm_ok m1).
    { destruct Hok as [HR HPm]. split.
      - intros j Hj. rewrite HF by (left; auto). apply HR. exact Hj.
      - intros ofs Ho. apply HP, HPm, Ho. }
    destruct (IH (S i) (PTree.set (fm_temp i) (Vint (nth i regs Int.zero)) le) m1 ltac:(lia) Hok1
      ltac:(rewrite PTree.gso by auto; exact Hmid) ltac:(rewrite PTree.gso by auto; exact Hhash))
      as (le' & m' & HE' & HB' & HF' & HP' & HV').
    exists le', m'. split; [cbn [fm_seq]; eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HE|exact HE']|].
    split.
    { intros j q Hj Hq. destruct (Nat.eq_dec j i) as [->|Hne'].
      - rewrite HF' by (right; left; change (size_chunk Mint8unsigned) with 1; lia). apply HB. exact Hq.
      - apply HB'; [lia|exact Hq]. }
    split; [|split; [intros b ofs k p Hp; apply HP', HP, Hp|intros b Hv; apply HV', HV, Hv]].
    intros ch b ofs Hc. rewrite HF' by (destruct Hc as [H|[H|H]]; [left; exact H|right; left; lia|right; right; exact H]).
    apply HF. destruct Hc as [H|[H|H]]; [left; exact H|right; left; exact H|right; right; lia].
Qed.
End FromMidstate.

Definition fm_le (bh : block) (oh : ptrofs) (bmid : block) (omid : ptrofs) : temp_env :=
  PTree.set _midstate (Vptr bmid omid) (PTree.set _hash (Vptr bh oh)
    (create_undef_temps (fn_temps f_sha256_fromMidstate))).

Theorem eval_sha_fromMidstate m bh oh bmid omid (regs : list int) :
  bh <> bmid -> length regs = 8%nat ->
  Ptrofs.unsigned oh + 32 <= Ptrofs.max_unsigned -> Ptrofs.unsigned omid + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bmid (Ptrofs.unsigned omid + 4 * Z.of_nat j) = Some (Vint (nth j regs Int.zero))) ->
  Mem.range_perm m bh (Ptrofs.unsigned oh) (Ptrofs.unsigned oh + 32) Cur Writable ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_fromMidstate) [Vptr bh oh; Vptr bmid omid] E0 m' Vundef /\
    (forall k, (k < 32)%nat ->
       Mem.load Mint8unsigned m' bh (Ptrofs.unsigned oh + Z.of_nat k) = Some (Vint (nth k (be_bytes regs) Int.zero))) /\
    (forall ch b ofs,
       (b <> bh \/ ofs + size_chunk ch <= Ptrofs.unsigned oh \/ Ptrofs.unsigned oh + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hne Hlr HohM HomM HR HP.
  destruct (fm_seq_exec bh bmid oh omid regs Hne HohM HomM 7 0%nat (fm_le bh oh bmid omid) m
    eq_refl (conj HR HP) eq_refl eq_refl) as (le' & m' & HE & HB & HF & HPm & HV).
  exists m'. split; [|split; [|split; [|split; [exact HPm|exact HV]]]].
  - eapply eval_funcall_internal with (e := empty_env) (le1 := fm_le bh oh bmid omid) (m1 := m)
      (le2 := le') (m2 := m') (out := Out_normal).
    + apply function_entry2_intro.
      * apply list_norepet_nil.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * intros x y HX HY Hxy. cbn in HX, HY.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hxy; discriminate | congruence].
      * apply alloc_variables_nil.
      * reflexivity.
    + rewrite fromMidstate_body. exact HE.
    + cbn. reflexivity.
    + reflexivity.
  - intros k Hk.
    replace k with (4 * (k / 4) + k mod 4)%nat at 2 by (symmetry; apply Nat.div_mod_eq).
    assert (Hq : (k mod 4 < 4)%nat) by (apply Nat.mod_upper_bound; lia).
    assert (Hj : (k / 4 < 8)%nat) by (apply Nat.div_lt_upper_bound; lia).
    rewrite be_bytes_nth by (rewrite ?Hlr; assumption).
    replace (Ptrofs.unsigned oh + Z.of_nat k) with
      (Ptrofs.unsigned oh + 4 * Z.of_nat (k / 4) + Z.of_nat (k mod 4))
      by (pose proof (Nat.div_mod_eq k 4); lia).
    apply HB; [lia|exact Hq].
  - intros ch b ofs Hc. apply HF. rewrite Z.mul_0_r, Z.add_0_r. exact Hc.
Qed.

(** ** sha256_hash *)
Local Transparent sha_ge.
Definition hash_env (bb : block) : env := PTree.set _buf (bb, tarray tuchar 32) empty_env.
Definition hash_temps (bx : block) (cbase : Z) (bt : block) (ot : ptrofs) : temp_env :=
  PTree.set _h (Vptr bt ot) (PTree.set _ctx (Vptr bx (Ptrofs.repr cbase))
    (create_undef_temps (fn_temps f_sha256_hash))).
Lemma hash_blocks bb : blocks_of_env sha_ge (hash_env bb) = [(bb, 0, 32)].
Proof. vm_compute. reflexivity. Qed.
Lemma hash_entry m m1 bb bx cbase bt ot :
  Mem.alloc m 0 32 = (m1, bb) ->
  function_entry2 sha_ge f_sha256_hash [Vptr bx (Ptrofs.repr cbase); Vptr bt ot] m
    (hash_env bb) (hash_temps bx cbase bt ot) m1.
Proof.
  intros HA. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros a b HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bb).
    + change (Mem.alloc m 0 32 = (m1, bb)); exact HA.
    + constructor.
  - reflexivity.
Qed.
Lemma eval_midstate_s e le m bt ot :
  le!_h = Some (Vptr bt ot) ->
  eval_expr sha_ge e le m
    (Efield (Ederef (Etempvar _h (tptr (Tstruct _sha256_midstate noattr))) (Tstruct _sha256_midstate noattr))
      _s (tarray tuint 8))
    (Vptr bt (Ptrofs.add ot (Ptrofs.repr 0))).
Proof.
  intros Hh. eapply eval_Elvalue.
  - eapply eval_Efield_struct with (delta := 0).
    + eapply eval_Elvalue; [apply eval_Ederef; apply eval_Etempvar; exact Hh|apply deref_loc_copy; reflexivity].
    + reflexivity.
    + vm_compute; reflexivity.
    + vm_compute; reflexivity.
  - apply deref_loc_reference; reflexivity.
Qed.
Local Opaque sha_ge.

Theorem eval_sha256_hash (Hmodel : memcpy_model) m bx cbase bo obase bt ot
    (l regs regsH : list int) (c : int64) (ovf : bool) :
  0 <= cbase -> cbase + 88 <= Ptrofs.max_unsigned -> 0 <= obase -> obase + 32 <= Ptrofs.max_unsigned ->
  bo <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bx ->
  sha_symbol_block _simplicity_sha256_compression <> bo ->
  length regs = 8%nat -> length regsH = 8%nat ->
  Ptrofs.unsigned ot + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bt (Ptrofs.unsigned ot + 4 * Z.of_nat j) = Some (Vint (nth j regsH Int.zero))) ->
  Mem.load Mptr m bx cbase = Some (Vptr bo (Ptrofs.repr obase)) ->
  Mem.load Mint64 m bx (cbase + 8) = Some (Vlong c) ->
  Int64.unsigned c mod 64 = Z.of_nat (length l) ->
  Mem.load Mint8unsigned m bx (cbase + 80) = Some (Vint (bit_int ovf)) ->
  (forall i, (i < length l)%nat ->
     Mem.load Mint8unsigned m bx (cbase + 16 + Z.of_nat i) = Some (Vint (nth i l Int.zero))) ->
  (forall i, (i < 8)%nat ->
     Mem.load Mint32 m bo (obase + 4 * Z.of_nat i) = Some (Vint (nth i regs Int.zero)) /\
     Mem.valid_access m Mint32 bo (obase + 4 * Z.of_nat i) Writable) ->
  sha_dispatch_ok m ->
  Mem.load Mint64 m (sha_symbol_block _sha256_max_counter) 0 = Some (Vlong sha_max_counter) ->
  Mem.range_perm m bx (cbase + 8) (cbase + 81) Cur Writable -> (8 | cbase) ->
  let bs := be_bytes regsH in
  let ovf' := uc_overflow ovf c (Int64.repr 32) in
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_sha256_hash)
      [Vptr bx (Ptrofs.repr cbase); Vptr bt ot] E0 m' Vundef /\
    Mem.load Mptr m' bx cbase = Some (Vptr bo (Ptrofs.repr obase)) /\
    Mem.load Mint64 m' bx (cbase + 8) = Some (Vlong (Int64.add c (Int64.repr 32))) /\
    Mem.load Mint8unsigned m' bx (cbase + 80) = Some (Vint (bit_int ovf')) /\
    (forall i, (i < length (fst (absorb_i l regs bs)))%nat ->
       Mem.load Mint8unsigned m' bx (cbase + 16 + Z.of_nat i) =
         Some (Vint (nth i (fst (absorb_i l regs bs)) Int.zero))) /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bo (obase + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs bs)) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bx \/ ofs + size_chunk ch <= cbase + 8 \/ cbase + 81 <= ofs) ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Hcb HcM Hob HoM Hox Hgx Hgo Hr HrH HotM HH HOut HCnt HMod HOvf HBlk HRegs Hdisp HMax HPerm HAl bs ovf'.
  assert (Hlbs : length bs = 32%nat) by (unfold bs; rewrite be_bytes_length, HrH; reflexivity).
  destruct (Mem.alloc m 0 32) as [m1 bb] eqn:A1.
  pose proof (mext_alloc _ _ _ _ _ A1) as (XV & XL & XP & XA).
  assert (Fb : forall b0, Mem.valid_block m b0 -> b0 <> bb).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hv). }
  assert (Vx : Mem.valid_block m bx) by (eapply jet_bitmachine_rep.load_valid_block; exact HOut).
  assert (Vo : Mem.valid_block m bo).
  { destruct (HRegs 0%nat ltac:(lia)) as [HL0 _]. eapply jet_bitmachine_rep.load_valid_block; exact HL0. }
  assert (Vt : Mem.valid_block m bt) by (eapply jet_bitmachine_rep.load_valid_block; exact (HH 0%nat ltac:(lia))).
  assert (VG : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression))
    by (eapply jet_bitmachine_rep.load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m (sha_symbol_block _sha256_max_counter))
    by (eapply jet_bitmachine_rep.load_valid_block; exact HMax).
  assert (PB1 : Mem.range_perm m1 bb 0 32 Cur Freeable).
  { intros ofs Hr0. eapply Mem.perm_alloc_2; eauto. }
  set (omid := Ptrofs.add ot (Ptrofs.repr 0)).
  assert (Homid : Ptrofs.unsigned omid = Ptrofs.unsigned ot) by (unfold omid; rewrite Ptrofs.add_zero; reflexivity).
  destruct (eval_sha_fromMidstate m1 bb Ptrofs.zero bt omid regsH (not_eq_sym (Fb bt Vt)) HrH
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(rewrite Homid; exact HotM))
    as (m2 & HW & HB2 & HF2 & HP2 & HV2).
  { intros j Hj. rewrite Homid. rewrite XL by exact Vt. apply HH. exact Hj. }
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. intros ofs Hr0.
    eapply Mem.perm_implies with (p1 := Freeable); [apply PB1; lia|constructor]. }
  change (Ptrofs.unsigned Ptrofs.zero) with 0 in HB2, HF2.
  assert (K2 : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch m2 b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. rewrite HF2 by (left; apply Fb; exact Hv). apply XL. exact Hv. }
  pose proof (eval_sha256_uchars Hmodel m2 bx cbase bo obase bb Ptrofs.zero l regs bs c ovf
    Hcb HcM Hob HoM Hox (not_eq_sym (Fb bx Vx)) (not_eq_sym (Fb bo Vo)) Hgx Hgo) as HU.
  cbv zeta in HU.
  destruct HU as (m3 & HUc & HOut3 & HCnt3 & HOvf3 & HBlk3 & HReg3 & HMem3 & HPerm3 & HVal3).
  { change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Hlbs.
    change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { exact Hr. }
  { rewrite K2 by exact Vx. exact HOut. }
  { rewrite K2 by exact Vx. exact HCnt. }
  { exact HMod. }
  { rewrite K2 by exact Vx. exact HOvf. }
  { intros i Hi. rewrite K2 by exact Vx. apply HBlk. exact Hi. }
  { intros i Hi. destruct (HRegs i Hi) as [HL0 [Pr Al]]. split.
    - rewrite K2 by exact Vo. exact HL0.
    - split; [|exact Al]. intros ofs Hr0. apply HP2, XP, Pr, Hr0. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. apply HB2. rewrite <- Hlbs. exact Hi. }
  { unfold sha_dispatch_ok. rewrite K2 by exact VG. exact Hdisp. }
  { rewrite K2 by exact VM. exact HMax. }
  { intros ofs Hr0. apply HP2, XP, HPerm, Hr0. }
  { exact HAl. }
  rewrite Hlbs in HUc, HCnt3, HOvf3. change (Z.of_nat 32) with 32 in HUc, HCnt3, HOvf3.
  fold ovf' in HUc, HOvf3.
  assert (Vb2 : Mem.valid_block m2 bb) by (apply HV2; eapply Mem.valid_new_block; exact A1).
  destruct (free_list_blocks [(bb, 0, 32)] m3) as (mf & HFL & HLf & HPf & HVf).
  { intros b0 lo hi [Heq|[]]. injection Heq as <- <- <-. intros ofs Hr0.
    apply HPerm3; [exact Vb2|]. apply HP2, PB1, Hr0. }
  { repeat constructor; cbn; tauto. }
  cbn [map fst] in HLf, HPf.
  assert (HNb : forall b0, Mem.valid_block m b0 -> ~ In b0 [bb]).
  { intros b0 Hv [Heq|[]]. exact (Fb b0 Hv (eq_sym Heq)). }
  assert (V2 : forall b0, Mem.valid_block m b0 -> Mem.valid_block m2 b0).
  { intros b0 Hv. apply HV2, XV, Hv. }
  set (le0 := hash_temps bx cbase bt ot).
  exists mf. split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
  - eapply eval_funcall_internal with (e := hash_env bb) (le1 := le0) (m1 := m1)
      (le2 := le0) (m2 := m3) (out := Out_normal).
    + apply hash_entry; exact A1.
    + cbn [f_sha256_hash fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := m2).
      { change le0 with (set_opttemp None Vundef le0) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_fromMidstate) Ptrofs.zero)
          (vargs := [Vptr bb Ptrofs.zero; Vptr bt omid]) (f := Internal f_sha256_fromMidstate).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_fromMidstate_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs.
          + eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
          + reflexivity.
          + eapply eval_Econs; [apply eval_midstate_s; reflexivity|reflexivity|apply eval_Enil].
        - exact sha_fromMidstate_funct.
        - reflexivity.
        - exact HW. }
      change le0 with (set_opttemp None (Vint (bit_int (negb ovf'))) le0) at 2.
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
        (vargs := [Vptr bx (Ptrofs.repr cbase); Vptr bb Ptrofs.zero; Vlong (Int64.repr 32)])
        (f := Internal f_sha256_uchars).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchars_symbol]|].
        apply deref_loc_reference; reflexivity.
      * eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
        eapply eval_Econs.
        -- eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity].
        -- reflexivity.
        -- eapply eval_Econs; [apply eval_Esizeof|reflexivity|apply eval_Enil].
      * exact sha_uchars_funct.
      * reflexivity.
      * exact HUc.
    + cbn. reflexivity.
    + rewrite hash_blocks. exact HFL.
  - rewrite HLf by (apply HNb; exact Vx). exact HOut3.
  - rewrite HLf by (apply HNb; exact Vx). exact HCnt3.
  - rewrite HLf by (apply HNb; exact Vx). exact HOvf3.
  - intros i Hi. rewrite HLf by (apply HNb; exact Vx). apply HBlk3. exact Hi.
  - intros i Hi. rewrite HLf by (apply HNb; exact Vo). apply HReg3. exact Hi.
  - intros ch b0 ofs Hv Hc1 Hc2. rewrite HLf by (apply HNb; exact Hv).
    rewrite HMem3; [apply K2; exact Hv|apply V2; exact Hv|exact Hc1|exact Hc2].
  - intros b0 ofs k p Hv Hp. apply HPf; [apply HNb; exact Hv|].
    apply HPerm3; [apply V2; exact Hv|]. apply HP2, XP, Hp.
  - intros b0 Hv. apply HVf, HVal3, V2, Hv.
Qed.
