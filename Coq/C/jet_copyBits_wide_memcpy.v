(** The plain [memcpy] branch of copyBitsHelper when two words are copied
    (remaining count between 65 and 128).  Conditional on the explicit
    [memcpy_model]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_word_bits C.jet_frame_constants.
Require Import C.jet_copyBits_exec C.jet_copyBits_helper_exec.
Require Import C.jet_copyBits_loop_exec C.jet_copyBits_loop_crossing.
Require Import C.jet_memcpy_model C.jet_copyBits_memcpy_exec C.jet_copyBits_memcpy_helper.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 60.

Lemma eval_copy_mcpy_m2 le m n :
  64 < n <= 128 -> le!_n = Some (Vlong (Int64.repr n)) ->
  eval_expr ge0 empty_env le m copy_mcpy_m_expr (Vlong (Int64.repr 2)).
Proof.
  intros Hn HN. rewrite copy_mcpy_m_shape.
  assert (Hr : forall z, 0 <= z <= 128 -> 0 <= z <= Int64.max_unsigned)
    by (intros z Hz; change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (Z.eq_dec n 128) as [->|Hn128].
  - eapply eval_Ebinop with (v1 := Vlong (Int64.repr 2)) (v2 := Vint Int.zero).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr 128)) (v2 := Vlong (Int64.repr 64));
        [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
      vm_compute. reflexivity.
    + eapply eval_Eunop with (v1 := Vint Int.one).
      * eapply eval_Eunop with (v1 := Vlong Int64.zero).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 128)) (v2 := Vlong (Int64.repr 64));
             [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
           vm_compute. reflexivity.
        -- vm_compute. reflexivity.
      * vm_compute. reflexivity.
    + vm_compute. reflexivity.
  - eapply eval_Ebinop with (v1 := Vlong (Int64.repr 1)) (v2 := Vint Int.one).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr 64));
        [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
      simpl. unfold sem_div, sem_binarith. simpl.
      assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity.
      assert (Int64.divu (Int64.repr n) (Int64.repr 64) = Int64.repr 1) as ->.
      { unfold Int64.divu. rewrite !Int64.unsigned_repr by (apply Hr; lia).
        assert (n / 64 = 1) as -> by (symmetry; apply (Z.div_unique n 64 1 (n - 64)); lia).
        reflexivity. }
      reflexivity.
    + eapply eval_Eunop with (v1 := Vint Int.zero).
      * eapply eval_Eunop with (v1 := Vlong (Int64.repr (n - 64))).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr 64));
             [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
           simpl. unfold sem_mod, sem_binarith. simpl.
           assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity.
           assert (Int64.modu (Int64.repr n) (Int64.repr 64) = Int64.repr (n - 64)) as ->.
           { unfold Int64.modu. rewrite !Int64.unsigned_repr by (apply Hr; lia).
             assert (n mod 64 = n - 64) as -> by (symmetry; apply (Z.mod_unique n 64 1 (n - 64)); lia).
             reflexivity. }
           reflexivity.
        -- cbv beta iota delta [sem_unary_operation sem_notbool bool_val option_map typeof classify_bool].
           rewrite (Int64.eq_false (Int64.repr (n - 64)) Int64.zero) by
             (intro HE; apply (f_equal Int64.unsigned) in HE;
              rewrite Int64.unsigned_repr in HE by (apply Hr; lia);
              change (Int64.unsigned Int64.zero) with 0 in HE; lia).
           reflexivity.
      * reflexivity.
    + vm_compute. reflexivity.
Qed.

Definition copy_mcpy_env2 le := PTree.set _m (Vlong (Int64.repr 2)) le.

Lemma exec_copy_memcpy_branch2 le m m' bi src_ofs bw dst_ofs ss n :
  (ss = 0 \/ ss = 64) -> 64 < n <= 128 ->
  le!_dst_ptr = Some (Vptr bw dst_ofs) -> le!_src_ptr = Some (Vptr bi src_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  external_call (EF_external "memcpy" memcpy_sig) ge0
    [Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8));
     Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (2 - ss / 64)))); Vlong (Int64.repr 16)]
    m E0 (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8))) m' ->
  Clight2.exec_stmt ge0 empty_env le m copy_memcpy_branch E0 (copy_mcpy_env2 le) m' Out_normal.
Proof.
  intros Hss Hn HD HS HSS HN Hext.
  rewrite copy_memcpy_branch_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := copy_mcpy_env2 le).
  - apply exec_set. eapply eval_copy_mcpy_m2; eassumption.
  - assert (HM : (copy_mcpy_env2 le)!_m = Some (Vlong (Int64.repr 2))) by (unfold copy_mcpy_env2; apply PTree.gss).
    assert (Hexec : Clight2.exec_stmt ge0 empty_env (copy_mcpy_env2 le) m copy_mcpy_call E0
      (set_opttemp None (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8))) (copy_mcpy_env2 le)) m' Out_normal).
    2: exact Hexec.
    rewrite copy_mcpy_call_shape.
    eapply exec_Scall with (vf := Vptr block_memcpy Ptrofs.zero)
      (vargs := [Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8));
        Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (2 - ss / 64)))); Vlong (Int64.repr 16)]).
    + reflexivity.
    + eapply eval_Elvalue.
      * apply eval_Evar_global; [reflexivity|apply symbol_memcpy].
      * apply deref_loc_reference; reflexivity.
    + eapply eval_Econs with (v1 := Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8))).
      * eapply eval_Ebinop with (v1 := Vptr bw dst_ofs) (v2 := Vlong Int64.one).
        -- apply eval_Etempvar. unfold copy_mcpy_env2. rewrite PTree.gso by discriminate. exact HD.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 2)) (v2 := Vint Int.one);
             [apply eval_Etempvar; exact HM|apply eval_Econst_int|vm_compute; reflexivity].
        -- simpl. rewrite sem_sub_tulong_ptr.
           assert (HK : Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 Int64.one) = Ptrofs.repr 8)
             by (vm_compute; reflexivity).
           rewrite HK. reflexivity.
      * reflexivity.
      * eapply eval_Econs with (v1 := Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (2 - ss / 64))))).
        -- eapply eval_Ebinop with (v1 := Vptr bi src_ofs)
             (v2 := Vlong (Int64.sub (Int64.repr 2) (Int64.divu (Int64.repr ss) (Int64.repr 64)))).
           ++ apply eval_Etempvar. unfold copy_mcpy_env2. rewrite PTree.gso by discriminate. exact HS.
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr 2)) (v2 := Vlong (Int64.divu (Int64.repr ss) (Int64.repr 64))).
              ** apply eval_Etempvar; exact HM.
              ** eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr 64));
                   [apply eval_Etempvar; unfold copy_mcpy_env2; rewrite PTree.gso by discriminate; exact HSS
                   |apply eval_generated_uword_bits|].
                 simpl. unfold sem_div, sem_binarith. simpl.
                 assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity. reflexivity.
              ** simpl. unfold sem_sub, sem_binarith. simpl. reflexivity.
           ++ simpl. rewrite sem_sub_tulong_ptr.
              assert (HK : Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64
                (Int64.sub (Int64.repr 2) (Int64.divu (Int64.repr ss) (Int64.repr 64)))) =
                Ptrofs.repr (8 * (2 - ss / 64))) by (destruct Hss as [-> | ->]; vm_compute; reflexivity).
              rewrite HK. reflexivity.
        -- reflexivity.
        -- eapply eval_Econs with (v1 := Vlong (Int64.repr 16)).
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr 2)) (v2 := Vlong (Int64.repr 8)).
              ** apply eval_Etempvar; exact HM.
              ** eapply eval_Esizeof.
              ** vm_compute. reflexivity.
           ++ reflexivity.
           ++ apply eval_Enil.
    + apply funct_memcpy.
    + reflexivity.
    + eapply eval_funcall_external. exact Hext.
Qed.

Lemma exec_copy_choice_memcpy2 le m m' bi src_ofs bw dst_ofs ss n :
  (ss = 0 \/ ss = 64) -> 64 < n <= 128 ->
  le!_dst_ptr = Some (Vptr bw dst_ofs) -> le!_src_ptr = Some (Vptr bi src_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  external_call (EF_external "memcpy" memcpy_sig) ge0
    [Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8));
     Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (2 - ss / 64)))); Vlong (Int64.repr 16)]
    m E0 (Vptr bw (Ptrofs.sub dst_ofs (Ptrofs.repr 8))) m' ->
  Clight2.exec_stmt ge0 empty_env le m copy_tail_after_partial E0 (copy_mcpy_env2 le) m' Out_normal.
Proof.
  intros Hss Hn HD HS HSS HN Hext.
  assert (Hmod : Int64.modu (Int64.repr ss) (Int64.repr 64) = Int64.zero).
  { destruct Hss as [-> | ->]; reflexivity. }
  rewrite copy_tail_choice_shape.
  eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
  - eapply eval_Ebinop with (v1 := Vint Int.zero) (v2 := Vlong Int64.zero).
    + apply eval_Econst_int.
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr 64));
        [apply eval_Etempvar; exact HSS|apply eval_generated_uword_bits|].
      simpl. unfold sem_mod, sem_binarith. simpl.
      assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity.
      rewrite Hmod. reflexivity.
    + vm_compute. reflexivity.
  - reflexivity.
  - eapply exec_copy_memcpy_branch2; eassumption.
Qed.

Lemma app_eq_length_inv {A} (a c b d : list A) :
  length a = length c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  revert c. induction a as [|x a IH]; intros [|y c] HL HE; simpl in *; try discriminate.
  - split; [reflexivity|exact HE].
  - injection HE as -> HE. injection HL as HL. destruct (IH c HL HE) as [-> ->]. split; reflexivity.
Qed.

(** Two adjacent 64-bit words copied by the modelled [memcpy]. *)
Lemma memcpy_two_words_effect (Hmodel : memcpy_model) m bi src bw dst v0 v1 :
  Mem.load Mint64 m bi src = Some (Vlong v0) -> Mem.load Mint64 m bi (src + 8) = Some (Vlong v1) ->
  Mem.valid_access m Mint64 bw dst Writable -> Mem.valid_access m Mint64 bw (dst + 8) Writable ->
  0 <= src -> src + 16 <= Ptrofs.max_unsigned -> 0 <= dst -> dst + 16 <= Ptrofs.max_unsigned ->
  (bi <> bw \/ src + 16 <= dst \/ dst + 16 <= src) ->
  exists m',
    external_call (EF_external "memcpy" memcpy_sig) ge0
      [Vptr bw (Ptrofs.repr dst); Vptr bi (Ptrofs.repr src); Vlong (Int64.repr 16)]
      m E0 (Vptr bw (Ptrofs.repr dst)) m' /\
    Mem.load Mint64 m' bw dst = Some (Vlong v0) /\
    Mem.load Mint64 m' bw (dst + 8) = Some (Vlong v1) /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= dst \/ dst + 16 <= ofs ->
      Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm m' b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HL0 HL1 [HW0 HAl0] [HW1 HAl1] Hs0 Hs1 Hd0 Hd1 Hsep.
  destruct (Mem.load_loadbytes _ _ _ _ _ HL0) as [bytes0 [HB0 Hdec0]].
  destruct (Mem.load_loadbytes _ _ _ _ _ HL1) as [bytes1 [HB1 Hdec1]].
  change (size_chunk Mint64) with 8 in HB0, HB1.
  assert (Hlen0 : length bytes0 = 8%nat) by (apply (Mem.loadbytes_length _ _ _ _ _ HB0)).
  assert (Hlen1 : length bytes1 = 8%nat) by (apply (Mem.loadbytes_length _ _ _ _ _ HB1)).
  assert (HB : Mem.loadbytes m bi src 16 = Some (bytes0 ++ bytes1)).
  { change 16 with (8 + 8). apply Mem.loadbytes_concat; [exact HB0|exact HB1|lia|lia]. }
  destruct (Hmodel ge0 m bw (Ptrofs.repr dst) bi (Ptrofs.repr src) 16 (bytes0 ++ bytes1)) as [m' [HS HE]].
  - rewrite !Ptrofs.unsigned_repr by lia. exact HB.
  - rewrite Ptrofs.unsigned_repr by lia. intros ofs Hofs.
    destruct (zlt ofs (dst + 8)); [apply HW0|apply HW1]; change (size_chunk Mint64) with 8; lia.
  - rewrite !Ptrofs.unsigned_repr by lia. lia.
  - change Int64.max_unsigned with 18446744073709551615; lia.
  - rewrite Ptrofs.unsigned_repr in HS by lia.
    exists m'. split; [exact HE|].
    assert (HLen : Z.of_nat (length (bytes0 ++ bytes1)) = 16).
    { rewrite app_length, Hlen0, Hlen1. reflexivity. }
    assert (HL' : Mem.loadbytes m' bw dst (8 + 8) = Some (bytes0 ++ bytes1)).
    { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HS) as Hsame.
      rewrite HLen in Hsame. exact Hsame. }
    destruct (Mem.loadbytes_split _ _ _ _ _ _ HL' ltac:(lia) ltac:(lia)) as (c0 & c1 & HC0 & HC1 & Hcat).
    assert (Hc0 : bytes0 = c0 /\ bytes1 = c1).
    { pose proof (Mem.loadbytes_length _ _ _ _ _ HC0) as HL0'.
      apply app_eq_length_inv in Hcat; [exact Hcat|].
      rewrite HL0', Hlen0. reflexivity. }
    destruct Hc0 as [<- <-].
    split.
    + rewrite (Mem.loadbytes_load Mint64 m' bw dst bytes0 HC0 HAl0). rewrite <- Hdec0. reflexivity.
    + split.
      * rewrite (Mem.loadbytes_load Mint64 m' bw (dst + 8) bytes1 HC1 HAl1). rewrite <- Hdec1. reflexivity.
      * split.
        -- intros chunk b ofs Hout. eapply Mem.load_storebytes_other; [exact HS|].
           rewrite HLen. destruct Hout as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
        -- split.
           ++ intros b ofs kind p HP. eapply Mem.perm_storebytes_1; eauto.
           ++ intros b HV. eapply Mem.storebytes_valid_block_1; eauto.
Qed.
