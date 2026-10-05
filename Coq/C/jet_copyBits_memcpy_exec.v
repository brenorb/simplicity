(** Execution of the actual [memcpy] branch of [copyBitsHelper] for counts up
    to one word.  The external call is a premise here; [jet_memcpy_model]
    discharges it from the explicit memcpy model. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_constants.
Require Import C.jet_copyBits_helper_exec C.jet_copyBits_loop_exec C.jet_memcpy_model.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 30.

Definition copy_mcpy_mset := match copy_memcpy_branch with Ssequence s _ => s | _ => Sskip end.
Definition copy_mcpy_call := match copy_memcpy_branch with Ssequence _ s => s | _ => Sskip end.
Definition copy_mcpy_m_expr := match copy_mcpy_mset with Sset _ e => e | _ => Econst_int Int.zero tint end.

Lemma copy_memcpy_branch_shape : copy_memcpy_branch =
  Ssequence (Sset _m copy_mcpy_m_expr) copy_mcpy_call.
Proof. reflexivity. Qed.

Lemma copy_mcpy_m_shape : copy_mcpy_m_expr =
  Ebinop Oadd (Ebinop Odiv (Etempvar _n tulong) generated_uword_bits tulong)
    (Eunop Onotbool (Eunop Onotbool (Ebinop Omod (Etempvar _n tulong) generated_uword_bits tulong) tint) tint)
    tulong.
Proof. reflexivity. Qed.

Lemma copy_mcpy_call_shape : copy_mcpy_call =
  Scall None (Evar _memcpy (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil)))
    (tptr tvoid) cc_default))
    [Ebinop Osub (Etempvar _dst_ptr (tptr tulong))
       (Ebinop Osub (Etempvar _m tulong) (Econst_int (Int.repr 1) tint) tulong) (tptr tulong);
     Ebinop Osub (Etempvar _src_ptr (tptr tulong))
       (Ebinop Osub (Etempvar _m tulong)
         (Ebinop Odiv (Etempvar _src_shift tulong) generated_uword_bits tulong) tulong) (tptr tulong);
     Ebinop Omul (Etempvar _m tulong) (Esizeof tulong tulong) tulong].
Proof. reflexivity. Qed.

Lemma eval_copy_mcpy_m le m n :
  1 <= n <= 64 -> le!_n = Some (Vlong (Int64.repr n)) ->
  eval_expr ge0 empty_env le m copy_mcpy_m_expr (Vlong (Int64.repr 1)).
Proof.
  intros Hn HN. rewrite copy_mcpy_m_shape.
  assert (Hr : forall z, 0 <= z <= 64 -> 0 <= z <= Int64.max_unsigned)
    by (intros z Hz; change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (Z.eq_dec n 64) as [->|Hn64].
  - eapply eval_Ebinop with (v1 := Vlong (Int64.repr 1)) (v2 := Vint Int.zero).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr 64)) (v2 := Vlong (Int64.repr 64));
        [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
      vm_compute. reflexivity.
    + eapply eval_Eunop with (v1 := Vint Int.one).
      * eapply eval_Eunop with (v1 := Vlong Int64.zero).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 64)) (v2 := Vlong (Int64.repr 64));
             [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
           vm_compute. reflexivity.
        -- vm_compute. reflexivity.
      * vm_compute. reflexivity.
    + vm_compute. reflexivity.
  - eapply eval_Ebinop with (v1 := Vlong Int64.zero) (v2 := Vint Int.one).
    + eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr 64));
        [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
      simpl. unfold sem_div, sem_binarith. simpl.
      assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity.
      assert (Int64.divu (Int64.repr n) (Int64.repr 64) = Int64.zero) as ->.
      { unfold Int64.divu. rewrite !Int64.unsigned_repr by (apply Hr; lia).
        rewrite Z.div_small by lia. reflexivity. }
      reflexivity.
    + eapply eval_Eunop with (v1 := Vint Int.zero).
      * eapply eval_Eunop with (v1 := Vlong (Int64.repr n)).
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr 64));
             [apply eval_Etempvar; exact HN|apply eval_generated_uword_bits|].
           simpl. unfold sem_mod, sem_binarith. simpl.
           assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity.
           assert (Int64.modu (Int64.repr n) (Int64.repr 64) = Int64.repr n) as ->.
           { unfold Int64.modu. rewrite !Int64.unsigned_repr by (apply Hr; lia).
             rewrite Z.mod_small by lia. reflexivity. }
           reflexivity.
        -- cbv beta iota delta [sem_unary_operation sem_notbool bool_val option_map typeof classify_bool]. rewrite (Int64.eq_false (Int64.repr n) Int64.zero) by
             (intro HE; apply (f_equal Int64.unsigned) in HE;
              rewrite Int64.unsigned_repr in HE by (apply Hr; lia); change (Int64.unsigned Int64.zero) with 0 in HE; lia).
           reflexivity.
      * reflexivity.
    + vm_compute. reflexivity.
Qed.

Lemma sem_sub_tulong_ptr b ofs k m :
  sem_sub ge0 (Vptr b ofs) (tptr tulong) (Vlong k) tulong m =
    Some (Vptr b (Ptrofs.sub ofs (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 k)))).
Proof. unfold sem_sub. simpl. reflexivity. Qed.

Definition copy_mcpy_env le := PTree.set _m (Vlong (Int64.repr 1)) le.

Lemma exec_copy_memcpy_branch le m m' bi src_ofs bw dst_ofs ss n :
  (ss = 0 \/ ss = 64) -> 1 <= n <= 64 ->
  le!_dst_ptr = Some (Vptr bw dst_ofs) -> le!_src_ptr = Some (Vptr bi src_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_n = Some (Vlong (Int64.repr n)) ->
  external_call (EF_external "memcpy" memcpy_sig) ge0
    [Vptr bw dst_ofs; Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (1 - ss / 64)))); Vlong (Int64.repr 8)]
    m E0 (Vptr bw dst_ofs) m' ->
  Clight2.exec_stmt ge0 empty_env le m copy_memcpy_branch E0 (copy_mcpy_env le) m' Out_normal.
Proof.
  intros Hss Hn HD HS HSS HN Hext.
  rewrite copy_memcpy_branch_shape.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := copy_mcpy_env le).
  - apply exec_set. eapply eval_copy_mcpy_m; eassumption.
  - assert (HM : (copy_mcpy_env le)!_m = Some (Vlong (Int64.repr 1))) by (unfold copy_mcpy_env; apply PTree.gss).
    assert (Hexec : Clight2.exec_stmt ge0 empty_env (copy_mcpy_env le) m copy_mcpy_call E0
      (set_opttemp None (Vptr bw dst_ofs) (copy_mcpy_env le)) m' Out_normal).
    2: exact Hexec.
    rewrite copy_mcpy_call_shape.
    eapply exec_Scall with (vf := Vptr block_memcpy Ptrofs.zero)
      (vargs := [Vptr bw dst_ofs; Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (1 - ss / 64))));
        Vlong (Int64.repr 8)]).
    + reflexivity.
    + eapply eval_Elvalue.
      * apply eval_Evar_global; [reflexivity|apply symbol_memcpy].
      * apply deref_loc_reference; reflexivity.
    + eapply eval_Econs with (v1 := Vptr bw dst_ofs).
      * eapply eval_Ebinop with (v1 := Vptr bw dst_ofs) (v2 := Vlong Int64.zero).
        -- apply eval_Etempvar. unfold copy_mcpy_env. rewrite PTree.gso by discriminate. exact HD.
        -- eapply eval_Ebinop with (v1 := Vlong (Int64.repr 1)) (v2 := Vint Int.one);
             [apply eval_Etempvar; exact HM|apply eval_Econst_int|vm_compute; reflexivity].
        -- simpl. rewrite sem_sub_tulong_ptr.
           change (Ptrofs.of_int64 Int64.zero) with Ptrofs.zero.
           rewrite Ptrofs.mul_zero, Ptrofs.sub_zero_l. reflexivity.
      * reflexivity.
      * eapply eval_Econs with (v1 := Vptr bi (Ptrofs.sub src_ofs (Ptrofs.repr (8 * (1 - ss / 64))))).
        -- eapply eval_Ebinop with (v1 := Vptr bi src_ofs)
             (v2 := Vlong (Int64.sub (Int64.repr 1) (Int64.divu (Int64.repr ss) (Int64.repr 64)))).
           ++ apply eval_Etempvar. unfold copy_mcpy_env. rewrite PTree.gso by discriminate. exact HS.
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr 1)) (v2 := Vlong (Int64.divu (Int64.repr ss) (Int64.repr 64))).
              ** apply eval_Etempvar; exact HM.
              ** eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr 64));
                   [apply eval_Etempvar; unfold copy_mcpy_env; rewrite PTree.gso by discriminate; exact HSS
                   |apply eval_generated_uword_bits|].
                 simpl. unfold sem_div, sem_binarith. simpl.
                 assert (Int64.eq (Int64.repr 64) Int64.zero = false) as -> by reflexivity. reflexivity.
              ** simpl. unfold sem_sub, sem_binarith. simpl. reflexivity.
           ++ simpl. rewrite sem_sub_tulong_ptr.
              assert (HK : Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64
                (Int64.sub (Int64.repr 1) (Int64.divu (Int64.repr ss) (Int64.repr 64)))) =
                Ptrofs.repr (8 * (1 - ss / 64))) by (destruct Hss as [-> | ->]; vm_compute; reflexivity).
              rewrite HK. reflexivity.
        -- reflexivity.
        -- eapply eval_Econs with (v1 := Vlong (Int64.repr 8)).
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr 1)) (v2 := Vlong (Int64.repr 8)).
              ** apply eval_Etempvar; exact HM.
              ** eapply eval_Esizeof.
              ** vm_compute. reflexivity.
           ++ reflexivity.
           ++ apply eval_Enil.
    + apply funct_memcpy.
    + reflexivity.
    + eapply eval_funcall_external. exact Hext.
Qed.
