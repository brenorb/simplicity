(** The actual copyBitsHelper prefix, factored at generated statement boundaries.
    This file supplies INTERNAL execution lemmas; no jet coverage is claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_access C.jet_frame_constants.
Require Import C.jet_read8_layout C.jet_write_layout C.jet_copyBits_exec.
Require Import C.jet_LSBclear_width C.jet_LSBkeep_width C.jet_word_bits.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition copy_field id field ty :=
  Efield (Ederef (Etempvar id (tptr (Tstruct _frameItem noattr)))
    (Tstruct _frameItem noattr)) field ty.
Definition copy_src_init :=
  Ssequence (Sset _t'17 (copy_field _src _edge (tptr tulong)))
    (Ssequence (Sset _t'18 (copy_field _src _offset tulong))
      (Sset _src_ptr (Ebinop Osub
        (Ebinop Osub (Etempvar _t'17 (tptr tulong)) (Econst_int Int.one tint) (tptr tulong))
        (Ebinop Odiv (Etempvar _t'18 tulong) generated_uword_bits tulong) (tptr tulong)))).
Definition copy_dst_init :=
  Ssequence (Sset _t'15 (copy_field _dst _edge (tptr tulong)))
    (Ssequence (Sset _t'16 (copy_field _dst _offset tulong))
      (Sset _dst_ptr (Ebinop Oadd (Etempvar _t'15 (tptr tulong))
        (Ebinop Odiv (Ebinop Osub (Etempvar _t'16 tulong) (Econst_int Int.one tint) tulong)
          generated_uword_bits tulong) (tptr tulong)))).
Definition copy_src_shift_init :=
  Ssequence (Sset _t'14 (copy_field _src _offset tulong))
    (Sset _src_shift (Ebinop Osub generated_uword_bits
      (Ebinop Omod (Etempvar _t'14 tulong) generated_uword_bits tulong) tulong)).
Definition copy_dst_shift_init :=
  Ssequence (Sset _t'13 (copy_field _dst _offset tulong))
    (Sset _dst_shift (Ebinop Omod (Etempvar _t'13 tulong) generated_uword_bits tulong)).
Definition copy_helper_tail :=
  match f_copyBitsHelper.(fn_body) with
  | Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ tail))) => tail
  | _ => Sskip
  end.
Lemma copy_helper_body_prefix : f_copyBitsHelper.(fn_body) =
  Ssequence copy_src_init (Ssequence copy_dst_init
    (Ssequence copy_src_shift_init (Ssequence copy_dst_shift_init copy_helper_tail))).
Proof. reflexivity. Qed.

Lemma copy_eval_field_lvalue id field ty e le m bf base :
  le!id = Some (Vptr bf (Ptrofs.repr base)) ->
  (field = _edge /\ ty = tptr tulong) \/ (field = _offset /\ ty = tulong) ->
  eval_lvalue ge0 e le m (copy_field id field ty)
    bf (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr (if Pos.eqb field _edge then 0 else 8))) Full.
Proof.
  intros HP [[HF HT]|[HF HT]]; subst field ty;
    eapply eval_Efield_struct.
  all: try reflexivity.
  all: eapply eval_Elvalue;
    [eapply eval_Ederef; apply eval_Etempvar; exact HP|apply deref_loc_copy; reflexivity].
Qed.
Lemma copy_eval_edge id e le m bf base bw edge :
  frame_base_valid base -> le!id = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mptr m bf base = Some (Vptr bw (Ptrofs.repr edge)) ->
  eval_expr ge0 e le m (copy_field id _edge (tptr tulong)) (Vptr bw (Ptrofs.repr edge)).
Proof.
  intros HB HP HL. eapply eval_Elvalue.
  - eapply copy_eval_field_lvalue; [exact HP|left; auto].
  - apply deref_loc_value with (chunk := Mptr); [reflexivity|].
    unfold Mem.loadv. change (Mem.load Mptr m bf
      (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 0))) =
      Some (Vptr bw (Ptrofs.repr edge))).
    rewrite frame_field_address by (assumption || lia).
    replace (base + 0) with base by lia. exact HL.
Qed.
Lemma copy_eval_offset id e le m bf base cursor :
  frame_base_valid base -> le!id = Some (Vptr bf (Ptrofs.repr base)) ->
  Mem.load Mint64 m bf (base + 8) = Some (Vlong (Int64.repr cursor)) ->
  eval_expr ge0 e le m (copy_field id _offset tulong) (Vlong (Int64.repr cursor)).
Proof.
  intros HB HP HL. eapply eval_Elvalue.
  - eapply copy_eval_field_lvalue; [exact HP|right; auto].
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.loadv. change (Mem.load Mint64 m bf
      (Ptrofs.unsigned (Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8))) =
      Some (Vlong (Int64.repr cursor))).
    rewrite frame_field_address by (assumption || lia). exact HL.
Qed.
Lemma copy_eval_word id e le m bw ofs w :
  le!id = Some (Vptr bw ofs) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned ofs) = Some (Vlong w) ->
  eval_expr ge0 e le m (Ederef (Etempvar id (tptr tulong)) tulong) (Vlong w).
Proof.
  intros HP HW. eapply eval_Elvalue.
  - eapply eval_Ederef. apply eval_Etempvar; exact HP.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|exact HW].
Qed.

Definition copy_src_env le bi edge rc :=
  PTree.set _src_ptr (Vptr bi (Ptrofs.repr (edge - 8 * (1 + rc / 64))))
    (PTree.set _t'18 (Vlong (Int64.repr rc)) (PTree.set _t'17 (Vptr bi (Ptrofs.repr edge)) le)).
Definition copy_dst_env le bw outedge cursor :=
  PTree.set _dst_ptr (Vptr bw (Ptrofs.repr (write_word_address outedge cursor)))
    (PTree.set _t'16 (Vlong (Int64.repr cursor)) (PTree.set _t'15 (Vptr bw (Ptrofs.repr outedge)) le)).
Definition copy_src_shift_env le rc :=
  PTree.set _src_shift (Vlong (Int64.repr (64 - rc mod 64))) (PTree.set _t'14 (Vlong (Int64.repr rc)) le).
Definition copy_dst_shift_env le cursor :=
  PTree.set _dst_shift (Vlong (Int64.repr (cursor mod 64))) (PTree.set _t'13 (Vlong (Int64.repr cursor)) le).

Ltac copy_scalar :=
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shl Int64.shru Int64.or Int64.zero_ext Int.repr
    Z.sub Z.add Z.mul Z.div Z.modulo Ptrofs.repr Ptrofs.unsigned
    Ptrofs.add Ptrofs.sub Ptrofs.mul Ptrofs.of_int64];
  unfold sem_binarith, sem_cast;
  cbn -[Int64.repr Int64.unsigned Int64.sub Int64.add Int64.divu Int64.modu
    Int64.ltu Int64.shl Int64.shru Int64.or Int64.zero_ext Int.repr
    Z.sub Z.add Z.mul Z.div Z.modulo Ptrofs.repr Ptrofs.unsigned
    Ptrofs.add Ptrofs.sub Ptrofs.mul Ptrofs.of_int64];
  change (Int.signed Int.one) with 1;
  change (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_ints Int.one)) with (Ptrofs.repr 8);
  repeat match goal with H : ?lhs = ?rhs |- _ => progress rewrite H end;
  first [reflexivity|eassumption].

Ltac copy_temp :=
  apply eval_Etempvar;
  repeat first [rewrite PTree.gss|rewrite PTree.gso by discriminate];
  first [reflexivity|eassumption].
Ltac copy_expr :=
  first [solve [apply eval_generated_uword_bits]
    | solve [eapply copy_eval_edge; [eassumption|reflexivity|eassumption]]
    | solve [eapply copy_eval_offset; [eassumption|reflexivity|eassumption]]
    | solve [eapply copy_eval_word; [reflexivity|eassumption]]
    | copy_temp
    | eapply eval_Ecast; [copy_expr|copy_scalar]
    | eapply eval_Eunop; [copy_expr|copy_scalar]
    | eapply eval_Ebinop; [copy_expr|copy_expr|copy_scalar]
    | apply eval_Econst_int | apply eval_Econst_long].

Lemma exec_copy_src_init e le m bs sbase bi edge rc :
  frame_base_valid sbase -> le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  frame_fields_at m bs sbase bi edge rc ->
  0 <= rc <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  Clight2.exec_stmt ge0 e le m copy_src_init E0 (copy_src_env le bi edge rc) m Out_normal.
Proof.
  intros HB HP [HE HO] HR HEdge.
  assert (HQ : 0 <= rc / 64 <= Int64.max_unsigned).
  { split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia]. }
  destruct (read8_layout_pointer edge (rc / 64) HQ HEdge) as [HPfirst HPword].
  assert (Hdiv : Int64.divu (Int64.repr rc) (Int64.repr 64) = Int64.repr (rc / 64)).
  { unfold Int64.divu. rewrite Int64.unsigned_repr by lia. reflexivity. }
  unfold copy_src_init, copy_src_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'17 (Vptr bi (Ptrofs.repr edge)) le).
  - apply exec_set. eapply copy_eval_edge; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'18 (Vlong (Int64.repr rc)) (PTree.set _t'17 (Vptr bi (Ptrofs.repr edge)) le)).
    + apply exec_set. eapply copy_eval_offset; [exact HB| |exact HO].
      rewrite PTree.gso by discriminate. exact HP.
    + apply exec_set. copy_expr.
Qed.

Lemma exec_copy_dst_init e le m bd base bw edge cursor :
  frame_base_valid base -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  frame_fields_at m bd base bw edge cursor ->
  1 <= cursor <= Int64.max_unsigned -> 0 <= edge ->
  write_word_address edge cursor <= Ptrofs.max_unsigned ->
  Clight2.exec_stmt ge0 e le m copy_dst_init E0 (copy_dst_env le bw edge cursor) m Out_normal.
Proof.
  intros HB HP [HE HO] HC Hedge Haddr.
  destruct (write_layout_index cursor HC) as [HQ [_ [Hsub [Hdiv _]]]].
  assert (Hptr : Ptrofs.add (Ptrofs.repr edge)
      (Ptrofs.mul (Ptrofs.repr 8) (Ptrofs.of_int64 (Int64.repr ((cursor - 1) / 64)))) =
      Ptrofs.repr (write_word_address edge cursor)).
  { apply write_layout_pointer; [exact HQ|exact Hedge|exact Haddr]. }
  unfold copy_dst_init, copy_dst_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'15 (Vptr bw (Ptrofs.repr edge)) le).
  - apply exec_set. eapply copy_eval_edge; eauto.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'16 (Vlong (Int64.repr cursor)) (PTree.set _t'15 (Vptr bw (Ptrofs.repr edge)) le)).
    + apply exec_set. eapply copy_eval_offset; [exact HB| |exact HO].
      rewrite PTree.gso by discriminate. exact HP.
    + apply exec_set. copy_expr.
Qed.

Lemma exec_copy_src_shift_init e le m bs base bi edge rc :
  frame_base_valid base -> le!_src = Some (Vptr bs (Ptrofs.repr base)) ->
  frame_fields_at m bs base bi edge rc -> 0 <= rc <= Int64.max_unsigned ->
  Clight2.exec_stmt ge0 e le m copy_src_shift_init E0 (copy_src_shift_env le rc) m Out_normal.
Proof.
  intros HB HP [_ HO] HR.
  assert (Hmod : Int64.modu (Int64.repr rc) (Int64.repr 64) = Int64.repr (rc mod 64)).
  { unfold Int64.modu. rewrite Int64.unsigned_repr by lia. reflexivity. }
  assert (Hsub : Int64.sub (Int64.repr 64) (Int64.repr (rc mod 64)) =
      Int64.repr (64 - rc mod 64)).
  { unfold Int64.sub. change (Int64.unsigned (Int64.repr 64)) with 64.
    rewrite Int64.unsigned_repr; [reflexivity|].
    change (0 <= rc mod 64 <= 18446744073709551615).
    pose proof (Z.mod_pos_bound rc 64 ltac:(lia)); lia. }
  unfold copy_src_shift_init, copy_src_shift_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'14 (Vlong (Int64.repr rc)) le).
  - apply exec_set. eapply copy_eval_offset; eauto.
  - apply exec_set. copy_expr.
Qed.

Lemma exec_copy_dst_shift_init e le m bd base bw edge cursor :
  frame_base_valid base -> le!_dst = Some (Vptr bd (Ptrofs.repr base)) ->
  frame_fields_at m bd base bw edge cursor -> 0 <= cursor <= Int64.max_unsigned ->
  Clight2.exec_stmt ge0 e le m copy_dst_shift_init E0 (copy_dst_shift_env le cursor) m Out_normal.
Proof.
  intros HB HP [_ HO] HC.
  assert (Hmod : Int64.modu (Int64.repr cursor) (Int64.repr 64) = Int64.repr (cursor mod 64)).
  { unfold Int64.modu. rewrite Int64.unsigned_repr by lia. reflexivity. }
  unfold copy_dst_shift_init, copy_dst_shift_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'13 (Vlong (Int64.repr cursor)) le).
  - apply exec_set. eapply copy_eval_offset; eauto.
  - apply exec_set. copy_expr.
Qed.

Definition copy_helper_env bd base bs sbase n bi edge rc bw outedge cursor :=
  copy_dst_shift_env (copy_src_shift_env
    (copy_dst_env (copy_src_env
      (copy_frame_env f_copyBitsHelper bd (Ptrofs.repr base) bs (Ptrofs.repr sbase) n)
      bi edge rc) bw outedge cursor) rc) cursor.

Lemma copy_helper_entry m bd base bs sbase n :
  function_entry2 ge0 f_copyBitsHelper
    [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)]
    m empty_env (copy_frame_env f_copyBitsHelper bd (Ptrofs.repr base) bs (Ptrofs.repr sbase) n) m.
Proof.
  apply copy_frame_entry; [reflexivity|reflexivity|].
  intros i j HI HJ Heq; cbn in HI, HJ; subst j.
  repeat match goal with H : _ \/ _ |- _ => destruct H end;
    try contradiction; vm_compute in *; congruence.
Qed.

Lemma eval_copy_helper_prefix_composes m mf bd base bs sbase bi edge rc bw outedge cursor n le' out :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  Clight2.exec_stmt ge0 empty_env
    (copy_helper_env bd base bs sbase n bi edge rc bw outedge cursor) m copy_helper_tail E0 le' mf out ->
  (out = Out_normal \/ out = Out_return None) ->
  Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
    [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef.
Proof.
  intros HS HB HF HW HR HC HE HO HA Htail Hout.
  set (le := copy_frame_env f_copyBitsHelper bd (Ptrofs.repr base) bs (Ptrofs.repr sbase) n).
  eapply eval_funcall_internal with (e := empty_env) (le1 := le) (le2 := le')
    (m1 := m) (m2 := mf) (out := out).
  - apply copy_helper_entry.
  - rewrite copy_helper_body_prefix.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := copy_src_env le bi edge rc).
    + apply exec_copy_src_init with (bs := bs) (sbase := sbase); try assumption.
      unfold le, copy_frame_env. rewrite PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
        (le1 := copy_dst_env (copy_src_env le bi edge rc) bw outedge cursor).
      * apply exec_copy_dst_init with (bd := bd) (base := base); try assumption.
        unfold copy_src_env, le, copy_frame_env.
        rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
          (le1 := copy_src_shift_env (copy_dst_env (copy_src_env le bi edge rc) bw outedge cursor) rc).
        -- apply exec_copy_src_shift_init with (bs := bs) (base := sbase) (bi := bi) (edge := edge);
            try assumption.
           unfold copy_dst_env, copy_src_env, le, copy_frame_env.
           rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
            (le1 := copy_helper_env bd base bs sbase n bi edge rc bw outedge cursor).
           ++ apply exec_copy_dst_shift_init with (bd := bd) (base := base) (bw := bw) (edge := outedge);
                try assumption; [|lia].
              unfold copy_src_shift_env, copy_dst_env, copy_src_env, le, copy_frame_env.
              rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
           ++ exact Htail.
  - destruct Hout as [Hout|Hout]; subst out; reflexivity.
  - reflexivity.
Qed.

Definition copy_word id := Ederef (Etempvar id (tptr tulong)) tulong.
Definition copy_clear_stmt := Ssequence
  (Ssequence (Sset _t'12 (copy_word _dst_ptr))
    (Scall (Some _t'1) (Evar _LSBclear (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      [Etempvar _t'12 tulong; Etempvar _dst_shift tulong]))
  (Sassign (copy_word _dst_ptr) (Etempvar _t'1 tulong)).
Definition copy_left_fill := Ssequence
  (Ssequence (Sset _t'11 (copy_word _src_ptr))
    (Scall (Some _t'2) (Evar _LSBkeep (Tfunction (Tcons tulong (Tcons tulong Tnil)) tulong cc_default))
      [Etempvar _t'11 tulong; Etempvar _src_shift tulong]))
  (Ssequence (Sset _t'10 (copy_word _dst_ptr))
    (Sassign (copy_word _dst_ptr) (Ebinop Oor (Etempvar _t'10 tulong)
      (Ecast (Ebinop Oshl (Etempvar _t'2 tulong)
        (Ebinop Osub (Etempvar _dst_shift tulong) (Etempvar _src_shift tulong) tulong) tulong) tulong) tulong))).
Definition copy_partial :=
  match copy_helper_tail with Ssequence (Sifthenelse _ yes _) _ => yes | _ => Sskip end.
Definition copy_partial_left :=
  match copy_partial with Ssequence _ (Ssequence (Sifthenelse _ yes _) _) => yes | _ => Sskip end.
Definition copy_partial_right :=
  match copy_partial with Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition copy_left_after_return :=
  match copy_partial_left with Ssequence _ (Ssequence _ rest) => rest | _ => Sskip end.
Definition copy_tail_after_partial :=
  match copy_helper_tail with Ssequence _ rest => rest | _ => Sskip end.

Lemma copy_partial_shape : copy_partial = Ssequence copy_clear_stmt
  (Ssequence (Sifthenelse
    (Ebinop Olt (Etempvar _src_shift tulong) (Etempvar _dst_shift tulong) tint) copy_partial_left Sskip)
    copy_partial_right).
Proof. reflexivity. Qed.
Lemma copy_partial_left_shape : copy_partial_left = Ssequence copy_left_fill
  (Ssequence (Sifthenelse
    (Ebinop Ole (Etempvar _n tulong) (Etempvar _src_shift tulong) tint) (Sreturn None) Sskip)
    copy_left_after_return).
Proof. reflexivity. Qed.
Lemma copy_helper_tail_shape : copy_helper_tail =
  Ssequence (Sifthenelse (Etempvar _dst_shift tulong) copy_partial Sskip) copy_tail_after_partial.
Proof. reflexivity. Qed.

Definition copy_clear_env le ds old :=
  PTree.set _t'1 (Vlong (clear_low ds old)) (PTree.set _t'12 (Vlong old) le).
Definition copy_left_env le ss ds old source :=
  PTree.set _t'10 (Vlong (clear_low ds old))
    (PTree.set _t'2 (Vlong (Int64.zero_ext ss source)) (PTree.set _t'11 (Vlong source) le)).
Definition copy_left_value ss ds old source :=
  Int64.or (clear_low ds old)
    (Int64.shl (Int64.zero_ext ss source) (Int64.repr (ds - ss))).

Lemma exec_copy_clear le m mf bw ofs ds old :
  1 <= ds <= 64 -> le!_dst_ptr = Some (Vptr bw ofs) ->
  le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned ofs) (Vlong (clear_low ds old)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_clear_stmt E0 (copy_clear_env le ds old) mf Out_normal.
Proof.
  intros HD HP HS HW SF. unfold copy_clear_stmt, copy_clear_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'1 (Vlong (clear_low ds old)) (PTree.set _t'12 (Vlong old) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'12 (Vlong old) le).
    + apply exec_set. eapply copy_eval_word; [exact HP|exact HW].
    + eapply call_word_helper with (f := f_LSBclear) (n := Int64.repr ds).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply symbol_LSBclear.
      * apply funct_LSBclear.
      * copy_temp.
      * copy_temp.
      * apply eval_clear_width; exact HD.
  - eapply exec_Sassign_value with (v := Vlong (clear_low ds old)) (v2 := Vlong (clear_low ds old)).
    + eapply eval_Ederef. copy_temp.
    + copy_temp.
    + reflexivity.
    + apply assign_frame_word_at; exact SF.
Qed.

Lemma exec_copy_left_fill le m mf bi src_ofs bw dst_ofs ss ds old source :
  1 <= ss /\ ss < ds <= 63 ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  Mem.load Mint64 m bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong (clear_low ds old)) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_left_value ss ds old source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_left_fill E0 (copy_left_env le ss ds old source) mf Out_normal.
Proof.
  intros Hrange HP HD HS HDS Hsource Hdest SF.
  assert (Hsub : Int64.sub (Int64.repr ds) (Int64.repr ss) = Int64.repr (ds - ss)).
  { unfold Int64.sub. rewrite !Int64.unsigned_repr;
      [reflexivity|change (0 <= ss <= 18446744073709551615); lia|change (0 <= ds <= 18446744073709551615); lia]. }
  assert (Hshift : Int64.ltu (Int64.repr (ds - ss)) Int64.iwordsize = Datatypes.true).
  { unfold Int64.ltu. rewrite Int64.unsigned_repr by (change (0 <= ds - ss <= 18446744073709551615); lia).
    change ((if zlt (ds - ss) 64 then true else false) = true). rewrite zlt_true by lia; reflexivity. }
  unfold copy_left_fill, copy_left_env.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
    (le1 := PTree.set _t'2 (Vlong (Int64.zero_ext ss source)) (PTree.set _t'11 (Vlong source) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'11 (Vlong source) le).
    + apply exec_set. eapply copy_eval_word; [exact HP|exact Hsource].
    + eapply call_word_helper with (f := f_LSBkeep) (n := Int64.repr ss).
      * reflexivity.
      * reflexivity.
      * reflexivity.
      * apply symbol_LSBkeep.
      * apply funct_LSBkeep.
      * copy_temp.
      * copy_temp.
      * apply eval_keep_width; lia.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m)
      (le1 := PTree.set _t'10 (Vlong (clear_low ds old))
        (PTree.set _t'2 (Vlong (Int64.zero_ext ss source)) (PTree.set _t'11 (Vlong source) le))).
    + apply exec_set. eapply copy_eval_word; [|exact Hdest].
      rewrite !PTree.gso by discriminate; exact HD.
    + eapply exec_Sassign_value with (v := Vlong (copy_left_value ss ds old source))
        (v2 := Vlong (copy_left_value ss ds old source)).
      * eapply eval_Ederef. copy_temp.
      * unfold copy_left_value. copy_expr.
      * reflexivity.
      * apply assign_frame_word_at; exact SF.
Qed.

Lemma exec_copy_tail_short_left le m mc mf bi src_ofs bw dst_ofs ss ds n old source :
  1 <= ss /\ ss < ds <= 63 -> 0 < n <= ss ->
  le!_src_ptr = Some (Vptr bi src_ofs) -> le!_dst_ptr = Some (Vptr bw dst_ofs) ->
  le!_src_shift = Some (Vlong (Int64.repr ss)) -> le!_dst_shift = Some (Vlong (Int64.repr ds)) ->
  le!_n = Some (Vlong (Int64.repr n)) ->
  Mem.load Mint64 m bw (Ptrofs.unsigned dst_ofs) = Some (Vlong old) ->
  Mem.store Mint64 m bw (Ptrofs.unsigned dst_ofs) (Vlong (clear_low ds old)) = Some mc ->
  Mem.load Mint64 mc bi (Ptrofs.unsigned src_ofs) = Some (Vlong source) ->
  Mem.store Mint64 mc bw (Ptrofs.unsigned dst_ofs) (Vlong (copy_left_value ss ds old source)) = Some mf ->
  Clight2.exec_stmt ge0 empty_env le m copy_helper_tail E0
    (copy_left_env (copy_clear_env le ds old) ss ds old source) mf (Out_return None).
Proof.
  intros Hrange HN HP HD HS HDS HNtemp Hold SC Hsource SF.
  assert (Hnonzero : Int64.eq (Int64.repr ds) Int64.zero = Datatypes.false).
  { apply Int64.eq_false. intro HE. apply (f_equal Int64.unsigned) in HE.
    rewrite Int64.unsigned_repr in HE by (change (0 <= ds <= 18446744073709551615); lia).
    change (ds = 0) in HE; lia. }
  assert (Hlt : Int64.ltu (Int64.repr ss) (Int64.repr ds) = Datatypes.true).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_true by lia; reflexivity|change (0 <= ds <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  assert (Hback : Int64.ltu (Int64.repr ss) (Int64.repr n) = Datatypes.false).
  { unfold Int64.ltu. rewrite !Int64.unsigned_repr;
      [rewrite zlt_false by lia; reflexivity|change (0 <= n <= 18446744073709551615); lia|
        change (0 <= ss <= 18446744073709551615); lia]. }
  rewrite copy_helper_tail_shape. apply exec_Sseq_2; [|discriminate].
  eapply exec_Sifthenelse with (v1 := Vlong (Int64.repr ds)) (b := Datatypes.true).
  - copy_temp.
  - change (Some (negb (Int64.eq (Int64.repr ds) Int64.zero)) = Some true).
    rewrite Hnonzero; reflexivity.
  - rewrite copy_partial_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := copy_clear_env le ds old).
    + eapply exec_copy_clear; eauto; lia.
    + apply exec_Sseq_2; [|discriminate].
      eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
      * eapply eval_Ebinop with (v1 := Vlong (Int64.repr ss)) (v2 := Vlong (Int64.repr ds)).
        -- unfold copy_clear_env; copy_temp.
        -- unfold copy_clear_env; copy_temp.
        -- change (Some (Val.of_bool (Int64.ltu (Int64.repr ss) (Int64.repr ds))) = Some (Vint Int.one)).
           rewrite Hlt; reflexivity.
      * reflexivity.
      * rewrite copy_partial_left_shape.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf)
          (le1 := copy_left_env (copy_clear_env le ds old) ss ds old source).
        -- eapply exec_copy_left_fill with (src_ofs := src_ofs) (dst_ofs := dst_ofs); try eassumption.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HP.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HD.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HS.
           ++ unfold copy_clear_env. rewrite !PTree.gso by discriminate; exact HDS.
           ++ exact (Mem.load_store_same _ _ _ _ _ _ SC).
        -- apply exec_Sseq_2; [|discriminate].
           eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := Datatypes.true).
           ++ eapply eval_Ebinop with (v1 := Vlong (Int64.repr n)) (v2 := Vlong (Int64.repr ss)).
              ** unfold copy_left_env, copy_clear_env; copy_temp.
              ** unfold copy_left_env, copy_clear_env; copy_temp.
              ** change (Some (Val.of_bool (negb (Int64.ltu (Int64.repr ss) (Int64.repr n)))) =
                   Some (Vint Int.one)). rewrite Hback; reflexivity.
           ++ reflexivity.
           ++ apply exec_Sreturn_none.
Qed.

Theorem eval_copy_helper_short_left m bd base bs sbase bi edge rc bw outedge cursor n old source :
  frame_base_valid sbase -> frame_base_valid base ->
  frame_fields_at m bs sbase bi edge rc -> frame_fields_at m bd base bw outedge cursor ->
  0 <= rc <= Int64.max_unsigned -> 1 <= cursor <= Int64.max_unsigned ->
  8 * (1 + rc / 64) <= edge <= Ptrofs.max_unsigned ->
  0 <= outedge -> write_word_address outedge cursor <= Ptrofs.max_unsigned ->
  64 - rc mod 64 < cursor mod 64 -> 0 < n <= 64 - rc mod 64 ->
  bd <> bw ->
  (bi <> bw \/ edge - 8 * (1 + rc / 64) + 8 <= write_word_address outedge cursor \/
    write_word_address outedge cursor + 8 <= edge - 8 * (1 + rc / 64)) ->
  Mem.load Mint64 m bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source) ->
  Mem.load Mint64 m bw (write_word_address outedge cursor) = Some (Vlong old) ->
  Mem.valid_access m Mint64 bw (write_word_address outedge cursor) Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_copyBitsHelper)
      [Vptr bd (Ptrofs.repr base); Vptr bs (Ptrofs.repr sbase); Vlong (Int64.repr n)] E0 mf Vundef /\
    Mem.load Mint64 mf bw (write_word_address outedge cursor) =
      Some (Vlong (copy_left_value (64 - rc mod 64) (cursor mod 64) old source)) /\
    frame_fields_at mf bd base bw outedge cursor /\
    (forall chunk b ofs, b <> bw \/ ofs + size_chunk chunk <= write_word_address outedge cursor \/
      write_word_address outedge cursor + 8 <= ofs -> Mem.load chunk mf b ofs = Mem.load chunk m b ofs) /\
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mf b ofs kind p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mf b).
Proof.
  intros HS HB HF HW HR HC HE HO HA Hshort Hn Hbd Hsep Hsource Hold PW.
  pose proof (Z.mod_pos_bound rc 64 ltac:(lia)) as Hrm.
  pose proof (Z.mod_pos_bound cursor 64 ltac:(lia)) as Hcm.
  assert (Hsrcaddr : 0 <= edge - 8 * (1 + rc / 64) <= Ptrofs.max_unsigned).
  { pose proof (Z.div_pos rc 64 ltac:(lia) ltac:(lia)); lia. }
  assert (Hdstaddr : 0 <= write_word_address outedge cursor <= Ptrofs.max_unsigned).
  { unfold write_word_address in *. pose proof (Z.div_pos (cursor - 1) 64 ltac:(lia) ltac:(lia)); lia. }
  destruct (Mem.valid_access_store m Mint64 bw (write_word_address outedge cursor)
    (Vlong (clear_low (cursor mod 64) old)) PW) as [mc SC].
  assert (HsourceC : Mem.load Mint64 mc bi (edge - 8 * (1 + rc / 64)) = Some (Vlong source)).
  { erewrite Mem.load_store_other; [exact Hsource|exact SC|exact Hsep]. }
  assert (PWC : Mem.valid_access mc Mint64 bw (write_word_address outedge cursor) Writable)
    by (eapply Mem.store_valid_access_1; eauto).
  destruct (Mem.valid_access_store mc Mint64 bw (write_word_address outedge cursor)
    (Vlong (copy_left_value (64 - rc mod 64) (cursor mod 64) old source)) PWC) as [mf SF].
  exists mf. split.
  - eapply eval_copy_helper_prefix_composes; try eassumption; [|right; reflexivity].
    eapply exec_copy_tail_short_left with (src_ofs := Ptrofs.repr (edge - 8 * (1 + rc / 64)))
      (dst_ofs := Ptrofs.repr (write_word_address outedge cursor)) (mc := mc)
      (bi := bi) (bw := bw) (ss := 64 - rc mod 64) (ds := cursor mod 64)
      (n := n) (old := old) (source := source); try lia.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env. rewrite PTree.gss; reflexivity.
    + unfold copy_helper_env, copy_dst_shift_env, copy_src_shift_env, copy_dst_env, copy_src_env, copy_frame_env.
      rewrite !PTree.gso by discriminate. rewrite PTree.gss; reflexivity.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact Hold.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SC.
    + rewrite Ptrofs.unsigned_repr by exact Hsrcaddr; exact HsourceC.
    + rewrite Ptrofs.unsigned_repr by exact Hdstaddr; exact SF.
  - split.
    + exact (Mem.load_store_same _ _ _ _ _ _ SF).
    + split.
      * destruct HW as [Hedge Hcursor]. split.
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           erewrite Mem.load_store_other; [exact Hedge|exact SC|auto].
        -- erewrite Mem.load_store_other; [|exact SF|auto].
           erewrite Mem.load_store_other; [exact Hcursor|exact SC|auto].
      * split.
        -- intros chunk b ofs Houtside.
           erewrite Mem.load_store_other; [|exact SF|exact Houtside].
           eapply Mem.load_store_other; eauto.
        -- split.
           ++ intros b ofs kind p HP; eauto using Mem.perm_store_1.
           ++ intros b HV; eauto using Mem.store_valid_block_1.
Qed.
