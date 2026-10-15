(** Actual local-array expressions, entry and call boundary of lbtc_asset. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events Globalenvs.
From compcert Require Import ClightBigstep.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval.
Require Import C.jet_elements_wrapper C.jet_elements_hash_write C.jet_elements_hash_helpers.
Require Import C.jet_u32_local_init.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition lbtc_asset_words : list int := map Int.repr
  [1834097720; -333536937; 883827383; -1000315839;
   673824976; 1470040689; 1025246445; -377945489].

Definition lbtc_array_expr := Efield (Evar _lbtc_assetid (Tstruct _sha256_midstate noattr))
  _s (tarray tuint 8).
Definition lbtc_write_stmt := Scall None
  (Evar _writeHash (Tfunction (Tcons (tptr (Tstruct _frameItem noattr))
    (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
  [Etempvar _dst (tptr (Tstruct _frameItem noattr));
   Eaddrof (Evar _lbtc_assetid (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr))].
Definition lbtc_locals bl bh := PTree.set _lbtc_assetid (bh, Tstruct _sha256_midstate noattr)
  (PTree.set _src (bl, Tstruct _frameItem noattr) empty_env).

Lemma lbtc_body_shape : fn_body f_simplicity_lbtc_asset =
  Ssequence elements_copy_stmt
    (u32_local_prefix lbtc_array_expr 0 lbtc_asset_words (elements_simple_rest lbtc_write_stmt)).
Proof. reflexivity. Qed.

Lemma lbtc_blocks bl bh : blocks_of_env elements_ge (lbtc_locals bl bh) =
  [(bl, 0, 16); (bh, 0, 32)].
Proof. vm_compute; reflexivity. Qed.

Lemma lbtc_entry env m ma mb bl bh bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 32 = (mb, bh) ->
  function_entry2 elements_ge f_simplicity_lbtc_asset
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (lbtc_locals bl bh) (elements_wrapper_temps f_simplicity_lbtc_asset env bd dbase bs sbase) mb.
Proof.
  intros A1 A2. constructor.
  - change (list_norepet [_src; _lbtc_assetid]). repeat constructor; simpl; intuition discriminate.
  - change (list_norepet [_dst; _src; _env]). repeat constructor; simpl; intuition discriminate.
  - intros i j Hi Hj. contradiction.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact A1.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := bh).
      * change (Mem.alloc ma 0 32 = (mb, bh)); exact A2.
      * constructor.
  - reflexivity.
Qed.

Lemma lbtc_copy m mc bl bh bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt elements_ge (lbtc_locals bl bh) le m elements_copy_stmt E0 le mc Out_normal.
Proof.
  intros HB HA HD HL Hbytes Hstore.
  assert (Hbase : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase)
    by (apply Ptrofs.unsigned_repr; unfold frame_base_valid in HB; lia).
  eapply exec_Sassign_copy.
  - apply eval_Evar_local. unfold lbtc_locals. rewrite PTree.gso by discriminate. apply PTree.gss.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite Hbase; exact HA.
    + intros _. change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite Hbase; exact Hbytes.
    + exact Hstore.
Qed.

Lemma lbtc_array_eval e le m bh :
  e!_lbtc_assetid = Some (bh, Tstruct _sha256_midstate noattr) ->
  eval_expr elements_ge e le m lbtc_array_expr (Vptr bh Ptrofs.zero).
Proof.
  intro Hlocal.
  assert (Hvar : eval_expr elements_ge e le m
    (Evar _lbtc_assetid (Tstruct _sha256_midstate noattr)) (Vptr bh Ptrofs.zero)).
  { eapply eval_Elvalue; [apply eval_Evar_local; exact Hlocal|apply deref_loc_copy; reflexivity]. }
  pose proof (eval_elements_field_array e le m
    (Evar _lbtc_assetid (Tstruct _sha256_midstate noattr)) _sha256_midstate _s 0
    (tarray tuint 8) bh Ptrofs.zero ltac:(reflexivity) elements_midstate_s
    ltac:(intros; discriminate) ltac:(reflexivity) Hvar) as H.
  rewrite Ptrofs.add_zero in H. exact H.
Qed.

Lemma lbtc_lhs_eval e le m bh j :
  e!_lbtc_assetid = Some (bh, Tstruct _sha256_midstate noattr) -> (j < 8)%nat ->
  eval_lvalue elements_ge e le m (u32_local_lhs lbtc_array_expr j)
    bh (Ptrofs.repr (0 + 4 * Z.of_nat j)) Full.
Proof.
  intros Hlocal Hj.
  assert (Hsigned : Int.signed (Int.repr (Z.of_nat j)) = Z.of_nat j)
    by (apply Int.signed_repr; change (-2147483648 <= Z.of_nat j <= 2147483647); lia).
  unfold u32_local_lhs. eapply eval_Ederef.
  eapply eval_Ebinop with (v1 := Vptr bh Ptrofs.zero) (v2 := Vint (Int.repr (Z.of_nat j))).
  - apply lbtc_array_eval; exact Hlocal.
  - constructor.
  - change (Some (Vptr bh (Ptrofs.add Ptrofs.zero
      (Ptrofs.mul (Ptrofs.repr 4) (Ptrofs.of_ints (Int.repr (Z.of_nat j)))))) =
      Some (Vptr bh (Ptrofs.repr (0 + 4 * Z.of_nat j)))).
    unfold Ptrofs.of_ints. rewrite Hsigned. unfold Ptrofs.mul, Ptrofs.add.
    change (Ptrofs.unsigned Ptrofs.zero) with 0.
    change (Ptrofs.unsigned (Ptrofs.repr 4)) with 4.
    rewrite (Ptrofs.unsigned_repr (Z.of_nat j)) by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    rewrite (Ptrofs.unsigned_repr (4 * Z.of_nat j)) by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
    reflexivity.
Qed.

Lemma lbtc_write_call e le m me bh bd dbase :
  e!_lbtc_assetid = Some (bh, Tstruct _sha256_midstate noattr) -> e!_writeHash = None ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall elements_ge m (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr bh Ptrofs.zero] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le m lbtc_write_stmt E0 le me Out_normal.
Proof.
  intros Hlocal Hglobal Hdst Hcall. unfold lbtc_write_stmt.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero)
    (f := Internal f_writeHash)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bh Ptrofs.zero]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact Hglobal|exact elements_writeHash_symbol]|
      apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact Hdst|reflexivity|].
    eapply eval_Econs; [apply eval_Eaddrof, eval_Evar_local; exact Hlocal|reflexivity|apply eval_Enil].
  - exact elements_writeHash_funct.
  - reflexivity.
  - exact Hcall.
Qed.
