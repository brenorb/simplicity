(** The actual two stores of issuanceTokenAmt's reissuance compound literal.
    This establishes the amount representation; it is not the whole jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Memory Events ClightBigstep.
Require Import C.jet_exec C.jets_elements C.jet_elements_linkage.
Require Import C.jet_elements_field_eval C.jet_elements_amt_helper C.jet_elements_amount_jets.
Require Import C.jet_elements_prim.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition token_zero_object := Evar ___compound (Tstruct _confAmount noattr).
Definition token_zero_explicit := Efield
  (Efield token_zero_object _anon_union (Tunion __4799 noattr)) _explicit tulong.
Definition token_zero_prefix := Efield token_zero_object _prefix tint.
Definition token_zero_init_stmt := Ssequence
  (Sassign token_zero_explicit (Econst_int Int.zero tint))
  (Sassign token_zero_prefix (Econst_int Int.one tint)).

Lemma token_zero_init_shape :
  match fn_body f_issuanceTokenAmt with
  | Ssequence _ (Sifthenelse _
      (Ssequence (Ssequence _ (Sifthenelse _ _ (Ssequence init _))) _) _) =>
      init = token_zero_init_stmt
  | _ => False
  end.
Proof. reflexivity. Qed.

Lemma token_zero_object_eval e le m b :
  e!___compound = Some (b, Tstruct _confAmount noattr) ->
  eval_expr elements_ge e le m token_zero_object (Vptr b Ptrofs.zero).
Proof.
  intro HE. eapply eval_Elvalue;
    [apply eval_Evar_local; exact HE|apply deref_loc_copy; reflexivity].
Qed.

Lemma token_zero_explicit_lvalue e le m b :
  e!___compound = Some (b, Tstruct _confAmount noattr) ->
  eval_lvalue elements_ge e le m token_zero_explicit b Ptrofs.zero Full.
Proof.
  intro HE. unfold token_zero_explicit.
  change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) at 1.
  eapply eval_elements_union_field_lvalue;
    [reflexivity|exact elements_confAmount_explicit|].
  eapply eval_Elvalue; [|apply deref_loc_copy; reflexivity].
  change Ptrofs.zero with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 0)) at 1.
  eapply eval_elements_field_lvalue;
    [reflexivity|exact elements_confAmount_union|apply token_zero_object_eval; exact HE].
Qed.

Lemma token_zero_prefix_lvalue e le m b :
  e!___compound = Some (b, Tstruct _confAmount noattr) ->
  eval_lvalue elements_ge e le m token_zero_prefix b (Ptrofs.repr 32) Full.
Proof.
  intro HE. unfold token_zero_prefix.
  change (Ptrofs.repr 32) with (Ptrofs.add Ptrofs.zero (Ptrofs.repr 32)).
  eapply eval_elements_field_lvalue;
    [reflexivity|exact elements_confAmount_prefix|apply token_zero_object_eval; exact HE].
Qed.

Theorem exec_token_zero_init e le m b :
  e!___compound = Some (b, Tstruct _confAmount noattr) ->
  Mem.range_perm m b 0 40 Cur Writable ->
  exists mi,
    Clight2.exec_stmt elements_ge e le m token_zero_init_stmt E0 le mi Out_normal /\
    amount_rep mi b 0 (Explicit Int64.zero) /\
    (forall chunk bb ofs, bb <> b \/ ofs + size_chunk chunk <= 0 \/ 40 <= ofs ->
       Mem.load chunk mi bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mi bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mi bb).
Proof.
  intros HE HP.
  assert (H64 : Mem.valid_access m Mint64 b 0 Writable).
  { split; [intros ofs Ho; apply HP; change (size_chunk Mint64) with 8 in Ho; lia|
            change (8 | 0); exists 0; reflexivity]. }
  destruct (Mem.valid_access_store m Mint64 b 0 (Vlong Int64.zero) H64) as [m1 HS1].
  assert (H32 : Mem.valid_access m1 Mint32 b 32 Writable).
  { split.
    - intros ofs Ho. eapply Mem.perm_store_1; [exact HS1|].
      apply HP. change (size_chunk Mint32) with 4 in Ho. lia.
    - change (4 | 32); exists 8; reflexivity. }
  destruct (Mem.valid_access_store m1 Mint32 b 32 (Vint Int.one) H32) as [mi HS2].
  assert (E1 : Clight2.exec_stmt elements_ge e le m
    (Sassign token_zero_explicit (Econst_int Int.zero tint)) E0 le m1 Out_normal).
  { eapply exec_Sassign_value with (v := Vlong Int64.zero) (v2 := Vint Int.zero)
      (b := b) (ofs := Ptrofs.zero).
    - apply token_zero_explicit_lvalue; exact HE.
    - constructor.
    - reflexivity.
    - apply assign_loc_value with (chunk := Mint64); [reflexivity|exact HS1]. }
  assert (E2 : Clight2.exec_stmt elements_ge e le m1
    (Sassign token_zero_prefix (Econst_int Int.one tint)) E0 le mi Out_normal).
  { eapply exec_Sassign_value with (v := Vint Int.one) (v2 := Vint Int.one)
      (b := b) (ofs := Ptrofs.repr 32).
    - apply token_zero_prefix_lvalue; exact HE.
    - constructor.
    - reflexivity.
    - apply assign_loc_value with (chunk := Mint32); [reflexivity|exact HS2]. }
  exists mi. split.
  - unfold token_zero_init_stmt.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := le); eauto.
  - split.
    + unfold amount_rep. split.
      * rewrite (Mem.load_store_other _ _ _ _ _ _ HS2).
        -- exact (Mem.load_store_same _ _ _ _ _ _ HS1).
        -- right; left; change (0 + 8 <= 32); lia.
      * exact (Mem.load_store_same _ _ _ _ _ _ HS2).
    + split.
      * intros chunk bb ofs Ho.
        rewrite (Mem.load_store_other _ _ _ _ _ _ HS2).
        -- apply (Mem.load_store_other _ _ _ _ _ _ HS1). cbn [size_chunk]. lia.
        -- cbn [size_chunk]. lia.
      * split.
        -- intros; eapply Mem.perm_store_1; [exact HS2|]. eapply Mem.perm_store_1; eauto.
        -- intros; eapply Mem.store_valid_block_1; [exact HS2|]. eapply Mem.store_valid_block_1; eauto.
Qed.
