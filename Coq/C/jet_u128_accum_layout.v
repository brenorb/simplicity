(** Complete actual uint128 += uint64 call: read lo, store wrapped lo,
    reload hi and updated lo, then store hi plus the promoted comparison. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_u128_fields.
Require Import C.jet_umul128_layout C.jet_u128_accum_value C.jet_readBit_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition u128_accum_temps br base a := PTree.set _a (Vlong a)
  (PTree.set _r (Vptr br (Ptrofs.repr base))
    (create_undef_temps f_secp256k1_u128_accum_u64.(fn_temps))).
Definition u128_accum_hi_expr := Ebinop Oadd (Etempvar _t'1 tulong)
  (Ebinop Olt (Etempvar _t'2 tulong) (Etempvar _a tulong) tint) tulong.

Lemma u128_accum_symbol : Genv.find_symbol (Clight.genv_genv ge0) _secp256k1_u128_accum_u64 =
  Some (jet_symbol_block _secp256k1_u128_accum_u64).
Proof. vm_compute; reflexivity. Qed.
Lemma u128_accum_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _secp256k1_u128_accum_u64) Ptrofs.zero) =
  Some (Internal f_secp256k1_u128_accum_u64).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_u128_accum_hi_expr e le m hi lo a :
  le!_t'1 = Some (Vlong hi) -> le!_t'2 = Some (Vlong (u128_accum_lo lo a)) ->
  le!_a = Some (Vlong a) ->
  eval_expr ge0 e le m u128_accum_hi_expr (Vlong (u128_accum_hi hi lo a)).
Proof.
  intros HH HL HA. unfold u128_accum_hi_expr.
  eapply eval_Ebinop with (v1 := Vlong hi) (v2 := Vint (bit_int (u128_accum_carry lo a))).
  - apply eval_Etempvar; exact HH.
  - eapply eval_Ebinop with (v1 := Vlong (u128_accum_lo lo a)) (v2 := Vlong a).
    + apply eval_Etempvar; exact HL.
    + apply eval_Etempvar; exact HA.
    + change (Some (Val.of_bool (u128_accum_carry lo a)) =
        Some (Vint (bit_int (u128_accum_carry lo a)))).
      destruct (u128_accum_carry lo a); reflexivity.
  - unfold u128_accum_hi. destruct (u128_accum_carry lo a); reflexivity.
Qed.

Theorem eval_u128_accum_layout m br base hi lo a : frame_base_valid base ->
  Mem.valid_access m Mint64 br base Writable ->
  Mem.valid_access m Mint64 br (base + 8) Writable ->
  Mem.load Mint64 m br base = Some (Vlong lo) ->
  Mem.load Mint64 m br (base + 8) = Some (Vlong hi) ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_secp256k1_u128_accum_u64)
      [Vptr br (Ptrofs.repr base); Vlong a] E0 mf Vundef /\
    Mem.load Mint64 mf br base = Some (Vlong (u128_accum_lo lo a)) /\
    Mem.load Mint64 mf br (base + 8) = Some (Vlong (u128_accum_hi hi lo a)) /\
    (forall chunk bb addr, bb <> br \/ addr + size_chunk chunk <= base \/ base + 16 <= addr ->
      Mem.load chunk mf bb addr = Mem.load chunk m bb addr) /\
    (forall bb addr kind p, Mem.perm m bb addr kind p -> Mem.perm mf bb addr kind p) /\
    Mem.nextblock mf = Mem.nextblock m.
Proof.
  intros HB PL PH LL LH.
  destruct (Mem.valid_access_store m Mint64 br base (Vlong (u128_accum_lo lo a)) PL) as [mi SL].
  assert (PHi : Mem.valid_access mi Mint64 br (base + 8) Writable).
  { destruct PH as [P A]. split; [|exact A]. intros addr Haddr.
    eapply Mem.perm_store_1; [exact SL|apply P; exact Haddr]. }
  destruct (Mem.valid_access_store mi Mint64 br (base + 8) (Vlong (u128_accum_hi hi lo a)) PHi)
    as [mf SH].
  assert (LLi : Mem.load Mint64 mi br base = Some (Vlong (u128_accum_lo lo a))).
  { exact (Mem.load_store_same _ _ _ _ _ _ SL). }
  assert (LHi : Mem.load Mint64 mi br (base + 8) = Some (Vlong hi)).
  { erewrite Mem.load_store_other; [exact LH|exact SL|right; right; cbn; lia]. }
  set (le0 := u128_accum_temps br base a).
  set (le1 := PTree.set _t'3 (Vlong lo) le0).
  set (le2 := PTree.set _t'1 (Vlong hi) le1).
  set (le3 := PTree.set _t'2 (Vlong (u128_accum_lo lo a)) le2).
  exists mf. split.
  - eapply eval_funcall_internal with (e := PTree.empty _) (le1 := le0) (le2 := le3)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + constructor.
      * constructor.
      * change (list_norepet [_r; _a]). vm_compute.
        repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
      * change (list_disjoint [_r; _a] [_t'3; _t'2; _t'1]). vm_compute; intuition congruence.
      * constructor.
      * reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mi).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
        -- apply exec_set. eapply (eval_u128_field Datatypes.false _r); [exact HB| |].
           ++ unfold le0, u128_accum_temps. umul128_lookup.
           ++ change (base + u128_field_offset Datatypes.false) with (base + 0). rewrite Z.add_0_r; exact LL.
        -- eapply exec_Sassign with (loc := br) (ofs := Ptrofs.add (Ptrofs.repr base) Ptrofs.zero)
             (bf := Full) (v2 := Vlong (u128_accum_lo lo a)) (v := Vlong (u128_accum_lo lo a)).
           ++ apply (eval_u128_field_lvalue Datatypes.false _r). unfold le1, le0, u128_accum_temps. umul128_lookup.
           ++ unfold le1, le0, u128_accum_temps, u128_accum_lo. umul128_scalar.
           ++ reflexivity.
           ++ apply assign_loc_value with (chunk := Mint64); [reflexivity|].
              unfold Mem.storev. change Ptrofs.zero with (Ptrofs.repr 0).
              rewrite (frame_field_address base 0 HB ltac:(lia)), Z.add_0_r. exact SL.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mi).
        -- apply exec_set. eapply (eval_u128_field Datatypes.true _r); [exact HB| |exact LHi].
           unfold le1, le0, u128_accum_temps. umul128_lookup.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mi).
           ++ apply exec_set. eapply (eval_u128_field Datatypes.false _r); [exact HB| |].
              ** unfold le2, le1, le0, u128_accum_temps. umul128_lookup.
              ** change (base + u128_field_offset Datatypes.false) with (base + 0). rewrite Z.add_0_r; exact LLi.
           ++ eapply exec_Sassign with (loc := br) (ofs := Ptrofs.add (Ptrofs.repr base) (Ptrofs.repr 8))
                (bf := Full) (v2 := Vlong (u128_accum_hi hi lo a)) (v := Vlong (u128_accum_hi hi lo a)).
              ** apply (eval_u128_field_lvalue Datatypes.true _r). unfold le3, le2, le1, le0, u128_accum_temps. umul128_lookup.
              ** apply eval_u128_accum_hi_expr; unfold le3, le2, le1, le0, u128_accum_temps; umul128_lookup.
              ** reflexivity.
              ** apply assign_loc_value with (chunk := Mint64); [reflexivity|].
                 unfold Mem.storev. rewrite frame_field_address by (exact HB || lia). exact SH.
    + reflexivity.
    + reflexivity.
  - split.
    + erewrite Mem.load_store_other; [exact LLi|exact SH|right; left; cbn; lia].
    + split; [exact (Mem.load_store_same _ _ _ _ _ _ SH)|]. split.
      * intros chunk bb addr Hout. erewrite Mem.load_store_other; [|exact SH|].
        -- eapply Mem.load_store_other; [exact SL|].
           destruct Hout as [N|[L|R]]; [left; exact N|right; left; exact L|right; right; cbn; lia].
        -- destruct Hout as [N|[L|R]]; [left; exact N|right; left; lia|right; right; cbn; lia].
      * split.
        -- intros bb addr kind p HP. eapply Mem.perm_store_1; [exact SH|].
           eapply Mem.perm_store_1; [exact SL|exact HP].
        -- rewrite (Mem.nextblock_store _ _ _ _ _ _ SH). eapply Mem.nextblock_store; exact SL.
Qed.
