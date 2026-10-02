(** Actual two-local multiply_64 entry, copy, readers, uint128 calls and return.
    Intermediate executions in this composition rule are discharged by layout. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_one8 C.jet_frame_layout C.jet_arith8_layout_exec.
Require Import C.jet_wide C.jet_binary_wide_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition e_frame_u128 bl br := PTree.set _r (br,Tstruct _secp256k1_uint128 noattr) (e_one8 bl).
Definition multiply64_temps env bd dbase bs sbase :=
  le_arith8_layout env f_simplicity_multiply_64 bd (Ptrofs.repr dbase) bs (Ptrofs.repr sbase).
Definition multiply64_read_temps env bd dbase bs sbase a b :=
  PTree.set _y (Vlong b) (PTree.set _t'2 (Vlong b)
    (PTree.set _x (Vlong a) (PTree.set _t'1 (Vlong a) (multiply64_temps env bd dbase bs sbase)))).

Lemma entry_frame_u128_jet env f m ma mb bl br bd dofs bs sofs :
  f.(fn_vars) = [(_src,Tstruct _frameItem noattr); (_r,Tstruct _secp256k1_uint128 noattr)] ->
  f.(fn_params) = [(_dst,tptr (Tstruct _frameItem noattr)); (_src,Tstruct _frameItem noattr);
    (_env,tptr (Tstruct _txEnv noattr))] ->
  list_disjoint [_dst; _src; _env] (map fst f.(fn_temps)) ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 16 = (mb,br) ->
  function_entry2 ge0 f [Vptr bd dofs; Vptr bs sofs; env] m (e_frame_u128 bl br)
    (le_arith8_layout env f bd dofs bs sofs) mb.
Proof.
  intros HV HP HT HA HB. constructor.
  - rewrite HV. change (list_norepet [_src; _r]). vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
  - rewrite HP. change (list_norepet [_dst; _src; _env]). vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
  - rewrite HP; exact HT.
  - rewrite HV. eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma,bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := br).
      * change (Mem.alloc ma 0 16 = (mb,br)); exact HB.
      * constructor.
  - unfold le_arith8_layout. rewrite HP; reflexivity.
Qed.

Lemma exec_frame_u128_copy m mc bl br bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs -> le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt ge0 (e_frame_u128 bl br) le m
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr))) E0 le mc Out_normal.
Proof.
  intros HB HA HN HL Hbytes HS.
  assert (HP : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local. unfold e_frame_u128. rewrite PTree.gso by discriminate. reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_frameItem_copy; [reflexivity| | |left; exact HN| |exact HS].
    + intros _; rewrite HP; exact HA.
    + intros _; exists 0; reflexivity.
    + rewrite HP; exact Hbytes.
Qed.

Lemma call_frame_u128_read s result le m mr bl br w :
  Clight2.eval_funcall ge0 m (Internal (wide_reader s)) [Vptr bl Ptrofs.zero] E0 mr (Vlong w) ->
  Clight2.exec_stmt ge0 (e_frame_u128 bl br) le m (wide_binary_read s result)
    E0 (PTree.set result (Vlong w) le) mr Out_normal.
Proof.
  intros HC. eapply exec_Scall with (vf := Vptr (jet_symbol_block (wide_reader_id s)) Ptrofs.zero)
    (vargs := [Vptr bl Ptrofs.zero]) (f := Internal (wide_reader s)) (vres := Vlong w).
  - reflexivity.
  - eapply eval_Elvalue.
    + apply eval_Evar_global; [destruct s; reflexivity|apply wide_reader_symbol].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof, eval_Evar_local. unfold e_frame_u128; rewrite PTree.gso by discriminate; reflexivity.
    + reflexivity.
    + apply eval_Enil.
  - apply wide_reader_funct.
  - destruct s; reflexivity.
  - exact HC.
Qed.

Lemma u128_mul_symbol : Genv.find_symbol (Clight.genv_genv ge0) _secp256k1_u128_mul =
  Some (jet_symbol_block _secp256k1_u128_mul).
Proof. vm_compute; reflexivity. Qed.
Lemma u128_mul_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _secp256k1_u128_mul) Ptrofs.zero) = Some (Internal f_secp256k1_u128_mul).
Proof. vm_compute; reflexivity. Qed.
Lemma write128_symbol : Genv.find_symbol (Clight.genv_genv ge0) _write128 = Some (jet_symbol_block _write128).
Proof. vm_compute; reflexivity. Qed.
Lemma write128_funct : Genv.find_funct (Clight.genv_genv ge0)
  (Vptr (jet_symbol_block _write128) Ptrofs.zero) = Some (Internal f_write128).
Proof. vm_compute; reflexivity. Qed.

Lemma eval_multiply64_composes env m ma mb mcopy mr1 mr2 mk me mf bl br bd dbase bs sbase bytes a b :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.alloc ma 0 16 = (mb,br) ->
  Mem.loadbytes mb bs sbase 16 = Some bytes -> Mem.storebytes mb bl 0 bytes = Some mcopy ->
  Clight2.eval_funcall ge0 mcopy (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr1 (Vlong a) ->
  Clight2.eval_funcall ge0 mr1 (Internal f_simplicity_read64) [Vptr bl Ptrofs.zero] E0 mr2 (Vlong b) ->
  Clight2.eval_funcall ge0 mr2 (Internal f_secp256k1_u128_mul) [Vptr br Ptrofs.zero; Vlong a; Vlong b] E0 mk Vundef ->
  Clight2.eval_funcall ge0 mk (Internal f_write128) [Vptr bd (Ptrofs.repr dbase); Vptr br Ptrofs.zero] E0 me Vundef ->
  Mem.free_list me (blocks_of_env ge0 (e_frame_u128 bl br)) = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_simplicity_multiply_64)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one).
Proof.
  intros HSbase HAlign HN HA HB Hbytes Hcopy HR1 HR2 HM HW HF.
  set (le0 := multiply64_temps env bd dbase bs sbase).
  set (le1 := PTree.set _x (Vlong a) (PTree.set _t'1 (Vlong a) le0)).
  set (le2 := multiply64_read_temps env bd dbase bs sbase a b).
  eapply eval_funcall_internal with (e := e_frame_u128 bl br) (le1 := le0) (le2 := le2)
    (m1 := mb) (m2 := me) (out := Out_return (Some (Vint Int.one,tint))).
  - eapply entry_frame_u128_jet; try eassumption; try reflexivity.
    change (list_disjoint [_dst; _src; _env] [_x; _y; _t'2; _t'1]). vm_compute; intuition congruence.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mcopy).
    + eapply exec_frame_u128_copy; try eassumption; reflexivity.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mr1).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr1).
        -- apply (call_frame_u128_read W64); exact HR1.
        -- apply exec_set. apply eval_Etempvar. apply PTree.gss.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mr2).
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr2).
           ++ apply (call_frame_u128_read W64); exact HR2.
           ++ apply exec_set. apply eval_Etempvar. apply PTree.gss.
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mk).
           ++ eapply exec_Scall with (vf := Vptr (jet_symbol_block _secp256k1_u128_mul) Ptrofs.zero)
                (vargs := [Vptr br Ptrofs.zero; Vlong a; Vlong b]) (f := Internal f_secp256k1_u128_mul) (vres := Vundef).
              ** reflexivity.
              ** eapply eval_Elvalue.
                 --- apply eval_Evar_global; [reflexivity|exact u128_mul_symbol].
                 --- apply deref_loc_reference; reflexivity.
              ** eapply eval_Econs.
                 --- apply eval_Eaddrof, eval_Evar_local. unfold e_frame_u128; apply PTree.gss.
                 --- reflexivity.
                 --- eapply eval_Econs.
                     +++ apply eval_Etempvar. unfold le2, multiply64_read_temps.
                         repeat rewrite PTree.gso by discriminate. apply PTree.gss.
                     +++ reflexivity.
                     +++ eapply eval_Econs; [apply eval_Etempvar; unfold le2, multiply64_read_temps; apply PTree.gss|
                           reflexivity|apply eval_Enil].
              ** exact u128_mul_funct.
              ** reflexivity.
              ** exact HM.
           ++ eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := me).
              ** eapply call_frame_writer with (f := f_write128) (b := jet_symbol_block _write128)
                   (v := Vptr br Ptrofs.zero) (vret := Vundef).
                 --- reflexivity.
                 --- reflexivity.
                 --- reflexivity.
                 --- exact write128_symbol.
                 --- exact write128_funct.
                 --- apply eval_Eaddrof, eval_Evar_local. unfold e_frame_u128; apply PTree.gss.
                 --- reflexivity.
                 --- exact HW.
              ** apply exec_Sreturn_some. apply eval_Econst_int.
  - cbn; split; solve [discriminate|reflexivity].
  - exact HF.
Qed.
