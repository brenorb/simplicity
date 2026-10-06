(** The actual by-value source-frame copy at the secp public jet boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_secp_linkage C.jets_secp.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

Definition secp_public_env (bl ba : block) : env :=
  PTree.set jets_secp._a (ba, Tstruct jets_secp.__5467 noattr)
    (PTree.set jets_secp._src (bl, Tstruct jets_secp._frameItem noattr) empty_env).
Definition secp_public_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set jets_secp._env v_env
    (PTree.set jets_secp._src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set jets_secp._dst (Vptr bd (Ptrofs.repr dbase))
        (create_undef_temps (fn_temps f_simplicity_fe_normalize)))).
Lemma secp_fe_normalize_entry v_env m ma mb bl ba bd dbase bs sbase :
  Mem.alloc m 0 16 = (ma, bl) -> Mem.alloc ma 0 40 = (mb, ba) ->
  function_entry2 secp_ge f_simplicity_fe_normalize
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (secp_public_env bl ba) (secp_public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ma, bl)); exact HA.
    + eapply alloc_variables_cons with (m1 := mb) (b1 := ba).
      * change (Mem.alloc ma 0 40 = (mb, ba)); exact HB.
      * constructor.
  - reflexivity.
Qed.
Lemma exec_secp_public_copy m mc bl ba bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!jets_secp._src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m
    (Sassign (Evar jets_secp._src (Tstruct jets_secp._frameItem noattr))
      (Etempvar jets_secp._src (Tstruct jets_secp._frameItem noattr))) E0 le mc Out_normal.
Proof.
  intros HBase HAlign HSeparate HTemp HLoad HStore.
  assert (HUnsigned : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr; unfold frame_base_valid in HBase; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HTemp.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _; change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)); rewrite HUnsigned; exact HAlign.
    + intros _; change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HUnsigned; exact HLoad.
    + exact HStore.
Qed.
Lemma secp_public_copy_from_fields m bl ba bs sbase bi edge rc le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!jets_secp._src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  frame_fields_at m bs sbase bi edge rc -> Mem.range_perm m bl 0 16 Cur Writable ->
  exists mc,
    Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m
      (Sassign (Evar jets_secp._src (Tstruct jets_secp._frameItem noattr))
        (Etempvar jets_secp._src (Tstruct jets_secp._frameItem noattr))) E0 le mc Out_normal /\
    frame_fields_at mc bl 0 bi edge rc.
Proof.
  intros HBase HAlign HSeparate HTemp [HEdge HCursor] HPerm.
  destruct (frame_loadbytes_at m bs sbase _ _ HEdge HCursor) as [bytes HLoad].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HLoad) as HLength.
  assert (HWritable : Mem.range_perm m bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite HLength; exact HPerm. }
  destruct (Mem.range_perm_storebytes m bl 0 bytes HWritable) as [mc HStore].
  exists mc; split.
  - apply exec_secp_public_copy with (bs := bs) (sbase := sbase) (bytes := bytes); assumption.
  - apply (frame_copy_fields_at m mc bs sbase bl bytes _ _ HLoad HStore HEdge HCursor).
Qed.

From compcert Require Import Globalenvs.
Lemma secp_public_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._read_fe = Some (secp_symbol_block jets_secp._read_fe) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._read_fe) Ptrofs.zero) = Some (Internal f_read_fe) /\
  Genv.find_symbol secp_ge jets_secp._write_fe = Some (secp_symbol_block jets_secp._write_fe) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._write_fe) Ptrofs.zero) = Some (Internal f_write_fe).
Proof. vm_compute; repeat split; reflexivity. Qed.
