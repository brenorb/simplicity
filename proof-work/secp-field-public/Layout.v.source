(** Exact original public multiplication body and three-local entry. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy_layout C.jet_secp_linkage C.jets_secp.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition frame_type : type := Tstruct jets_secp._frameItem noattr.
Definition field_type : type := Tstruct jets_secp.__5467 noattr.
Definition public_env (bl ba bb : block) : env :=
  PTree.set jets_secp._b (bb, field_type)
    (PTree.set jets_secp._a (ba, field_type)
      (PTree.set jets_secp._src (bl, frame_type) empty_env)).
Definition public_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set jets_secp._env v_env
    (PTree.set jets_secp._src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set jets_secp._dst (Vptr bd (Ptrofs.repr dbase))
        (create_undef_temps (fn_temps f_simplicity_fe_multiply)))).
Definition copy_stmt := Sassign (Evar jets_secp._src frame_type) (Etempvar jets_secp._src frame_type).
Definition read_stmt id := Scall None
  (Evar jets_secp._read_fe (Tfunction
    (Tcons (tptr field_type) (Tcons (tptr frame_type) Tnil)) tvoid cc_default))
  [Eaddrof (Evar id field_type) (tptr field_type);
   Eaddrof (Evar jets_secp._src frame_type) (tptr frame_type)].
Definition mul_stmt := Scall None
  (Evar jets_secp._secp256k1_fe_mul (Tfunction
    (Tcons (tptr field_type) (Tcons (tptr field_type) (Tcons (tptr field_type) Tnil))) tvoid cc_default))
  [Eaddrof (Evar jets_secp._a field_type) (tptr field_type);
   Eaddrof (Evar jets_secp._a field_type) (tptr field_type);
   Eaddrof (Evar jets_secp._b field_type) (tptr field_type)].
Definition write_stmt := Scall None
  (Evar jets_secp._write_fe (Tfunction
    (Tcons (tptr frame_type) (Tcons (tptr field_type) Tnil)) tvoid cc_default))
  [Etempvar jets_secp._dst (tptr frame_type);
   Eaddrof (Evar jets_secp._a field_type) (tptr field_type)].
Definition rest_stmt := Ssequence (read_stmt jets_secp._a)
  (Ssequence (read_stmt jets_secp._b)
    (Ssequence mul_stmt (Ssequence write_stmt (Sreturn (Some (Econst_int (Int.repr 1) tint)))))).
Lemma original_public_body : fn_body f_simplicity_fe_multiply = Ssequence copy_stmt rest_stmt.
Proof. reflexivity. Qed.
Lemma helper_symbols :
  Genv.find_symbol secp_ge jets_secp._read_fe = Some (secp_symbol_block jets_secp._read_fe) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._read_fe) Ptrofs.zero) = Some (Internal f_read_fe) /\
  Genv.find_symbol secp_ge jets_secp._write_fe = Some (secp_symbol_block jets_secp._write_fe) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._write_fe) Ptrofs.zero) = Some (Internal f_write_fe) /\
  Genv.find_symbol secp_ge jets_secp._secp256k1_fe_mul = Some (secp_symbol_block jets_secp._secp256k1_fe_mul) /\
  Genv.find_funct secp_ge (Vptr (secp_symbol_block jets_secp._secp256k1_fe_mul) Ptrofs.zero) = Some (Internal f_secp256k1_fe_mul).
Proof. vm_compute; repeat split; reflexivity. Qed.

Lemma original_public_entry v_env m ml ma mb bl ba bb bd dbase bs sbase :
  Mem.alloc m 0 16 = (ml, bl) -> Mem.alloc ml 0 40 = (ma, ba) -> Mem.alloc ma 0 40 = (mb, bb) ->
  function_entry2 secp_ge f_simplicity_fe_multiply
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (public_env bl ba bb) (public_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HL HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ml) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ml, bl)); exact HL.
    + eapply alloc_variables_cons with (m1 := ma) (b1 := ba).
      * change (Mem.alloc ml 0 40 = (ma, ba)); exact HA.
      * eapply alloc_variables_cons with (m1 := mb) (b1 := bb).
        -- change (Mem.alloc ma 0 40 = (mb, bb)); exact HB.
        -- constructor.
  - reflexivity.
Qed.

Lemma exec_public_copy m mc bl ba bb bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!jets_secp._src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt secp_ge (public_env bl ba bb) le m copy_stmt E0 le mc Out_normal.
Proof.
  intros HBase HAlign HD HT HL HS.
  assert (HU : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr; unfold frame_base_valid in HBase; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HT.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _; change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)); rewrite HU; exact HAlign.
    + intros _; change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes); rewrite HU; exact HL.
    + exact HS.
Qed.
