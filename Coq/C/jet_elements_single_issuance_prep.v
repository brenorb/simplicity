(** Actual issuance_hash body, entry and frame copy. This jet has eight
    addressable locals and a t'3 branch result; do not substitute the smaller
    four-local, t'2 wrapper used by input/output hashing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_indexed_exec C.jet_elements_indexed_flag C.jet_elements_input_utxo_prep.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation FR := (Tstruct _frameItem noattr).
Local Notation CONF := (Tstruct _confidential noattr).
Local Notation AMT := (Tstruct _confAmount noattr).

Definition eis_env (bl bm bx ba bt bz bb br : block) : env :=
  PTree.set __res (br, CTX)
    (PTree.set ___compound__3 (bb, tarray tuchar 32)
      (PTree.set ___compound__2 (bz, AMT)
        (PTree.set ___compound__1 (bt, CONF)
          (PTree.set ___compound (ba, CONF)
            (PTree.set _ctx (bx, CTX)
              (PTree.set _midstate (bm, MID) (PTree.set _src (bl, FR) empty_env))))))).

Definition eis_temps (environment : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env environment (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_issuance_hash)))).

Definition eis_then : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_issuance_hash fn_body] beta iota in
      (fn_body f_simplicity_issuance_hash) in
    lazymatch b with Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ ?t _)) _)) => exact t end).

Definition eis_none : statement :=
  ltac:(let b := eval cbv delta [eis_then] beta iota in eis_then in
    lazymatch b with
    Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ ?n _)) _)) => exact n
    end).

Definition eis_some : statement :=
  ltac:(let b := eval cbv delta [eis_then] beta iota in eis_then in
    lazymatch b with
    Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ _ ?y)) _)) => exact y
    end).

Lemma eis_body :
  fn_body f_simplicity_issuance_hash =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR))
      (elements_indexed_rest_flag _t'3 _t'9 _t'10 _numInputs eis_then eiu_else).
Proof. reflexivity. Qed.

Lemma eis_blocks bl bm bx ba bt bz bb br :
  blocks_of_env sha_ge (eis_env bl bm bx ba bt bz bb br) =
    [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (bz, 0, 40);
     (bt, 0, 36); (bb, 0, 32); (ba, 0, 36); (br, 0, 88)].
Proof. vm_compute; reflexivity. Qed.

Lemma eis_entry environment m m1 m2 m3 m4 m5 m6 m7 m8 bl bm bx ba bt bz bb br bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) ->
  Mem.alloc m2 0 88 = (m3, bx) -> Mem.alloc m3 0 36 = (m4, ba) ->
  Mem.alloc m4 0 36 = (m5, bt) -> Mem.alloc m5 0 40 = (m6, bz) ->
  Mem.alloc m6 0 32 = (m7, bb) -> Mem.alloc m7 0 88 = (m8, br) ->
  function_entry2 sha_ge f_simplicity_issuance_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); environment] m
    (eis_env bl bm bx ba bt bz bb br) (eis_temps environment bd dbase bs sbase) m8.
Proof.
  intros A1 A2 A3 A4 A5 A6 A7 A8. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bm); [change (Mem.alloc m1 0 32 = (m2, bm)); exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bx); [change (Mem.alloc m2 0 88 = (m3, bx)); exact A3|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := ba); [change (Mem.alloc m3 0 36 = (m4, ba)); exact A4|].
    eapply alloc_variables_cons with (m1 := m5) (b1 := bt); [change (Mem.alloc m4 0 36 = (m5, bt)); exact A5|].
    eapply alloc_variables_cons with (m1 := m6) (b1 := bz); [change (Mem.alloc m5 0 40 = (m6, bz)); exact A6|].
    eapply alloc_variables_cons with (m1 := m7) (b1 := bb); [change (Mem.alloc m6 0 32 = (m7, bb)); exact A7|].
    eapply alloc_variables_cons with (m1 := m8) (b1 := br); [change (Mem.alloc m7 0 88 = (m8, br)); exact A8|].
    constructor.
  - reflexivity.
Qed.

Lemma eis_copy e le m mc bl bs sbase bytes :
  e!_src = Some (bl, FR) ->
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge e le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
Proof.
  intros HE HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; exact HE.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (bytes := bytes); cbn [typeof].
    + reflexivity.
    + intros _. rewrite HA. exact HS.
    + intros _. exists 0. reflexivity.
    + left. intro E; apply HD; symmetry; exact E.
    + rewrite HA. exact Hload.
    + exact Hstore.
Qed.
