(** Body/entry adapters for the original computing Elements input_hash.
    Frame copy, local layout, indexed wrapper and output encodings reuse
    input_utxo_hash's checked preparation contracts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval.
Require Import C.jet_elements_index_eval C.jet_elements_indexed_exec C.jet_elements_sha_program.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_input_utxo_prep.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation FR := (Tstruct _frameItem noattr).

Definition eih_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_input_hash)))).

Definition eih_then : statement :=
  ltac:(let b := eval cbv delta [f_simplicity_input_hash fn_body] beta iota in
      (fn_body f_simplicity_input_hash) in
    lazymatch b with Ssequence _ (Ssequence _ (Ssequence (Ssequence _ (Sifthenelse _ ?t _)) _)) => exact t end).

Lemma eih_body :
  fn_body f_simplicity_input_hash =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR))
      (elements_indexed_rest _t'9 _t'10 _numInputs eih_then eiu_else).
Proof. reflexivity. Qed.

Lemma eih_entry env m m1 m2 m3 m4 bl bm bx br bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) -> Mem.alloc m2 0 88 = (m3, bx) ->
  Mem.alloc m3 0 88 = (m4, br) ->
  function_entry2 sha_ge f_simplicity_input_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (eiu_env bl bm bx br) (eih_temps env bd dbase bs sbase) m4.
Proof.
  intros HA HB HC HD. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact HA|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bm); [change (Mem.alloc m1 0 32 = (m2, bm)); exact HB|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bx); [change (Mem.alloc m2 0 88 = (m3, bx)); exact HC|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := br); [change (Mem.alloc m3 0 88 = (m4, br)); exact HD|].
    constructor.
  - reflexivity.
Qed.


Lemma eih_input_ptr e le m xp ip bin inbase r :
  le!xp = Some (Vptr bin (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> inbase + 544 * Int64.unsigned r <= Ptrofs.max_unsigned ->
  eval_expr sha_ge e le m
    (Ebinop Oadd (Etempvar xp (tptr (Tstruct _sigInput noattr))) (Etempvar ip tulong)
      (tptr (Tstruct _sigInput noattr)))
    (Vptr bin (Ptrofs.repr (inbase + 544 * Int64.unsigned r))).
Proof.
  intros HP HI HB HM. rewrite elements_sha_genv.
  eapply eval_Ebinop; [apply eval_Etempvar; exact HP|apply eval_Etempvar; exact HI|].
  cbn [typeof]. unfold sem_binary_operation.
  rewrite (sem_add_ptr_long_sizeof (Clight.genv_cenv elements_ge) (Tstruct _sigInput noattr)
    r (Ptrofs.repr inbase) bin 544 m elements_sizeof_sigInput).
  replace (Ptrofs.of_int64 r) with
    (Ptrofs.of_int64 (Int64.repr (Int64.unsigned r)))
    by (rewrite Int64.repr_unsigned; reflexivity).
  rewrite elements_ptr_index_repr; [reflexivity|exact HB|lia|apply Int64.unsigned_range|exact HM].
Qed.

Lemma eih_isPegin_field : elements_field_at _sigInput _isPegin 537.
Proof. vm_compute; reflexivity. Qed.
Lemma eih_hasAnnex_field : elements_field_at _sigInput _hasAnnex 536.
Proof. vm_compute; reflexivity. Qed.
Lemma eih_pegin_field : elements_field_at _sigInput _pegin 32.
Proof. vm_compute; reflexivity. Qed.
Lemma eih_annex_field : elements_field_at _sigInput _annexHash 0.
Proof. vm_compute; reflexivity. Qed.
