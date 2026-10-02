(** Actual sha256_init allocation, IV call, compound initialization,
    By_copy struct return and local cleanup. Initial-only consumer is separate. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jets C.jet_exec C.jet_sha256_iv_exec C.jet_sha256_init_fields_layout.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha_init_env bc := PTree.set ___compound (bc,Tstruct _sha256_context noattr) empty_env.
Definition sha_init_temps br bi input := PTree.set _output (Vptr bi (Ptrofs.repr input))
  (PTree.set __res (Vptr br Ptrofs.zero) (create_undef_temps f_sha256_init.(fn_temps))).

Lemma sha_init_entry m ma bc br bi input : Mem.alloc m 0 88 = (ma,bc) ->
  function_entry2 ge0 f_sha256_init [Vptr br Ptrofs.zero; Vptr bi (Ptrofs.repr input)]
    m (sha_init_env bc) (sha_init_temps br bi input) ma.
Proof.
  intros HA. constructor.
  - change (list_norepet [___compound]); repeat constructor; cbn; tauto.
  - change (list_norepet [__res; _output]); vm_compute.
    repeat (apply list_norepet_cons; [simpl; intuition discriminate|]). constructor.
  - change (list_disjoint [__res; _output] []); intros i j HI HJ; contradiction.
  - eapply alloc_variables_cons with (m1 := ma) (b1 := bc);
      [change (Mem.alloc m 0 88 = (ma,bc)); exact HA|constructor].
  - reflexivity.
Qed.

Theorem eval_sha256_init_composes m ma mi mz me mf bc br bi input bytes :
  bc <> br -> Mem.alloc m 0 88 = (ma,bc) ->
  Clight2.eval_funcall ge0 ma (Internal f_sha256_iv) [Vptr bi (Ptrofs.repr input)] E0 mi Vundef ->
  Clight2.exec_stmt ge0 (sha_init_env bc) (sha_init_temps br bi input) mi sha_ctx_fields_stmt
    E0 (sha_init_temps br bi input) mz Out_normal ->
  Mem.loadbytes mz bc 0 88 = Some bytes -> Mem.storebytes mz br 0 bytes = Some me ->
  Mem.free me bc 0 88 = Some mf ->
  Clight2.eval_funcall ge0 m (Internal f_sha256_init) [Vptr br Ptrofs.zero; Vptr bi (Ptrofs.repr input)] E0 mf Vundef.
Proof.
  intros HD HA HIV HFields HL HS HF. set (le := sha_init_temps br bi input).
  eapply eval_funcall_internal with (e := sha_init_env bc) (le1 := le) (le2 := le)
    (m1 := ma) (m2 := me) (out := Out_return None).
  - eapply sha_init_entry; exact HA.
  - rewrite sha256_init_body_shape.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi).
    + eapply exec_Scall with (vf := Vptr (jet_symbol_block _sha256_iv) Ptrofs.zero)
        (vargs := [Vptr bi (Ptrofs.repr input)]) (f := Internal f_sha256_iv) (vres := Vundef).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha256_iv_symbol]|apply deref_loc_reference; reflexivity].
      * eapply eval_Econs; [apply eval_Etempvar; unfold le, sha_init_temps; apply PTree.gss|reflexivity|apply eval_Enil].
      * exact sha256_iv_funct.
      * reflexivity.
      * exact HIV.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := me).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mz).
        -- exact HFields.
        -- eapply exec_Sassign_copy.
           ++ apply eval_Ederef. apply eval_Etempvar.
              unfold le, sha_init_temps; rewrite PTree.gso by discriminate; apply PTree.gss.
           ++ eapply eval_Elvalue; [apply eval_Evar_local; unfold sha_init_env; apply PTree.gss|apply deref_loc_copy; reflexivity].
           ++ reflexivity.
           ++ eapply assign_loc_copy with (b' := bc) (ofs' := Ptrofs.zero) (bytes := bytes).
              ** reflexivity.
              ** intros _. change (8 | 0); exists 0; reflexivity.
              ** intros _. change (8 | 0); exists 0; reflexivity.
              ** left; exact HD.
              ** exact HL.
              ** exact HS.
      * apply exec_Sreturn_none.
  - reflexivity.
  - change (Mem.free_list me [(bc,0,88)] = Some mf). cbn. rewrite HF; reflexivity.
Qed.
