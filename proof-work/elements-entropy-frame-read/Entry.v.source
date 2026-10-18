(** Exact five-local entry of the original entropy frame jet. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Values Events.
Require Import C.jets_elements C.jet_elements_linkage.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition entropy_frame_vars : list (ident * type) :=
  [(_src, Tstruct _frameItem noattr); (_op, Tstruct _outpoint noattr);
   (_contract, Tstruct _sha256_midstate noattr); (_result, Tstruct _sha256_midstate noattr);
   (__res, Tstruct _sha256_midstate noattr)].
Definition entropy_frame_params : list (ident * type) :=
  [(_dst, tptr (Tstruct _frameItem noattr)); (_src, Tstruct _frameItem noattr);
   (_env, tptr (Tstruct _txEnv noattr))].
Lemma entropy_frame_header :
  fn_vars f_simplicity_calculate_issuance_entropy = entropy_frame_vars /\
  fn_params f_simplicity_calculate_issuance_entropy = entropy_frame_params /\
  fn_temps f_simplicity_calculate_issuance_entropy = [(_t'1, tulong)] /\
  fn_return f_simplicity_calculate_issuance_entropy = tbool /\
  fn_callconv f_simplicity_calculate_issuance_entropy = cc_default.
Proof. repeat split; reflexivity. Qed.

Definition entropy_frame_env (bl bo bc br bt : block) : env :=
  PTree.set __res (bt, Tstruct _sha256_midstate noattr)
    (PTree.set _result (br, Tstruct _sha256_midstate noattr)
      (PTree.set _contract (bc, Tstruct _sha256_midstate noattr)
        (PTree.set _op (bo, Tstruct _outpoint noattr)
          (PTree.set _src (bl, Tstruct _frameItem noattr) empty_env)))).
Definition entropy_frame_temps (env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (PTree.set _t'1 Vundef (PTree.empty val)))).

Lemma entropy_frame_size : sizeof elements_ge (Tstruct _frameItem noattr) = 16.
Proof. vm_compute; reflexivity. Qed.
Lemma entropy_midstate_size : sizeof elements_ge (Tstruct _sha256_midstate noattr) = 32.
Proof. vm_compute; reflexivity. Qed.
Lemma entropy_outpoint_size : sizeof elements_ge (Tstruct _outpoint noattr) = 40.
Proof. vm_compute; reflexivity. Qed.

Theorem entropy_frame_entry env m m1 m2 m3 m4 m5 bl bo bc br bt bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 40 = (m2, bo) ->
  Mem.alloc m2 0 32 = (m3, bc) -> Mem.alloc m3 0 32 = (m4, br) ->
  Mem.alloc m4 0 32 = (m5, bt) ->
  function_entry2 elements_ge f_simplicity_calculate_issuance_entropy
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (entropy_frame_env bl bo bc br bt) (entropy_frame_temps env bd dbase bs sbase) m5.
Proof.
  intros A1 A2 A3 A4 A5. constructor.
  - change (list_norepet [_src; _op; _contract; _result; __res]).
    unfold _src, _op, _contract, _result, __res.
    repeat constructor; cbn; intuition discriminate.
  - change (list_norepet [_dst; _src; _env]).
    unfold _dst, _src, _env. repeat constructor; cbn; intuition discriminate.
  - change (list_disjoint [_dst; _src; _env] [_t'1]).
    unfold list_disjoint, _dst, _src, _env, _t'1. cbn. intuition congruence.
  - change (alloc_variables elements_ge empty_env m entropy_frame_vars (entropy_frame_env bl bo bc br bt) m5).
    unfold entropy_frame_vars, entropy_frame_env.
    eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + rewrite entropy_frame_size. exact A1.
    + eapply alloc_variables_cons with (m1 := m2) (b1 := bo).
      * rewrite entropy_outpoint_size. exact A2.
      * eapply alloc_variables_cons with (m1 := m3) (b1 := bc).
        -- rewrite entropy_midstate_size. exact A3.
        -- eapply alloc_variables_cons with (m1 := m4) (b1 := br).
           ++ rewrite entropy_midstate_size. exact A4.
           ++ eapply alloc_variables_cons with (m1 := m5) (b1 := bt).
              ** rewrite entropy_midstate_size. exact A5.
              ** constructor.
  - reflexivity.
Qed.

Lemma entropy_env_blocks bl bo bc br bt :
  blocks_of_env elements_ge (entropy_frame_env bl bo bc br bt) =
  [(bo, 0, 40); (bc, 0, 32); (bl, 0, 16); (bt, 0, 32); (br, 0, 32)].
Proof.
  unfold blocks_of_env.
  change ([(bo, 0, sizeof elements_ge (Tstruct _outpoint noattr));
    (bc, 0, sizeof elements_ge (Tstruct _sha256_midstate noattr));
    (bl, 0, sizeof elements_ge (Tstruct _frameItem noattr));
    (bt, 0, sizeof elements_ge (Tstruct _sha256_midstate noattr));
    (br, 0, sizeof elements_ge (Tstruct _sha256_midstate noattr))] =
    [(bo, 0, 40); (bc, 0, 32); (bl, 0, 16); (bt, 0, 32); (br, 0, 32)]).
  rewrite entropy_frame_size, entropy_outpoint_size, !entropy_midstate_size. reflexivity.
Qed.
