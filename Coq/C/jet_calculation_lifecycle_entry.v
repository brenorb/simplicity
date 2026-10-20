(** Four-local entry shared by the three actual calculation frame jets.
    Entry and AST shape are preparation, not an assumed jet execution. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Values Events.
Require Import C.jets_elements C.jet_elements_linkage.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition calculation_frame_vars : list (ident * type) :=
  [(_src, Tstruct _frameItem noattr); (_entropy, Tstruct _sha256_midstate noattr);
   (_result, Tstruct _sha256_midstate noattr); (__res, Tstruct _sha256_midstate noattr)].

Definition calculation_frame_params : list (ident * type) :=
  [(_dst, tptr (Tstruct _frameItem noattr)); (_src, Tstruct _frameItem noattr);
   (_env, tptr (Tstruct _txEnv noattr))].

Definition calculation_frame_header (f : function) : Prop :=
  fn_vars f = calculation_frame_vars /\ fn_params f = calculation_frame_params /\
  fn_temps f = [] /\ fn_return f = tbool /\ fn_callconv f = cc_default.

Lemma calculate_asset_frame_header : calculation_frame_header f_simplicity_calculate_asset.
Proof. repeat split; reflexivity. Qed.
Lemma calculate_explicit_token_frame_header : calculation_frame_header f_simplicity_calculate_explicit_token.
Proof. repeat split; reflexivity. Qed.
Lemma calculate_confidential_token_frame_header : calculation_frame_header f_simplicity_calculate_confidential_token.
Proof. repeat split; reflexivity. Qed.

Definition calculation_frame_env (bl bh br bt : block) : env :=
  PTree.set __res (bt, Tstruct _sha256_midstate noattr)
    (PTree.set _result (br, Tstruct _sha256_midstate noattr)
      (PTree.set _entropy (bh, Tstruct _sha256_midstate noattr)
        (PTree.set _src (bl, Tstruct _frameItem noattr) empty_env))).

Definition calculation_frame_temps (env : val) bd dbase bs sbase : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (PTree.empty val))).

Lemma calculation_frame_size : sizeof elements_ge (Tstruct _frameItem noattr) = 16.
Proof. vm_compute; reflexivity. Qed.
Lemma calculation_midstate_size : sizeof elements_ge (Tstruct _sha256_midstate noattr) = 32.
Proof. vm_compute; reflexivity. Qed.

Theorem calculation_frame_entry f env m m1 m2 m3 m4 bl bh br bt bd dbase bs sbase :
  calculation_frame_header f ->
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bh) ->
  Mem.alloc m2 0 32 = (m3, br) -> Mem.alloc m3 0 32 = (m4, bt) ->
  function_entry2 elements_ge f
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
    m (calculation_frame_env bl bh br bt) (calculation_frame_temps env bd dbase bs sbase) m4.
Proof.
  intros [HVars [HParams [HTemps [HReturn HCC]]]] A1 A2 A3 A4.
  constructor.
  - rewrite HVars. change (list_norepet [_src; _entropy; _result; __res]).
    unfold _src, _entropy, _result, __res. repeat constructor; cbn; intuition discriminate.
  - rewrite HParams. change (list_norepet [_dst; _src; _env]).
    unfold _dst, _src, _env. repeat constructor; cbn; intuition discriminate.
  - rewrite HParams, HTemps. intros x y HX HY. contradiction.
  - rewrite HVars. unfold calculation_frame_vars, calculation_frame_env.
    eapply alloc_variables_cons with (m1 := m1) (b1 := bl).
    + rewrite calculation_frame_size. exact A1.
    + eapply alloc_variables_cons with (m1 := m2) (b1 := bh).
      * rewrite calculation_midstate_size. exact A2.
      * eapply alloc_variables_cons with (m1 := m3) (b1 := br).
        -- rewrite calculation_midstate_size. exact A3.
        -- eapply alloc_variables_cons with (m1 := m4) (b1 := bt).
           ++ rewrite calculation_midstate_size. exact A4.
           ++ constructor.
  - rewrite HParams, HTemps. reflexivity.
Qed.
