(** Actual SWU globals, never writable field premises. Derive their stored
    limbs and readonly bounds from the original program initializer and
    combine them with the already-proved inversion-modulus startup state. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight Clightdefs ClightBigstep Integers
  Memory Values Globalenvs Events Maps.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_beta_global
  C.jet_clight_readonly_frame C.jet_clight_internal_preserve C.jet_sx_mem
  C.jet_secp_multiply_finish_product C.jet_secp_swu_candidates C.jet_secp_fe_math
  C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_caller C.jet_secp_fe_inverse_state.
Import ListNotations Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition swu_constant_words (d:bool) : list int64 :=
  if d then [Int64.repr 1851399581923904;Int64.repr 2444010998637548;
    Int64.repr 1068498044522422;Int64.repr 4379325180380693;Int64.repr 146332049513091]
  else [Int64.repr 800791873586141;Int64.repr 4119177257465895;
    Int64.repr 2366603538325650;Int64.repr 248548893979605;Int64.repr 270285854395128].
Definition swu_constant_digits d i := nth i (swu_constant_words d) Int64.zero.
Definition swu_constant_id (d:bool) := if d then _d else _negc.
Definition swu_constant_var (d:bool) := if d then v_d else v_negc.
Definition swu_constant_block d : block := secp_symbol_block (swu_constant_id d).
Definition swu_constant_state d m :=
  Mem.range_perm m (swu_constant_block d) 0 40 Cur Readable /\
  (forall i,(i<5)%nat -> Mem.load Mint64 m (swu_constant_block d) (8*Z.of_nat i)=
    Some (Vlong (swu_constant_digits d i))) /\
  readonly_region_bounds m (swu_constant_block d) 0 40.
Lemma swu_constant_symbol d :
  Genv.find_symbol (genv_genv secp_ge) (swu_constant_id d)=Some (swu_constant_block d).
Proof. destruct d;vm_compute;reflexivity. Qed.
Lemma swu_constant_info d :
  Genv.find_var_info (genv_genv secp_ge) (swu_constant_block d)=Some (swu_constant_var d).
Proof. destruct d;vm_compute;reflexivity. Qed.
Lemma swu_constant_radix d :
  radix_value (swu_constant_digits d)=if d then swu_d_constant else swu_negc_constant.
Proof. destruct d;vm_compute;reflexivity. Qed.
Lemma swu_constant_limb_bounds d i : (i<5)%nat ->
  0<=Int64.unsigned (swu_constant_digits d i)<=
    if Nat.eqb i 4 then 281474976710655 else 4503599627370495.
Proof.
  intro Index;destruct d;destruct i as [|[|[|[|[|i]]]]];try lia;
    vm_compute;intuition discriminate.
Qed.

Local Lemma swu_constant_initializers d : gvar_init (swu_constant_var d)=
  [Init_int64 (swu_constant_digits d 0);Init_int64 (swu_constant_digits d 1);
   Init_int64 (swu_constant_digits d 2);Init_int64 (swu_constant_digits d 3);
   Init_int64 (swu_constant_digits d 4)].
Proof. destruct d;reflexivity. Qed.
Local Lemma swu_constant_size d : init_data_list_size (gvar_init (swu_constant_var d))=40.
Proof. destruct d;reflexivity. Qed.
Local Lemma swu_constant_permission d : Genv.perm_globvar (swu_constant_var d)=Readable.
Proof. destruct d;reflexivity. Qed.
Local Lemma swu_constant_notvolatile d : gvar_volatile (swu_constant_var d)=false.
Proof. destruct d;reflexivity. Qed.
Local Opaque secp_ge swu_constant_block swu_constant_digits.
Theorem swu_constant_initializes d m :
  Genv.init_mem jets_secp.prog=Some m -> swu_constant_state d m.
Proof.
  intro Init;pose proof (swu_constant_info d) as Info;rewrite beta_genv_projection in Info.
  destruct (Genv.init_mem_characterization jets_secp.prog _ Info Init)
    as (Range & Bounds & Loads & Bytes).
  rewrite swu_constant_size,swu_constant_permission in Range,Bounds.
  specialize (Loads (swu_constant_notvolatile d));rewrite swu_constant_initializers in Loads.
  cbn [Genv.load_store_init_data] in Loads.
  unfold swu_constant_state;split;[exact Range|];split.
  - intros i Index;destruct i as [|[|[|[|[|i]]]]];try lia;
      cbn [Z.of_nat Z.mul Z.add] in *;tauto.
  - intros pos k p;split;[exact (Bounds pos k p)|].
    intros [Pos Order];eapply Mem.perm_implies;[|exact Order];
      destruct k;[apply Mem.perm_cur_max|];apply Range;exact Pos.
Qed.
Lemma swu_constant_valid d m :
  swu_constant_state d m -> Mem.valid_block m (swu_constant_block d).
Proof. intros [Range _];eapply Mem.perm_valid_block;apply (Range 0);lia. Qed.
Lemma swu_constant_separate d m b : swu_constant_state d m ->
  Mem.perm m b 0 Cur Freeable -> b<>swu_constant_block d.
Proof.
  intros [_ [_ Bounds]] Free Same;rewrite Same in Free.
  destruct (proj1 (Bounds 0 Cur Freeable) Free) as [_ Order];inversion Order.
Qed.
Lemma swu_constant_unchanged d m mf : swu_constant_state d m ->
  Mem.unchanged_on (fun b _=>b=swu_constant_block d) m mf -> swu_constant_state d mf.
Proof.
  intros State Unchanged;pose proof (swu_constant_valid d m State) as Valid.
  destruct State as [Range [Loads Bounds]];unfold swu_constant_state;split.
  - intros pos Pos;eapply Mem.perm_unchanged_on;
      [exact Unchanged|reflexivity|apply Range;exact Pos].
  - split.
    + intros i Index;eapply Mem.load_unchanged_on;
        [exact Unchanged|intros;reflexivity|apply Loads;exact Index].
    + intros pos k p;split.
      * intro Perm;apply (proj1 (Bounds pos k p));eapply Mem.perm_unchanged_on_2;
          [exact Unchanged|reflexivity|exact Valid|exact Perm].
      * intro At;eapply Mem.perm_unchanged_on;
          [exact Unchanged|reflexivity|apply (proj2 (Bounds pos k p));exact At].
Qed.
Lemma swu_constant_preserved d m mf : swu_constant_state d m ->
  readonly_preserved m mf -> swu_constant_state d mf.
Proof.
  intros State [_ Unchanged];eapply swu_constant_unchanged;[exact State|].
  eapply Mem.unchanged_on_implies;[exact Unchanged|].
  intros b pos At Valid;subst b;split;[exact Valid|].
  apply (readonly_bounds_not_writable _ _ _ _ (proj2 (proj2 State)) pos).
Qed.

Definition swu_startup m := (forall d,swu_constant_state d m) /\ modinfo_fe_state m.
Theorem swu_startup_initial m : Genv.init_mem jets_secp.prog=Some m -> swu_startup m.
Proof.
  intro Init;split;[intro d;apply swu_constant_initializes|apply modinfo_fe_state_initial];exact Init.
Qed.
Theorem swu_startup_exists : exists m,Genv.init_mem jets_secp.prog=Some m /\ swu_startup m.
Proof.
  destruct beta_initialized_memory_exists as [m [Init _]];exists m;split;
    [exact Init|apply swu_startup_initial;exact Init].
Qed.
Lemma swu_startup_preserved m mf : swu_startup m -> readonly_preserved m mf -> swu_startup mf.
Proof.
  intros [Constants Modulus] Preserved;split.
  - intro d;apply (swu_constant_preserved d m mf (Constants d) Preserved).
  - exact (proj1 (modinfo_fe_state_preserved m mf Modulus Preserved)).
Qed.
Lemma eval_swu_constant_address d e le m : e!(swu_constant_id d)=None ->
  eval_expr secp_ge e le m
    (Eaddrof (Evar (swu_constant_id d) (Tstruct __5467 noattr)) (tptr (Tstruct __5467 noattr)))
    (Vptr (swu_constant_block d) Ptrofs.zero).
Proof.
  intro Local;apply eval_Eaddrof;apply eval_Evar_global;[exact Local|apply swu_constant_symbol].
Qed.
Lemma swu_startup_separate m b : swu_startup m -> Mem.perm m b 0 Cur Freeable ->
  (forall d,b<>swu_constant_block d) /\ b<>modinfo_fe_block.
Proof.
  intros [Constants [_ Readonly]] Free;split;
    [intro d;apply (swu_constant_separate d m b (Constants d) Free)|].
  intro Same;subst b;apply (Readonly 0);apply Mem.perm_cur_max;
    eapply Mem.perm_implies;[exact Free|constructor].
Qed.
