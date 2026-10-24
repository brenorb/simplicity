(** Original finite affine-conversion entry through fe_inv_var preparation.
    The complete modular-inverse call is still required, not assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_rep C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_curve_statements C.jet_secp_curve_frame.
Require Import C.jet_secp_gej_affine_arithmetic C.jet_secp_fe_inv_prefix C.jet_secp_fe_inv_statements.
Require Import C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge C.jet_secp_point_mul_storage.
Require Import C.jet_secp_modinfo_fe_global C.jet_secp_modinv_var_entry C.jet_secp_signed62_numeric.
Import ListNotations Ctypes Values Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge modinfo_fe_block.

Definition affine_entry_temps br bp := PTree.set _a (Vptr bp Ptrofs.zero)
  (PTree.set _r (Vptr br Ptrofs.zero) (create_undef_temps(fn_temps f_secp256k1_ge_set_gej_var))).
Definition affine_finite_temps br bp := PTree.set _t'1 (Vint Int.zero) (affine_entry_temps br bp).
Definition affine_flag_statement := match fn_body f_secp256k1_ge_set_gej_var with
  | Ssequence flag _=>flag | _=>Sskip end.
Definition affine_inverse_statement := curve_call _secp256k1_fe_inv_var f_secp256k1_fe_inv_var None
  [affine_point_address _z;affine_point_address _z].
Lemma affine_entry_source : fn_body f_secp256k1_ge_set_gej_var=
  Ssequence affine_flag_statement
    (Ssequence affine_inverse_statement (affine_arithmetic_context affine_finish_statement)).
Proof. reflexivity. Qed.

Lemma affine_helper_entry m m1 mi b2 b3 br bp :
  Mem.alloc m 0 40=(m1,b2) -> Mem.alloc m1 0 40=(mi,b3) ->
  function_entry2 secp_ge f_secp256k1_ge_set_gej_var [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]
    m (affine_local_env b2 b3) (affine_entry_temps br bp) mi.
Proof.
  intros A1 A2;assert(Ok:fn_okb f_secp256k1_ge_set_gej_var=true) by reflexivity.
  destruct(fn_okb_true _ Ok) as (N1 & N2 & Disjoint).
  constructor;[exact N1|exact N2|exact Disjoint| |reflexivity].
  eapply alloc_variables_cons with (m1:=m1) (b1:=b2);[exact A1|].
  eapply alloc_variables_cons with (m1:=mi) (b1:=b3);[exact A2|constructor].
Qed.

Lemma exec_affine_finite_flag le m bp b2 b3 :
  le!_a=Some(Vptr bp Ptrofs.zero) -> Mem.load Mint32 m bp 120=Some(Vint Int.zero) ->
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) le m affine_flag_statement E0
    (PTree.set _t'1 (Vint Int.zero) le) m Out_normal.
Proof.
  intros Point Flag.
  unfold affine_flag_statement;cbn [fn_body].
  eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=PTree.set _t'1 (Vint Int.zero) le).
  - apply exec_Sset.
    destruct(affine_point_layout _infinity 120 ltac:(right;right;right;left;reflexivity)) as (co & Cenv & Offset).
    eapply eval_Elvalue with (loc:=bp) (ofs:=Ptrofs.repr 120) (bf:=Full).
    + rewrite <-(Ptrofs.add_zero_l(Ptrofs.repr 120)).
      eapply eval_Efield_struct with (co:=co) (delta:=120).
      * eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact Point|apply deref_loc_copy;reflexivity].
      * reflexivity.
      * exact Cenv.
      * exact Offset.
    + eapply deref_loc_value with (chunk:=Mint32);[reflexivity|exact Flag].
  - eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false).
    + apply eval_Etempvar;apply PTree.gss.
    + reflexivity.
    + apply exec_Sskip.
Qed.

Theorem affine_entry_to_inverse_core w m bp br :
  square_input_bounds w -> fe_at m bp 80 (words5 w) ->
  Mem.load Mint32 m bp 120=Some(Vint Int.zero) -> modinfo_fe_global_rep m ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m br 0 88 Cur Freeable ->
  exists b2 b3 ma bt bs mi mf,
  function_entry2 secp_ge f_secp256k1_ge_set_gej_var [Vptr br Ptrofs.zero;Vptr bp Ptrofs.zero]
    m (affine_local_env b2 b3) (affine_entry_temps br bp) ma /\
  Clight2.exec_stmt secp_ge (affine_local_env b2 b3) (affine_entry_temps br bp) ma affine_flag_statement
    E0 (affine_finite_temps br bp) ma Out_normal /\
  eval_exprlist secp_ge (affine_local_env b2 b3) (affine_finite_temps br bp) ma
    [affine_point_address _z;affine_point_address _z] (type_of_params(fn_params f_secp256k1_fe_inv_var))
    [Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)] /\
  function_entry2 secp_ge f_secp256k1_fe_inv_var [Vptr bp(Ptrofs.repr 80);Vptr bp(Ptrofs.repr 80)] ma
    (fe_inv_env bt bs) (fe_inv_slice_temps bp 80 bp 80) mi /\
  Clight2.exec_stmt secp_ge (fe_inv_env bt bs) (fe_inv_slice_temps bp 80 bp 80) mi fe_inv_prefix
    E0 (fe_inv_slice_temps bp 80 bp 80) mf Out_normal /\
  rep (fe_inv_packed_words w) [(bs,0);(modinfo_fe_block,0)] inv_start_regs mf /\
  fe_at mf bs 0 (words5(fe_inv_packed_words w)) /\ fe_at mf bp 80 (words5 w) /\
  Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf br 0 88 Cur Freeable /\
  Mem.range_perm mf b2 0 40 Cur Freeable /\ Mem.range_perm mf b3 0 40 Cur Freeable /\
  Mem.range_perm mf bt 0 40 Cur Freeable /\ Mem.range_perm mf bs 0 40 Cur Freeable /\
  signed62_normalized(fe_inv_packed_words w) /\
  signed62_unsigned_value(fe_inv_packed_words w)=fe_inv_value w /\
  modinfo_fe_global_rep mf /\ b2<>b3 /\ ~Mem.valid_block m b2 /\ ~Mem.valid_block m b3 /\
  bt<>bs /\ ~Mem.valid_block ma bt /\ ~Mem.valid_block ma bs /\ lframe (fun _ _=>True) m mf.
Proof.
  intros Bounds Z Flag Global FP FR.
  destruct(Mem.alloc m 0 40) as (m1,b2) eqn:A1.
  destruct(Mem.alloc m1 0 40) as (ma,b3) eqn:A2.
  pose proof(Mem.fresh_block_alloc _ _ _ _ _ A1) as Fresh2.
  assert(Fresh3:~Mem.valid_block m b3).
  { intro Old;apply(Mem.fresh_block_alloc _ _ _ _ _ A2);eapply Mem.valid_block_alloc;eassumption. }
  assert(Separate:b2<>b3).
  { intro E;apply(Mem.fresh_block_alloc _ _ _ _ _ A2);rewrite <-E;eapply Mem.valid_new_block;exact A1. }
  assert(AllocFrame:lframe (fun _ _=>True) m ma).
  { eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  assert(Za:fe_at ma bp 80 (words5 w)).
  { eapply curve_keep_field_range;[reflexivity|exact Z|exact AllocFrame|];intros;exact I. }
  assert(Globala:modinfo_fe_global_rep ma).
  { eapply modinfo_fe_global_lframe;[exact Global|exact AllocFrame|];intros;exact I. }
  assert(FlagA:Mem.load Mint32 ma bp 120=Some(Vint Int.zero)).
  { rewrite(proj1 AllocFrame);[exact Flag|eapply Mem.perm_valid_block;apply(FP 0);lia|intros;exact I]. }
  assert(F2:Mem.range_perm ma b2 0 40 Cur Freeable).
  { intros pos Hr;eapply Mem.perm_alloc_1;[exact A2|];eapply Mem.perm_alloc_2;eassumption. }
  assert(F3:Mem.range_perm ma b3 0 40 Cur Freeable).
  { intros pos Hr;eapply Mem.perm_alloc_2;eassumption. }
  destruct(fe_inv_entry_to_core w ma bp 80 bp 80 Bounds Za Globala)
    as (bt & bs & mi & mf & InverseEntry & Prepare & Core & Packed & Canonical & Source & FT & FS & Normalized & Numeric & GlobalF & TS & NewT & NewS & InvFrame).
  assert(Whole:lframe (fun _ _=>True) m mf) by (eapply lframe_trans;eassumption).
  assert(FPF:Mem.range_perm mf bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FP|exact Whole|];intros;exact I. }
  assert(FRF:Mem.range_perm mf br 0 88 Cur Freeable).
  { eapply curve_keep_free;[lia|exact FR|exact Whole|];intros;exact I. }
  assert(F2F:Mem.range_perm mf b2 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F2|exact InvFrame|];intros;exact I. }
  assert(F3F:Mem.range_perm mf b3 0 40 Cur Freeable).
  { eapply curve_keep_free;[lia|exact F3|exact InvFrame|];intros;exact I. }
  exists b2,b3,ma,bt,bs,mi,mf;split;[eapply affine_helper_entry;eassumption|];split.
  - apply(exec_affine_finite_flag (affine_entry_temps br bp) ma bp b2 b3);[reflexivity|exact FlagA].
  - split.
    + eapply eval_Econs.
      * apply eval_affine_point_address;[right;right;left;reflexivity|reflexivity].
      * reflexivity.
      * eapply eval_Econs;[apply eval_affine_point_address;[right;right;left;reflexivity|reflexivity]|reflexivity|constructor].
    + repeat first[assumption|split].
Qed.
