(** Indexed parsed-null-data loads in the actual Elements global environment. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_index_eval.
Require Import C.jet_exec.
Require Import C.jet_application_sep C.jet_elements_effects C.jet_elements_env_load.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_indexed_deref (xp ip sid : ident) : expr :=
  Ederef (Ebinop Oadd (Etempvar xp (tptr (Tstruct sid noattr))) (Etempvar ip tulong)
    (tptr (Tstruct sid noattr))) (Tstruct sid noattr).

Lemma eval_elements_indexed_field_value e le m xp ip sid sz field delta ty chunk b base r v :
  sizeof (Clight.genv_cenv elements_ge) (Tstruct sid noattr) = sz ->
  elements_field_at sid field delta -> access_mode ty = By_value chunk ->
  le!xp = Some (Vptr b (Ptrofs.repr base)) -> le!ip = Some (Vlong r) ->
  0 <= base -> 0 < sz <= 1000 -> 0 <= delta ->
  base + sz * Int64.unsigned r + delta <= Ptrofs.max_unsigned ->
  Mem.load chunk m b (base + sz * Int64.unsigned r + delta) = Some v ->
  eval_expr elements_ge e le m (Efield (elements_indexed_deref xp ip sid) field ty) v.
Proof.
  intros HS HF HT HX HI HB Hsz Hd HM HL.
  pose proof (Int64.unsigned_range r) as HR.
  assert (HP : 0 <= sz * Int64.unsigned r) by nia.
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r)))).
  { rewrite Int64.repr_unsigned. exact HI. }
  eapply eval_elements_field_value with (sid := sid) (delta := delta)
    (chunk := chunk) (ofs := Ptrofs.repr (base + sz * Int64.unsigned r)).
  - reflexivity.
  - exact HF.
  - exact HT.
  - unfold elements_indexed_deref. eapply eval_elements_index; eauto; lia.
  - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HL].
Qed.

Lemma eval_elements_indexed_nested_value e le m xp ip sid sz f1 d1 sid1 f2 d2 ty chunk b base r v :
  sizeof (Clight.genv_cenv elements_ge) (Tstruct sid noattr) = sz ->
  elements_field_at sid f1 d1 -> elements_field_at sid1 f2 d2 -> access_mode ty = By_value chunk ->
  le!xp = Some (Vptr b (Ptrofs.repr base)) -> le!ip = Some (Vlong r) ->
  0 <= base -> 0 < sz <= 1000 -> 0 <= d1 -> 0 <= d2 ->
  base + sz * Int64.unsigned r + d1 + d2 <= Ptrofs.max_unsigned ->
  Mem.load chunk m b (base + sz * Int64.unsigned r + d1 + d2) = Some v ->
  eval_expr elements_ge e le m
    (Efield (Efield (elements_indexed_deref xp ip sid) f1 (Tstruct sid1 noattr)) f2 ty) v.
Proof.
  intros HS HF1 HF2 HT HX HI HB Hsz Hd1 Hd2 HM HL.
  pose proof (Int64.unsigned_range r) as HR.
  assert (HP : 0 <= sz * Int64.unsigned r) by nia.
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r)))).
  { rewrite Int64.repr_unsigned. exact HI. }
  assert (HStruct : eval_expr elements_ge e le m
    (Efield (elements_indexed_deref xp ip sid) f1 (Tstruct sid1 noattr))
    (Vptr b (Ptrofs.repr (base + sz * Int64.unsigned r + d1)))).
  { rewrite <- (elements_ptr_add_repr (base + sz * Int64.unsigned r) d1) by lia.
    eapply eval_elements_field_struct; [reflexivity|exact HF1|].
    unfold elements_indexed_deref. eapply eval_elements_index; eauto; lia. }
  eapply eval_elements_field_value with (sid := sid1) (delta := d2)
    (chunk := chunk) (ofs := Ptrofs.repr (base + sz * Int64.unsigned r + d1)).
  - reflexivity.
  - exact HF2.
  - exact HT.
  - exact HStruct.
  - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HL].
Qed.

Lemma elements_sigOutput_pnd : elements_field_at _sigOutput _pnd 224.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_sigOutput_isNullData : elements_field_at _sigOutput _isNullData 240.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_parsedNullData_op : elements_field_at _parsedNullData _op 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_parsedNullData_len : elements_field_at _parsedNullData _len 8.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_opcode_code : elements_field_at _opcode _code 32.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_opcode_dataHash : elements_field_at _opcode _dataHash 0.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_sizeof_opcode : sizeof (Clight.genv_cenv elements_ge) (Tstruct _opcode noattr) = 36.
Proof. vm_compute; reflexivity. Qed.

Definition elements_output_ops_expr (xp : ident) : expr :=
  Efield (Efield (elements_indexed_deref xp _i _sigOutput) _pnd (Tstruct _parsedNullData noattr))
    _op (tptr (Tstruct _opcode noattr)).

Definition elements_opcode_code_expr (xp : ident) : expr :=
  Efield (elements_indexed_deref xp _j _opcode) _code tint.

Lemma eval_elements_output_ops e le m xp b base r bop opbase :
  le!xp = Some (Vptr b (Ptrofs.repr base)) -> le!_i = Some (Vlong r) ->
  0 <= base -> base + 248 * Int64.unsigned r + 224 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m b (base + 248 * Int64.unsigned r + 224) = Some (Vptr bop (Ptrofs.repr opbase)) ->
  eval_expr elements_ge e le m (elements_output_ops_expr xp) (Vptr bop (Ptrofs.repr opbase)).
Proof.
  intros HX HI HB HM HL. unfold elements_output_ops_expr.
  eapply eval_elements_indexed_nested_value with (sz := 248) (d1 := 224) (d2 := 0) (chunk := Mptr);
    [exact elements_sizeof_sigOutput|exact elements_sigOutput_pnd|exact elements_parsedNullData_op|
     reflexivity|exact HX|exact HI|exact HB|lia|lia|lia|lia|].
  replace (base + 248 * Int64.unsigned r + 224 + 0) with (base + 248 * Int64.unsigned r + 224) by lia.
  exact HL.
Qed.

Lemma eval_elements_opcode_code e le m xp b base r code :
  le!xp = Some (Vptr b (Ptrofs.repr base)) -> le!_j = Some (Vlong r) ->
  0 <= base -> base + 36 * Int64.unsigned r + 32 <= Ptrofs.max_unsigned ->
  Mem.load Mint32 m b (base + 36 * Int64.unsigned r + 32) = Some (Vint code) ->
  eval_expr elements_ge e le m (elements_opcode_code_expr xp) (Vint code).
Proof.
  intros HX HI HB HM HL. unfold elements_opcode_code_expr.
  eapply eval_elements_indexed_field_value with (sz := 36) (delta := 32) (chunk := Mint32);
    [exact elements_sizeof_opcode|exact elements_opcode_code|reflexivity|exact HX|exact HI|exact HB|lia|lia|exact HM|exact HL].
Qed.

Definition elements_null_data_reload (t1 t2 t3 t4 : ident) : statement :=
  Ssequence
    (Sset t1 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      _tx (tptr (Tstruct _elementsTransaction noattr))))
    (Ssequence
      (Sset t2 (Efield (Ederef (Etempvar t1 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) _output (tptr (Tstruct _sigOutput noattr))))
      (Ssequence (Sset t3 (elements_output_ops_expr t2)) (Sset t4 (elements_opcode_code_expr t3)))).

Definition elements_null_data_reload_temps t1 t2 t3 t4 bt txbase bout outbase bop opbase code le :=
  PTree.set t4 (Vint code) (PTree.set t3 (Vptr bop (Ptrofs.repr opbase))
    (PTree.set t2 (Vptr bout (Ptrofs.repr outbase)) (PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) le))).

Lemma elements_null_data_reload_temps_other t1 t2 t3 t4 bt txbase bout outbase bop opbase code le k :
  ~ In k [t1; t2; t3; t4] ->
  (elements_null_data_reload_temps t1 t2 t3 t4 bt txbase bout outbase bop opbase code le)!k = le!k.
Proof.
  intros H. unfold elements_null_data_reload_temps.
  repeat rewrite PTree.gso by (simpl in H; intuition congruence). reflexivity.
Qed.

Lemma exec_elements_null_data_reload e le m t1 t2 t3 t4 be ebase bt txbase bout outbase bop opbase i j code :
  (forall t, In t [t1; t2; t3; t4] -> t <> _i /\ t <> _j /\ t <> _env /\ t <> _dst) ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_i = Some (Vlong i) -> le!_j = Some (Vlong j) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 16 <= Ptrofs.max_unsigned ->
  0 <= outbase -> outbase + 248 * Int64.unsigned i + 232 <= Ptrofs.max_unsigned ->
  0 <= opbase -> opbase + 36 * Int64.unsigned j + 36 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) ->
  Mem.load Mptr m bout (outbase + 248 * Int64.unsigned i + 224) = Some (Vptr bop (Ptrofs.repr opbase)) ->
  Mem.load Mint32 m bop (opbase + 36 * Int64.unsigned j + 32) = Some (Vint code) ->
  Clight2.exec_stmt elements_ge e le m (elements_null_data_reload t1 t2 t3 t4) E0
    (elements_null_data_reload_temps t1 t2 t3 t4 bt txbase bout outbase bop opbase code le) m Out_normal.
Proof.
  intros Hsafe Henv Hi Hj He0 HeM Ht0 HtM Ho0 HoM Hp0 HpM L1 L2 L3 L4.
  pose proof (Hsafe t1 (or_introl eq_refl)) as (H1i & H1j & H1e & H1d).
  pose proof (Hsafe t2 (or_intror (or_introl eq_refl))) as (H2i & H2j & H2e & H2d).
  pose proof (Hsafe t3 (or_intror (or_intror (or_introl eq_refl)))) as (H3i & H3j & H3e & H3d).
  set (le1 := PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) le).
  set (le2 := PTree.set t2 (Vptr bout (Ptrofs.repr outbase)) le1).
  set (le3 := PTree.set t3 (Vptr bop (Ptrofs.repr opbase)) le2).
  unfold elements_null_data_reload, elements_null_data_reload_temps. fold le1 le2 le3.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le1).
  - apply exec_set.
    eapply eval_elements_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
    + reflexivity.
    + exact elements_txEnv_tx.
    + reflexivity.
    + apply eval_elements_deref_struct; exact Henv.
    + rewrite elements_ptr_add_repr by lia. replace (ebase + 0) with ebase by lia.
      apply elements_loadv_repr; [lia|exact L1].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le2).
    + apply exec_set.
      eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := 8) (chunk := Mptr).
      * reflexivity.
      * exact elements_elementsTransaction_output.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold le1; apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact L2].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := le3).
      * apply exec_set. eapply eval_elements_output_ops with (base := outbase) (r := i);
          [unfold le2; apply PTree.gss| |exact Ho0|lia|exact L3].
        unfold le2, le1. rewrite !PTree.gso by congruence. exact Hi.
      * apply exec_set. eapply eval_elements_opcode_code with (base := opbase) (r := j);
          [unfold le3; apply PTree.gss| |exact Hp0|lia|exact L4].
        unfold le3, le2, le1. rewrite !PTree.gso by congruence. exact Hj.
Qed.

(** Append to the right spine without changing the generated statement shape. *)
Fixpoint elements_append_stmt (s tail : statement) : statement :=
  match s with
  | Ssequence a b => Ssequence a (elements_append_stmt b tail)
  | _ => Ssequence s tail
  end.

Lemma exec_elements_append_stmt ge s :
  forall e le m t1 le1 m1 tail t2 le2 m2 out,
  Clight2.exec_stmt ge e le m s t1 le1 m1 Out_normal ->
  Clight2.exec_stmt ge e le1 m1 tail t2 le2 m2 out ->
  Clight2.exec_stmt ge e le m (elements_append_stmt s tail) (t1 ** t2) le2 m2 out.
Proof.
  induction s; intros rho lenv mem0 tr1 lenv1 mem1 last tr2 lenv2 mem2 result HS HT; cbn [elements_append_stmt];
    try solve [eapply exec_Sseq_1; eassumption].
  inversion HS; subst; [|contradiction].
  rewrite Eapp_assoc. eapply exec_Sseq_1; [eassumption|]. eapply IHs2; eassumption.
Qed.

Definition elements_null_data_path_loads m be ebase bt txbase bout outbase bop opbase i j code : Prop :=
  Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr txbase)) /\
  Mem.load Mptr m bt (txbase + 8) = Some (Vptr bout (Ptrofs.repr outbase)) /\
  Mem.load Mptr m bout (outbase + 248 * Int64.unsigned i + 224) = Some (Vptr bop (Ptrofs.repr opbase)) /\
  Mem.load Mint32 m bop (opbase + 36 * Int64.unsigned j + 32) = Some (Vint code).

Definition elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j : list (block * Z * Z) :=
  [(be, ebase, ebase + 8); (bt, txbase + 8, txbase + 16);
   (bout, outbase + 248 * Int64.unsigned i + 224, outbase + 248 * Int64.unsigned i + 232);
   (bop, opbase + 36 * Int64.unsigned j + 32, opbase + 36 * Int64.unsigned j + 36)].

Lemma elements_null_data_path_loads_preserved m mf bd dbase bw edge cur n cells
    be ebase bt txbase bout outbase bop opbase i j code :
  0 < n -> n <= cur -> write_effect m mf bd dbase bw edge cur n cells ->
  Forall (fun '(b, lo, hi) => out_sep bd dbase bw edge cur n b lo hi)
    (elements_null_data_path_footprint be ebase bt txbase bout outbase bop opbase i j) ->
  elements_null_data_path_loads m be ebase bt txbase bout outbase bop opbase i j code ->
  elements_null_data_path_loads mf be ebase bt txbase bout outbase bop opbase i j code.
Proof.
  intros Hn HC HE HS (L1 & L2 & L3 & L4).
  unfold elements_null_data_path_footprint in HS.
  inversion HS as [|? ? S1 HS1]; subst.
  inversion HS1 as [|? ? S2 HS2]; subst.
  inversion HS2 as [|? ? S3 HS3]; subst.
  inversion HS3 as [|? ? S4 HS4]; subst. cbn beta iota in S1, S2, S3, S4.
  unfold elements_null_data_path_loads. repeat split.
  - rewrite (write_effect_env_load m mf bd dbase bw edge cur n cells cur n be ebase (ebase + 8) Mptr ebase)
      by (first [exact Hn | exact HC | exact HE | exact S1 | change (size_chunk Mptr) with 8; lia | lia]).
    exact L1.
  - rewrite (write_effect_env_load m mf bd dbase bw edge cur n cells cur n bt (txbase + 8) (txbase + 16) Mptr (txbase + 8))
      by (first [exact Hn | exact HC | exact HE | exact S2 | change (size_chunk Mptr) with 8; lia | lia]).
    exact L2.
  - rewrite (write_effect_env_load m mf bd dbase bw edge cur n cells cur n bout
      (outbase + 248 * Int64.unsigned i + 224) (outbase + 248 * Int64.unsigned i + 232)
      Mptr (outbase + 248 * Int64.unsigned i + 224))
      by (first [exact Hn | exact HC | exact HE | exact S3 | change (size_chunk Mptr) with 8; lia | lia]).
    exact L3.
  - rewrite (write_effect_env_load m mf bd dbase bw edge cur n cells cur n bop
      (opbase + 36 * Int64.unsigned j + 32) (opbase + 36 * Int64.unsigned j + 36)
      Mint32 (opbase + 36 * Int64.unsigned j + 32))
      by (first [exact Hn | exact HC | exact HE | exact S4 | change (size_chunk Mint32) with 4; lia | lia]).
    exact L4.
Qed.

