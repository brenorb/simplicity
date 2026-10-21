(** Statement adapters for the two optional hash branches of input_hash. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Values Memory Events.
Require Import C.jet_exec C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval.
Require Import C.jet_elements_index_eval C.jet_elements_sha_program C.jet_elements_env_tx_calls.
Require Import C.jet_elements_support_sha_linkage C.jet_elements_support_sha_add_n_init.
Require Import C.jet_elements_single_input_payload.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64 sha_ge elements_ge.
Set Default Timeout 15.
Local Notation IT := (Tstruct _sigInput noattr).

Definition eih_input_field (f : ident) (t : type) : expr :=
  Efield (Ederef (Etempvar _input (tptr IT)) IT) f t.

Definition eih_uchar_stmt (x : int) : statement :=
  Scall None (Evar _sha256_uchar (Tfunction (Tcons CTXP (Tcons tuchar Tnil)) tbool cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Econst_int x tint].

Definition eih_hash_stmt (f : ident) : statement :=
  Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
    [Eaddrof (Evar _ctx CTX) CTXP; Eaddrof (eih_input_field f MID) (tptr MID)].

Definition eih_optional_stmt (temp flag field : ident) : statement :=
  Ssequence (Sset temp (eih_input_field flag tbool))
    (Sifthenelse (Etempvar temp tbool)
      (Ssequence (eih_uchar_stmt Int.one) (eih_hash_stmt field))
      (eih_uchar_stmt Int.zero)).

Lemma eih_uchar_stmt_exec e le m mf bx x vr :
  e!_sha256_uchar = None -> e!_ctx = Some (bx, CTX) ->
  Int.zero_ext 8 x = x ->
  Clight2.eval_funcall sha_ge m (Internal f_sha256_uchar)
    [Vptr bx Ptrofs.zero; Vint x] E0 mf vr ->
  Clight2.exec_stmt sha_ge e le m (eih_uchar_stmt x) E0 le mf Out_normal.
Proof.
  intros HG HC HX HF. change le with (set_opttemp None vr le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchar) Ptrofs.zero)
    (vargs := [Vptr bx Ptrofs.zero; Vint x]) (f := Internal f_sha256_uchar).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HG|exact sha_uchar_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact HC|reflexivity|].
    eapply eval_Econs; [apply eval_Econst_int|change (Some (Vint (Int.zero_ext 8 x)) = Some (Vint x)); rewrite HX; reflexivity|apply eval_Enil].
  - exact sha_uchar_funct.
  - reflexivity.
  - exact HF.
Qed.

Lemma eih_optional_stmt_exec temp flag field df dh e le m mf bx bin ofs h :
  temp <> _input ->
  elements_field_at _sigInput flag df -> elements_field_at _sigInput field dh ->
  0 <= df -> df < 544 -> 0 <= dh -> dh + 32 <= 544 ->
  0 <= ofs -> ofs + 544 <= Ptrofs.max_unsigned ->
  e!_sha256_uchar = None -> e!_sha256_hash = None -> e!_ctx = Some (bx, CTX) ->
  le!_input = Some (Vptr bin (Ptrofs.repr ofs)) ->
  Mem.load Mint8unsigned m bin (ofs + df) =
    Some (Vint (bit_int (match h with Some _ => true | None => false end))) ->
  eih_optional_calls bx bin (ofs + dh) h m mf ->
  Clight2.exec_stmt sha_ge e le m (eih_optional_stmt temp flag field) E0
    (PTree.set temp (Vint (bit_int (match h with Some _ => true | None => false end))) le) mf Out_normal.
Proof.
  intros HT HFlag HField Hdf0 Hdf1 Hdh0 Hdh1 Ho HM HG1 HG2 HC HI HL HCalls.
  set (le1 := PTree.set temp (Vint (bit_int (match h with Some _ => true | None => false end))) le).
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := m).
  { apply exec_Sset.
    eapply eval_elements_field_value with (sid := _sigInput) (delta := df) (chunk := Mint8unsigned).
    - reflexivity.
    - exact HFlag.
    - reflexivity.
    - apply eval_elements_deref_struct. exact HI.
    - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HL]. }
  assert (HI1 : le1!_input = Some (Vptr bin (Ptrofs.repr ofs))).
  { unfold le1. rewrite PTree.gso by (intro E; apply HT; symmetry; exact E). exact HI. }
  assert (HCond : eval_expr sha_ge e le1 m (Etempvar temp tbool)
    (Vint (bit_int (match h with Some _ => true | None => false end)))).
  { apply eval_Etempvar. unfold le1. apply PTree.gss. }
  destruct h as [h|]; cbn [eih_optional_calls] in HCalls.
  - destruct HCalls as (mi & vr & CU & CH).
    eapply exec_Sifthenelse with (v1 := Vint Int.one) (b := true);
      [exact HCond|reflexivity|].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le1) (m1 := mi).
    { eapply eih_uchar_stmt_exec; [exact HG1|exact HC|reflexivity|exact CU]. }
    apply (mt_call_hash e le1 mi mf _ctx bx (Eaddrof (eih_input_field field MID) (tptr MID))
      bin (Ptrofs.repr (ofs + dh))); [exact HG2|exact HC| |reflexivity|exact CH].
    eapply eval_Eaddrof. rewrite <- (elements_ptr_add_repr ofs dh) by lia.
    eapply eval_elements_field_lvalue; [reflexivity|exact HField|].
    apply eval_elements_deref_struct. exact HI1.
  - destruct HCalls as [vr CU].
    eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false);
      [exact HCond|reflexivity|].
    eapply eih_uchar_stmt_exec; [exact HG1|exact HC|reflexivity|exact CU].
Qed.
