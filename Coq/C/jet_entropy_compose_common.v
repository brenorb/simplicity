(** Actual straight-line bodies and their small-step composition interfaces.
    Call/store/free premises here are internal; Local must derive them from
    the initial public frame contract before claiming jet equivalence. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Values Events Globalenvs.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_sha_program.
Require Import C.jet_elements_calc_field_eval C.jet_elements_support_sha_linkage.
Require Import C.jet_frame_layout C.jet_frame_copy C.jet_struct_copy_loads.
Require Import C.jet_exec.
Require Import C.jet_entropy_frame_entry.

Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition calc_mid : type := Tstruct _sha256_midstate noattr.

Definition calc_mid_ptr : type := tptr calc_mid.

Definition calc_fr : type := Tstruct _frameItem noattr.

Definition calc_cc := {| cc_vararg := None; cc_unproto := false; cc_structret := true |}.

Definition calc_copy_src : statement := Sassign (Evar _src calc_fr) (Etempvar _src calc_fr).

Definition calc_copy_result : statement := Sassign (Evar _result calc_mid) (Evar __res calc_mid).

Definition calc_write : statement :=
  Scall None (Evar _writeHash (Tfunction (Tcons (tptr calc_fr) (Tcons calc_mid_ptr Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr calc_fr); Eaddrof (Evar _result calc_mid) calc_mid_ptr].

Lemma calc_mid_align : alignof_blockcopy elements_ge calc_mid = 4.
Proof. vm_compute; reflexivity. Qed.

Lemma calc_local_addr e le m id b :
  e!id = Some (b, calc_mid) ->
  eval_expr elements_ge e le m (Eaddrof (Evar id calc_mid) calc_mid_ptr) (Vptr b Ptrofs.zero).
Proof. intro HE. apply eval_Eaddrof, eval_Evar_local. exact HE. Qed.

Lemma calc_local_array e le m id b :
  e!id = Some (b, calc_mid) ->
  eval_expr elements_ge e le m (Efield (Evar id calc_mid) _s (tarray tuint 8)) (Vptr b Ptrofs.zero).
Proof. intro HE. rewrite <- elements_sha_genv. apply calc_eval_local_mid_s. exact HE. Qed.

Lemma exec_calc_result_copy e le m mf br bt bytes :
  e!_result = Some (br, calc_mid) -> e!__res = Some (bt, calc_mid) -> br <> bt ->
  Mem.loadbytes m bt 0 32 = Some bytes -> Mem.storebytes m br 0 bytes = Some mf ->
  Clight2.exec_stmt elements_ge e le m calc_copy_result E0 le mf Out_normal.
Proof.
  intros HR HT HN HL HS. unfold calc_copy_result. eapply exec_Sassign_copy.
  - apply eval_Evar_local. exact HR.
  - eapply eval_Elvalue; [apply eval_Evar_local; exact HT|apply deref_loc_copy; reflexivity].
  - reflexivity.
  - eapply assign_loc_copy with (b' := bt) (ofs' := Ptrofs.zero) (bytes := bytes); cbn [typeof].
    + reflexivity.
    + intros _. rewrite calc_mid_align. change (4 | 0). exists 0; reflexivity.
    + intros _. rewrite calc_mid_align. change (4 | 0). exists 0; reflexivity.
    + left; congruence.
    + unfold calc_mid. rewrite entropy_midstate_size. exact HL.
    + exact HS.
Qed.

Lemma exec_source_copy e le m mc bl bs sbase bytes :
  e!_src = Some (bl, calc_fr) ->
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt elements_ge e le m calc_copy_src E0 le mc Out_normal.
Proof.
  intros HE HB HS HN HL HBytes HStore.
  assert (HO : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase) by
    (apply Ptrofs.unsigned_repr; unfold frame_base_valid in HB; lia).
  unfold calc_copy_src. eapply exec_Sassign_copy.
  - apply eval_Evar_local. exact HE.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite HO. exact HS.
    + intros _. change (8 | 0). exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes). rewrite HO. exact HBytes.
    + exact HStore.
Qed.

Lemma calc_write_symbol :
  Genv.find_symbol (Clight.genv_genv elements_ge) _writeHash = Some (elements_symbol_block _writeHash).
Proof. vm_compute; reflexivity. Qed.

Lemma calc_write_funct :
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block _writeHash) Ptrofs.zero) = Some (Internal f_writeHash).
Proof. vm_compute; reflexivity. Qed.

Lemma exec_calc_write e le m mf br bd dbase :
  e!_writeHash = None -> e!_result = Some (br, calc_mid) ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall elements_ge m (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr br Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt elements_ge e le m calc_write E0 le mf Out_normal.
Proof.
  intros HNone HR HD HC. unfold calc_write. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block _writeHash) Ptrofs.zero) (f := Internal f_writeHash)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr br Ptrofs.zero]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact HNone|exact calc_write_symbol]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HD|reflexivity|].
    eapply eval_Econs; [apply calc_local_addr; exact HR|reflexivity|apply eval_Enil].
  - exact calc_write_funct.
  - reflexivity.
  - exact HC.
Qed.
