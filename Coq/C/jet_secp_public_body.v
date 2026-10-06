(** Composition of the unchanged secp public jet body with checked helper calls. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import C.jet_exec C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_public_copy.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition secp_frame_type : type := Tstruct jets_secp._frameItem noattr.
Definition secp_field_type : type := Tstruct jets_secp.__5467 noattr.
Definition secp_public_read_stmt : statement :=
  Scall None
    (Evar jets_secp._read_fe (Tfunction
      (Tcons (tptr secp_field_type) (Tcons (tptr secp_frame_type) Tnil)) tvoid cc_default))
    [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._src secp_frame_type) (tptr secp_frame_type)].
Definition secp_public_write_stmt : statement :=
  Scall None
    (Evar jets_secp._write_fe (Tfunction
      (Tcons (tptr secp_frame_type) (Tcons (tptr secp_field_type) Tnil)) tvoid cc_default))
    [Etempvar jets_secp._dst (tptr secp_frame_type);
     Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type)].
Definition secp_fe_normalize_rest : statement :=
  Ssequence secp_public_read_stmt
    (Ssequence secp_public_write_stmt (Sreturn (Some (Econst_int (Int.repr 1) tint)))).
Lemma secp_fe_normalize_body :
  fn_body f_simplicity_fe_normalize =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) secp_fe_normalize_rest.
Proof. reflexivity. Qed.
(** Compositional call lemmas: downstream results must derive these helper
    executions from frame/storage preconditions. *)
Lemma exec_secp_public_read le m mf bl ba :
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_public_read_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct secp_public_helper_symbols as [HRS [HRF [HWS HWF]]].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._read_fe) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero]) (f := Internal f_read_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HRS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HRF.
  - reflexivity.
  - exact HCall.
Qed.
Lemma exec_secp_public_write le m mf bl ba bd dbase :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_public_write_stmt E0 le mf Out_normal.
Proof.
  intros HDst HCall; destruct secp_public_helper_symbols as [HRS [HRF [HWS HWF]]].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._write_fe) Ptrofs.zero)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero]) (f := Internal f_write_fe) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HWS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Etempvar; exact HDst.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * apply eval_Enil.
  - exact HWF.
  - reflexivity.
  - exact HCall.
Qed.

Require Import C.jet_sx_state C.jet_sx_exec C.jet_sx_mem C.jet_secp_frame C.jet_secp_fe_nv C.jet_secp_fe_math.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_encoding C.jet_frame_inv.
Require Simplicity.Ty Simplicity.Word Simplicity.Alg Simplicity.Translate.
Require Import C.jet_secp_wrapper_run C.jet_secp_local_regions C.jet_secp_local_call.
Require Import C.jet_secp_canonical_normalize.
Local Opaque canonical_fe_normalize Simplicity.Translate.encode.
Lemma no_local_read_foot ba bl bi edge b pos :
  b <> ba -> b <> bl ->
  ~ foot [(ba,0);(bl,0)] (map rshape (local_read_initial_regs bi edge)) b pos.
Proof.
  intros HA HL [r [s [d [ch [HGet [_ [HBlock _]]]]]]].
  destruct r as [|[|r]].
  - change (b = ba) in HBlock; contradiction.
  - change (b = bl) in HBlock; contradiction.
  - cbn [local_read_initial_regs map nth_error] in HGet; destruct r; discriminate.
Qed.
Definition secp_locals_outside m0 bd bw bi ba bl : block -> Z -> Prop :=
  fun b _ => b <> ba /\ b <> bl /\ ~ extA m0 bd bw bi b.
Theorem exec_secp_fe_normalize_rest_canonical le m0 bd dbase bw outedge cursor N bi edge rc
    (value : Ty.tySem (Word.Word 8)) m ba bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (map Some (frame_input_word_bits value)) ->
  0 <= rc -> rc + 256 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bl 0 16 Cur Freeable ->
  frame_fields_at m bl 0 bi edge rc -> ba <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits value) rc) [] m ->
  exists mw,
    Clight2.exec_stmt secp_ge (secp_public_env bl ba) le m secp_fe_normalize_rest E0 le mw
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mw true
      (Simplicity.Translate.encode (@canonical_fe_normalize Alg.CoreFunSem value)) /\
    Mem.range_perm mw ba 0 40 Cur Freeable /\ Mem.range_perm mw bl 0 16 Cur Freeable /\
    lframe (secp_locals_outside m0 bd bw bi ba bl) m mw.
Proof.
  intros HDst HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv.
  destruct (eval_local_read_fe_canonical m0 bd dbase bw outedge cursor N bi edge rc value m ba bl
    HOutput HInput HCursor HMax HFieldFree HFrameFree HFields HSeparate HSep HInv)
    as [mr [HRead [HField [HFreeA [HFreeL [HReadInv HReadFrame]]]]]].
  destruct (eval_local_write_fe_after_read m0 bd dbase bw outedge cursor N bi edge rc value mr ba bl
    HOutput HField HFreeA HFreeL HSeparate HSep HReadInv)
    as [mw [HWrite [HFinal [HFinalFreeA [HFinalFreeL HWriteFrame]]]]].
  exists mw; split.
  - unfold secp_fe_normalize_rest.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := le).
    + apply exec_secp_public_read; exact HRead.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mw) (le1 := le).
      * apply exec_secp_public_write with (bd := bd) (dbase := dbase); assumption.
      * apply exec_Sreturn_some; constructor.
  - split; [exact HFinal|]; split; [exact HFinalFreeA|]; split; [exact HFinalFreeL|].
    eapply lframe_trans.
    + eapply lframe_implies; [exact HReadFrame|].
      intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
      apply no_local_read_foot; assumption.
    + eapply lframe_implies; [exact HWriteFrame|].
      intros b pos [HA [HL HE]] HValid; split; [exact HValid|]; split; [|exact HE].
      apply no_local_write_foot; assumption.
Qed.
