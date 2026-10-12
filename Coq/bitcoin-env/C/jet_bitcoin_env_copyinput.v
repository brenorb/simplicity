(** Execution of [copyInput(result, input)] (bitcoin/env.c), complete: the
    compound literal, the optional annex hash, the previous transaction id,
    the spent output ([copyOutput]) and the scriptSig hash. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep C.jet_uint32_array_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model C.jet_sha_compress_call.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_add_n_init C.jet_sha_add_n_calls.
Require Import C.jet_sha_tapdata_prep C.jet_sha_ctx_abs.
Require Import C.jet_env_store_words C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_tomidstate.
Require Import C.jet_bitcoin_env_hashbuffer C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_key.
Require Import C.jet_bitcoin_env_tapenv_fill C.jet_bitcoin_env_copyoutput C.jet_bitcoin_env_copyinput_fill.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition ci_env (bCmp : block) : env := PTree.set ___compound (bCmp, SIN) empty_env.

Lemma ci_blocks bCmp : blocks_of_env sha_ge (ci_env bCmp) = [(bCmp, 0, 160)].
Proof. vm_compute. reflexivity. Qed.

Lemma sha_copyOutput_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _copyOutput = Some (sha_symbol_block _copyOutput).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_copyOutput_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _copyOutput) Ptrofs.zero) =
    Some (Internal f_copyOutput).
Proof. vm_compute; reflexivity. Qed.

Lemma ci_entry m m1 bCmp vres vin :
  Mem.alloc m 0 160 = (m1, bCmp) ->
  function_entry2 sha_ge f_copyInput [vres; vin] m (ci_env bCmp)
    (PTree.set _input vin (PTree.set _result vres (create_undef_temps (fn_temps f_copyInput)))) m1.
Proof.
  intros A1. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bCmp); [rewrite ci_sizeof_SIN; exact A1|].
    constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

Lemma ci_call_hashBuffer e le m m' (a1 a2 : expr) b1 o1 b2 o2 :
  e!_hashBuffer = None ->
  eval_expr sha_ge e le m a1 (Vptr b1 o1) -> typeof a1 = tptr MID ->
  eval_expr sha_ge e le m a2 (Vptr b2 o2) -> typeof a2 = tptr RBUF ->
  Clight2.eval_funcall sha_ge m (Internal f_hashBuffer) [Vptr b1 o1; Vptr b2 o2] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _hashBuffer (Tfunction (Tcons (tptr MID) (Tcons (tptr RBUF) Tnil)) tvoid cc_default))
       [a1; a2]) E0 le m' Out_normal.
Proof.
  intros He H1 T1 H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _hashBuffer) Ptrofs.zero)
    (vargs := [Vptr b1 o1; Vptr b2 o2]) (f := Internal f_hashBuffer).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_hashBuffer_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1|rewrite T1; reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_hashBuffer_funct.
  - reflexivity.
  - exact HC.
Qed.

Lemma ci_call_copyOutput e le m m' (a1 a2 : expr) b1 o1 b2 o2 :
  e!_copyOutput = None ->
  eval_expr sha_ge e le m a1 (Vptr b1 o1) -> typeof a1 = tptr SOUT ->
  eval_expr sha_ge e le m a2 (Vptr b2 o2) -> typeof a2 = tptr ROUT ->
  Clight2.eval_funcall sha_ge m (Internal f_copyOutput) [Vptr b1 o1; Vptr b2 o2] E0 m' Vundef ->
  Clight2.exec_stmt sha_ge e le m
    (Scall None (Evar _copyOutput (Tfunction (Tcons (tptr SOUT) (Tcons (tptr ROUT) Tnil)) tvoid cc_default))
       [a1; a2]) E0 le m' Out_normal.
Proof.
  intros He H1 T1 H2 T2 HC. change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _copyOutput) Ptrofs.zero)
    (vargs := [Vptr b1 o1; Vptr b2 o2]) (f := Internal f_copyOutput).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact sha_copyOutput_symbol]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [exact H1|rewrite T1; reflexivity|].
    eapply eval_Econs; [exact H2|rewrite T2; reflexivity|apply eval_Enil].
  - exact sha_copyOutput_funct.
  - reflexivity.
  - exact HC.
Qed.

(** A raw buffer structure at [(b, o)]: data pointer, length, bytes. *)
Definition raw_buffer_at (m : mem) (b : block) (o : Z) (bd : block) (od : ptrofs) (bs : list int) : Prop :=
  exists len,
    Mem.load Mptr m b o = Some (Vptr bd od) /\
    Mem.load Mint32 m b (o + 8) = Some (Vint len) /\
    Z.of_nat (length bs) = Int.unsigned len /\
    Ptrofs.unsigned od + Z.of_nat (length bs) <= Ptrofs.max_unsigned /\
    Mem.valid_block m bd /\
    (forall i, (i < length bs)%nat ->
       Mem.load Mint8unsigned m bd (Ptrofs.unsigned od + Z.of_nat i) = Some (Vint (nth i bs Int.zero))).

Lemma raw_buffer_at_frame m m' b o bd od bs :
  raw_buffer_at m b o bd od bs ->
  (forall ch b' ofs, b' = b \/ b' = bd -> Mem.load ch m' b' ofs = Mem.load ch m b' ofs) ->
  (forall b', Mem.valid_block m b' -> Mem.valid_block m' b') ->
  raw_buffer_at m' b o bd od bs.
Proof.
  intros (len & H1 & H2 & H3 & H4 & H5 & H6) HL HV. exists len.
  rewrite !HL by tauto. repeat (split; [assumption|]). split; [apply HV, H5|].
  intros i Hi. rewrite HL by tauto. apply H6, Hi.
Qed.
