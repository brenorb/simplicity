(** Shared execution structure for actual Bitcoin 32-bit environment getters.
    The consumer must check the concrete function interface/body and field
    metadata; no desired function execution is assumed by the public consumer. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import C.jet_exec C.jet_frame_layout C.jets_bitcoin C.jet_bitcoin_linkage.
Require Import C.jet_bitcoin_env_read C.jet_bitcoin_version_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Lemma function_entry2_same_interface ge f g args m e le ma :
  g.(fn_vars) = f.(fn_vars) -> g.(fn_params) = f.(fn_params) -> g.(fn_temps) = f.(fn_temps) ->
  function_entry2 ge f args m e le ma -> function_entry2 ge g args m e le ma.
Proof.
  intros HV HP HT HEntry. destruct HEntry as [HVars HParams HDisjoint HAlloc HBind].
  constructor.
  - rewrite HV; exact HVars.
  - rewrite HP; exact HParams.
  - rewrite HP, HT; exact HDisjoint.
  - rewrite HV; exact HAlloc.
  - rewrite HP, HT; exact HBind.
Qed.

Definition bitcoin_getter32_body field : statement :=
  Ssequence
    (Sassign (Evar _src (Tstruct _frameItem noattr)) (Etempvar _src (Tstruct _frameItem noattr)))
    (Ssequence
      (Ssequence
        (Sset _t'1 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr)))
          (Tstruct _txEnv noattr)) _tx (tptr (Tstruct _bitcoinTransaction noattr))))
        (Ssequence
          (Sset _t'2 (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _bitcoinTransaction noattr)))
            (Tstruct _bitcoinTransaction noattr)) field tulong))
          (Scall None (Evar _simplicity_write32
            (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tulong])))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma bitcoin_version_getter32_body :
  f_simplicity_bitcoin_version.(fn_body) = bitcoin_getter32_body _version.
Proof. reflexivity. Qed.
Lemma bitcoin_locktime_getter32_body :
  f_simplicity_bitcoin_lock_time.(fn_body) = bitcoin_getter32_body _lockTime.
Proof. reflexivity. Qed.
Lemma bitcoin_tx_locktime_field :
  match (Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction with
  | Some co => field_offset (Clight.genv_cenv bitcoin_ge) _lockTime (co_members co) = OK (472, Full)
  | None => False
  end.
Proof. vm_compute; reflexivity. Qed.

Lemma eval_bitcoin_tx_u32_field e le m bt base field delta value :
  0 <= base -> 0 <= delta -> base + delta <= Ptrofs.max_unsigned ->
  (match (Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction with
   | Some co => field_offset (Clight.genv_cenv bitcoin_ge) field (co_members co) = OK (delta, Full)
   | None => False end) ->
  le!_t'1 = Some (Vptr bt (Ptrofs.repr base)) ->
  Mem.load Mint64 m bt (base + delta) = Some (Vlong value) ->
  eval_expr bitcoin_ge e le m
    (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct _bitcoinTransaction noattr)))
      (Tstruct _bitcoinTransaction noattr)) field tulong) (Vlong value).
Proof.
  intros HB HD HM HField HE HL.
  destruct ((Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction) as [co|] eqn:HCo; [|contradiction].
  eapply eval_Elvalue.
  - eapply eval_Efield_struct with (co := co) (delta := delta).
    + eapply eval_Elvalue; [apply eval_Ederef, eval_Etempvar; exact HE|].
      apply deref_loc_copy; reflexivity.
    + reflexivity.
    + exact HCo.
    + exact HField.
  - apply deref_loc_value with (chunk := Mint64); [reflexivity|].
    unfold Mem.loadv, Ptrofs.add.
    rewrite (Ptrofs.unsigned_repr base) by lia.
    rewrite (Ptrofs.unsigned_repr delta) by lia.
    rewrite Ptrofs.unsigned_repr by lia; exact HL.
Qed.

Lemma eval_bitcoin_getter32_composes f field delta m ma mc me mf bl bd dbase bs sbase
    be ebase bt txbase value bytes :
  f.(fn_vars) = f_simplicity_bitcoin_version.(fn_vars) ->
  f.(fn_params) = f_simplicity_bitcoin_version.(fn_params) ->
  f.(fn_temps) = f_simplicity_bitcoin_version.(fn_temps) ->
  f.(fn_return) = tbool -> f.(fn_body) = bitcoin_getter32_body field ->
  (match (Clight.genv_cenv bitcoin_ge)!_bitcoinTransaction with
   | Some co => field_offset (Clight.genv_cenv bitcoin_ge) field (co_members co) = OK (delta, Full)
   | None => False end) ->
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  0 <= ebase <= Ptrofs.max_unsigned -> 0 <= txbase -> 0 <= delta ->
  txbase + delta <= Ptrofs.max_unsigned ->
  Mem.alloc m 0 16 = (ma,bl) -> Mem.loadbytes ma bs sbase 16 = Some bytes ->
  Mem.storebytes ma bl 0 bytes = Some mc ->
  Mem.load Mptr mc be ebase = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 mc bt (txbase + delta) = Some (Vlong value) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong value] E0 me Vundef ->
  Mem.free me bl 0 16 = Some mf ->
  Clight2.eval_funcall bitcoin_ge m (Internal f)
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); Vptr be (Ptrofs.repr ebase)]
    E0 mf (Vint Int.one).
Proof.
  intros HV HP HT HRet HBody HField HB HS HD HE HTbase HDlt HTMax HA HL SC HEnv HValue HW HF.
  set (env := Vptr be (Ptrofs.repr ebase)).
  set (le := bitcoin_version_temps env bd dbase bs sbase).
  set (letx := PTree.set _t'1 (Vptr bt (Ptrofs.repr txbase)) le).
  set (ready := bitcoin_version_ready env bd dbase bs sbase bt txbase value).
  eapply eval_funcall_internal with (e := bitcoin_version_locals bl) (le1 := le) (le2 := ready)
    (m1 := ma) (m2 := me) (out := Out_return (Some (Vint Int.one, tint))).
  - eapply function_entry2_same_interface with (f := f_simplicity_bitcoin_version);
      [exact HV|exact HP|exact HT|apply bitcoin_version_entry; exact HA].
  - rewrite HBody. unfold bitcoin_getter32_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le).
    + eapply exec_bitcoin_version_copy; [exact HB|exact HS|exact HD|reflexivity|exact HL|exact SC].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := ready).
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := letx).
        -- apply exec_set. eapply eval_bitcoin_env_tx; [exact HE|reflexivity|exact HEnv].
        -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := ready).
           ++ apply exec_set. eapply eval_bitcoin_tx_u32_field;
                [exact HTbase|exact HDlt|exact HTMax|exact HField|reflexivity|exact HValue].
           ++ eapply call_bitcoin_version_write32; [reflexivity|reflexivity|reflexivity|exact HW].
      * apply exec_Sreturn_some, eval_Econst_int.
  - rewrite HRet. cbn; split; [discriminate|reflexivity].
  - change (Mem.free_list me [(bl,0,16)] = Some mf). cbn. rewrite HF; reflexivity.
Qed.
