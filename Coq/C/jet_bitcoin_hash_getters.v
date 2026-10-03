(** Execution of the Bitcoin getters of the form
      [t = env->PTR; write32s(dst, t->HASH.s, 8)]   (script_cmr, transaction_id)
    and  [t = env->PTR; writeHash(dst, &t->HASH)]   (internal_key).
    The statement shapes are parametric in the struct and field identifiers;
    each consumer checks the actual generated body and offsets by computation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_uint32_array_init C.jet_application_sep.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_field_eval C.jet_bitcoin_effects.
Require Import C.jet_bitcoin_write32s_exec C.jet_bitcoin_write32s_layout C.jet_bitcoin_hash_write.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge.
Set Default Timeout 10.

Definition bitcoin_env_ptr_stmt ptrfield sid : statement :=
  Sset _t'1
    (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
      ptrfield (tptr (Tstruct sid noattr))).

Definition bitcoin_hash_mid_write32s ptrfield sid hashfield : statement :=
  Ssequence (bitcoin_env_ptr_stmt ptrfield sid)
    (Scall None
      (Evar _write32s (Tfunction
        (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr tuint) (Tcons tulong Tnil)))
        tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr));
       Efield (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct sid noattr))) (Tstruct sid noattr))
         hashfield (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8);
       Econst_int (Int.repr 8) tint]).

Definition bitcoin_hash_mid_writeHash ptrfield sid hashfield : statement :=
  Ssequence (bitcoin_env_ptr_stmt ptrfield sid)
    (Scall None
      (Evar _writeHash (Tfunction
        (Tcons (tptr (Tstruct _frameItem noattr))
          (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil)) tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr));
       Eaddrof (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct sid noattr))) (Tstruct sid noattr))
         hashfield (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr))]).

(** [t = env->PTR] *)
Lemma exec_bitcoin_env_ptr e le m be ebase bt tbase ptrfield pdelta sid :
  bitcoin_field_at _txEnv ptrfield pdelta ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> 0 <= pdelta -> ebase + pdelta <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + pdelta) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.exec_stmt bitcoin_ge e le m (bitcoin_env_ptr_stmt ptrfield sid) E0
    (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le) m Out_normal.
Proof.
  intros HF HE H0 HD HM HL. unfold bitcoin_env_ptr_stmt. apply exec_set.
  eapply eval_bitcoin_field_value with (sid := _txEnv) (delta := pdelta) (chunk := Mptr).
  - reflexivity.
  - exact HF.
  - reflexivity.
  - apply eval_bitcoin_deref_struct; exact HE.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

(** The address of a midstate field of the struct [t'1] points at. *)
Lemma eval_bitcoin_hash_field_addr e le m bt tbase sid hashfield hdelta :
  le!_t'1 = Some (Vptr bt (Ptrofs.repr tbase)) ->
  bitcoin_field_at sid hashfield hdelta ->
  0 <= tbase -> 0 <= hdelta -> tbase + hdelta <= Ptrofs.max_unsigned ->
  eval_expr bitcoin_ge e le m
    (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct sid noattr))) (Tstruct sid noattr))
      hashfield (Tstruct _sha256_midstate noattr))
    (Vptr bt (Ptrofs.repr (tbase + hdelta))).
Proof.
  intros HE HF H0 HD HM.
  rewrite <- (bitcoin_ptr_add_repr tbase hdelta) by lia.
  eapply eval_bitcoin_field_struct; [reflexivity|exact HF|].
  apply eval_bitcoin_deref_struct; exact HE.
Qed.

Lemma eval_bitcoin_hash_array_arg e le m bt tbase sid hashfield hdelta :
  le!_t'1 = Some (Vptr bt (Ptrofs.repr tbase)) ->
  bitcoin_field_at sid hashfield hdelta ->
  0 <= tbase -> 0 <= hdelta -> tbase + hdelta <= Ptrofs.max_unsigned ->
  eval_expr bitcoin_ge e le m
    (Efield (Efield (Ederef (Etempvar _t'1 (tptr (Tstruct sid noattr))) (Tstruct sid noattr))
      hashfield (Tstruct _sha256_midstate noattr)) _s (tarray tuint 8))
    (Vptr bt (Ptrofs.repr (tbase + hdelta))).
Proof.
  intros HE HF H0 HD HM.
  assert (Hr : Ptrofs.repr (tbase + hdelta) =
    Ptrofs.add (Ptrofs.repr (tbase + hdelta)) (Ptrofs.repr 0))
    by (rewrite Ptrofs.add_zero; reflexivity).
  rewrite Hr.
  eapply eval_bitcoin_field_array with (sid := _sha256_midstate) (delta := 0);
    [reflexivity|exact bitcoin_midstate_s|intros chunk; discriminate|reflexivity|].
  eapply eval_bitcoin_hash_field_addr; eauto.
Qed.

Lemma exec_bitcoin_hash_getter_write32s e le mc me bd dbase be ebase bt tbase
    ptrfield pdelta sid hashfield hdelta :
  e!_write32s = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> 0 <= pdelta -> ebase + pdelta <= Ptrofs.max_unsigned ->
  0 <= tbase -> 0 <= hdelta -> tbase + hdelta <= Ptrofs.max_unsigned ->
  bitcoin_field_at _txEnv ptrfield pdelta -> bitcoin_field_at sid hashfield hdelta ->
  Mem.load Mptr mc be (ebase + pdelta) = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f_write32s)
    [Vptr bd (Ptrofs.repr dbase); Vptr bt (Ptrofs.repr (tbase + hdelta)); Vlong (Int64.repr 8)]
    E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc (bitcoin_hash_mid_write32s ptrfield sid hashfield) E0
    (PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le) me Out_normal.
Proof.
  intros HW HEnv HDst He H0 HD Ht Hd Hm HF1 HF2 HL HCall.
  unfold bitcoin_hash_mid_write32s.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'1 (Vptr bt (Ptrofs.repr tbase)) le).
  - eapply exec_bitcoin_env_ptr; eauto.
  - eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _write32s) Ptrofs.zero)
      (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bt (Ptrofs.repr (tbase + hdelta));
        Vlong (Int64.repr 8)])
      (f := Internal f_write32s) (vres := Vundef).
    + reflexivity.
    + eapply eval_Elvalue.
      * apply eval_Evar_global; [exact HW|exact bitcoin_write32s_symbol].
      * apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply eval_Etempvar; rewrite PTree.gso by discriminate; exact HDst|reflexivity|].
      eapply eval_Econs;
        [eapply eval_bitcoin_hash_array_arg; [apply PTree.gss|exact HF2|lia|lia|lia]|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
    + exact bitcoin_write32s_funct.
    + reflexivity.
    + exact HCall.
Qed.
