(** Original total_fee after readHash: environment loads, complete sorted
    lookup, write64 and return. Entry/readHash/freeing and canonical fee
    construction remain separate; no public jet is registered here. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clightdefs Clight ClightBigstep Maps Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval C.jet_elements_index_eval.
Require Import C.jet_memcmp_model C.jet_elements_fee_lookup_table C.jet_elements_fee_lookup_sorted.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_encoding C.jet_wide C.jet_wide_spec C.jet_elements_effects.
Require Import C.jet_output_layout.
Require Import C.jet_elements_steps C.jet_elements_call C.jet_elements_transport.
Require C.jets.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition total_fee_midstate := Tstruct _sha256_midstate noattr.
Definition total_fee_frame := Tstruct _frameItem noattr.
Definition total_fee_locals bs ba := PTree.set _assetid (ba,total_fee_midstate)
  (PTree.set _src (bs,total_fee_frame) empty_env).
Definition total_fee_local_key := Eaddrof (Evar _assetid total_fee_midstate) (tptr total_fee_midstate).
Definition total_fee_read_stmt := Scall None
  (Evar _readHash (Tfunction (Tcons (tptr total_fee_midstate) (Tcons (tptr total_fee_frame) Tnil)) tvoid cc_default))
  [total_fee_local_key;Eaddrof (Evar _src total_fee_frame) (tptr total_fee_frame)].
Definition total_fee_env_tx := Efield
  (Ederef (Etempvar _env (tptr(Tstruct _txEnv noattr))) (Tstruct _txEnv noattr))
  _tx (tptr(Tstruct _elementsTransaction noattr)).
Definition total_fee_table_expr := Efield
  (Ederef (Etempvar _t'2 (tptr(Tstruct _elementsTransaction noattr))) (Tstruct _elementsTransaction noattr))
  _feeOutputs (tptr(tptr(Tstruct _sigOutput noattr))).
Definition total_fee_count_expr := Efield
  (Ederef (Etempvar _t'4 (tptr(Tstruct _elementsTransaction noattr))) (Tstruct _elementsTransaction noattr))
  _numFees tulong.
Definition total_fee_lookup_call := Scall (Some _t'1)
  (Evar _lookup_fee (Tfunction (Tcons (tptr total_fee_midstate)
    (Tcons (tptr(tptr(Tstruct _sigOutput noattr))) (Tcons tulong Tnil))) tulong cc_default))
  [total_fee_local_key;Etempvar _t'3 (tptr(tptr(Tstruct _sigOutput noattr)));Etempvar _t'5 tulong].
Definition total_fee_lookup_setup := Ssequence (Sset _t'2 total_fee_env_tx)
  (Ssequence (Sset _t'3 total_fee_table_expr) (Ssequence (Sset _t'4 total_fee_env_tx)
    (Ssequence (Sset _t'5 total_fee_count_expr) total_fee_lookup_call))).
Definition total_fee_write_stmt := Scall None
  (Evar _simplicity_write64 (Tfunction (Tcons (tptr total_fee_frame) (Tcons tulong Tnil)) tvoid cc_default))
  [Etempvar _dst (tptr total_fee_frame);Etempvar _t'1 tulong].
Definition total_fee_after_read := Ssequence (Ssequence total_fee_lookup_setup total_fee_write_stmt)
  (Sreturn(Some(Econst_int Int.one tint))).
Lemma total_fee_body_source : fn_body f_simplicity_total_fee=
  Ssequence (Sassign (Evar _src total_fee_frame) (Etempvar _src total_fee_frame))
    (Ssequence total_fee_read_stmt total_fee_after_read).
Proof. reflexivity. Qed.
Lemma total_fee_table_field : elements_field_at _elementsTransaction _feeOutputs 16.
Proof. vm_compute;reflexivity. Qed.
Lemma total_fee_count_field : elements_field_at _elementsTransaction _numFees 712.
Proof. vm_compute;reflexivity. Qed.
Lemma total_fee_lookup_symbol : Genv.find_symbol (Clight.genv_genv elements_ge) _lookup_fee=
  Some(elements_symbol_block _lookup_fee).
Proof. vm_compute;reflexivity. Qed.
Lemma total_fee_lookup_funct : Genv.find_funct (Clight.genv_genv elements_ge)
  (Vptr(elements_symbol_block _lookup_fee) Ptrofs.zero)=Some(Internal f_lookup_fee).
Proof. vm_compute;reflexivity. Qed.

Definition total_fee_loaded bt txbase tableval len le := PTree.set _t'5 (Vlong(Int64.repr len))
  (PTree.set _t'4 (Vptr bt (Ptrofs.repr txbase)) (PTree.set _t'3 tableval
    (PTree.set _t'2 (Vptr bt (Ptrofs.repr txbase)) le))).
Definition total_fee_ready bt txbase tableval len value le := PTree.set _t'1 (Vlong value)
  (total_fee_loaded bt txbase tableval len le).

Lemma eval_total_fee_tx e le m be ebase bt txbase :
  le!_env=Some(Vptr be (Ptrofs.repr ebase)) -> 0<=ebase -> ebase+8<=Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase=Some(Vptr bt (Ptrofs.repr txbase)) ->
  eval_expr elements_ge e le m total_fee_env_tx (Vptr bt (Ptrofs.repr txbase)).
Proof.
  intros Env Lo Max Load;unfold total_fee_env_tx.
  eapply eval_elements_field_value with (sid:=_txEnv) (delta:=0) (chunk:=Mptr).
  - reflexivity.
  - exact elements_txEnv_tx.
  - reflexivity.
  - apply eval_elements_deref_struct;exact Env.
  - rewrite elements_ptr_add_repr by lia;rewrite Z.add_0_r;apply elements_loadv_repr;[lia|exact Load].
Qed.

Lemma total_fee_loaded_ptr_cast m b ofs value : Mem.load Mptr m b ofs=Some value -> value<>Vundef ->
  sem_cast value (tptr(tptr(Tstruct _sigOutput noattr))) (tptr(tptr(Tstruct _sigOutput noattr))) m=Some value.
Proof.
  intros Load Defined;pose proof (Mem.load_type m Mptr b ofs value Load) as Typed.
  change (Val.has_type value AST.Tlong) in Typed.
  destruct value;cbn [Val.has_type] in Typed;try contradiction;reflexivity.
Qed.

Theorem exec_total_fee_lookup (Model : memcmp_model) bs ba le m be ebase bt txbase tableval key entries :
  le!_env=Some(Vptr be (Ptrofs.repr ebase)) -> 0<=ebase -> ebase+8<=Ptrofs.max_unsigned ->
  0<=txbase -> txbase+720<=Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase=Some(Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase+16)=Some tableval ->
  Mem.load Mint64 m bt (txbase+712)=Some(Vlong(Int64.repr(Z.of_nat(length entries)))) ->
  tableval<>Vundef ->
  fee_lookup_storage m (Vptr ba Ptrofs.zero) tableval key entries -> fee_lookup_sorted entries ->
  Clight2.exec_stmt elements_ge (total_fee_locals bs ba) le m total_fee_lookup_setup E0
    (total_fee_ready bt txbase tableval (Z.of_nat(length entries)) (fee_lookup_value key entries) le) m Out_normal.
Proof.
  intros Env E0 EMax T0 TMax EnvTx Table Count Defined Storage Sorted.
  set (la:=PTree.set _t'2 (Vptr bt (Ptrofs.repr txbase)) le).
  set (lb:=PTree.set _t'3 tableval la).
  set (lc:=PTree.set _t'4 (Vptr bt (Ptrofs.repr txbase)) lb).
  set (ld:=PTree.set _t'5 (Vlong(Int64.repr(Z.of_nat(length entries)))) lc).
  unfold total_fee_lookup_setup.
  eapply exec_Sseq_1 with (t1:=Events.E0) (t2:=Events.E0) (le1:=la) (m1:=m).
  - apply exec_Sset;apply eval_total_fee_tx with (be:=be) (ebase:=ebase);assumption.
  - eapply exec_Sseq_1 with (t1:=Events.E0) (t2:=Events.E0) (le1:=lb) (m1:=m).
    + apply exec_Sset;unfold total_fee_table_expr.
      eapply eval_elements_field_value with (sid:=_elementsTransaction) (delta:=16) (chunk:=Mptr).
      * reflexivity.
      * exact total_fee_table_field.
      * reflexivity.
      * apply eval_elements_deref_struct;unfold la;apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Table].
    + eapply exec_Sseq_1 with (t1:=Events.E0) (t2:=Events.E0) (le1:=lc) (m1:=m).
      * apply exec_Sset;apply eval_total_fee_tx with (be:=be) (ebase:=ebase);try assumption.
        unfold lb,la;rewrite !PTree.gso by discriminate;exact Env.
      * eapply exec_Sseq_1 with (t1:=Events.E0) (t2:=Events.E0) (le1:=ld) (m1:=m).
        -- apply exec_Sset;unfold total_fee_count_expr.
           eapply eval_elements_field_value with (sid:=_elementsTransaction) (delta:=712) (chunk:=Mint64).
           ++ reflexivity.
           ++ exact total_fee_count_field.
           ++ reflexivity.
           ++ apply eval_elements_deref_struct;unfold lc;apply PTree.gss.
           ++ rewrite elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Count].
        -- unfold total_fee_lookup_call,total_fee_ready.
           change (total_fee_loaded bt txbase tableval (Z.of_nat(length entries)) le) with ld.
           eapply exec_Scall with (vf:=Vptr(elements_symbol_block _lookup_fee) Ptrofs.zero)
             (f:=Internal f_lookup_fee)
             (vargs:=[Vptr ba Ptrofs.zero;tableval;Vlong(Int64.repr(Z.of_nat(length entries)))])
             (vres:=Vlong(fee_lookup_value key entries)).
           ++ reflexivity.
           ++ eapply eval_Elvalue;[apply eval_Evar_global;[reflexivity|exact total_fee_lookup_symbol]|].
              apply deref_loc_reference;reflexivity.
           ++ eapply eval_Econs.
              ** unfold total_fee_local_key;apply eval_Eaddrof;apply eval_Evar_local;reflexivity.
              ** reflexivity.
              ** eapply eval_Econs.
                 --- apply eval_Etempvar;unfold ld,lc,lb;rewrite !PTree.gso by discriminate;apply PTree.gss.
                 --- apply total_fee_loaded_ptr_cast with (b:=bt) (ofs:=txbase+16);assumption.
                 --- eapply eval_Econs;[apply eval_Etempvar;unfold ld;apply PTree.gss|reflexivity|constructor].
           ++ exact total_fee_lookup_funct.
           ++ reflexivity.
           ++ apply (eval_fee_lookup_sorted Model);assumption.
Qed.

Definition total_fee_cells key entries :=
  encode (decode_wide W64 (Int64.zero_ext 64 (fee_lookup_value key entries))).
Theorem exec_total_fee_after_read (Model : memcmp_model) bs ba le m be ebase bt txbase tableval key entries
  bd dbase bw edge cursor :
  le!_env=Some(Vptr be (Ptrofs.repr ebase)) -> le!_dst=Some(Vptr bd (Ptrofs.repr dbase)) ->
  0<=ebase -> ebase+8<=Ptrofs.max_unsigned -> 0<=txbase -> txbase+720<=Ptrofs.max_unsigned ->
  Mem.load Mptr m be ebase=Some(Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase+16)=Some tableval ->
  Mem.load Mint64 m bt (txbase+712)=Some(Vlong(Int64.repr(Z.of_nat(length entries)))) ->
  tableval<>Vundef ->
  fee_lookup_storage m (Vptr ba Ptrofs.zero) tableval key entries -> fee_lookup_sorted entries ->
  write_frame_at m bd dbase bw edge cursor 64 -> exists mf,
  Clight2.exec_stmt elements_ge (total_fee_locals bs ba) le m total_fee_after_read E0
    (total_fee_ready bt txbase tableval (Z.of_nat(length entries)) (fee_lookup_value key entries) le) mf
    (Out_return(Some(Vint Int.one,tint))) /\
  write_effect m mf bd dbase bw edge cursor 64 (total_fee_cells key entries).
Proof.
  intros Env Dst E0 EMax T0 TMax EnvTx Table Count Defined Storage Sorted Frame.
  pose proof (exec_total_fee_lookup Model bs ba le m be ebase bt txbase tableval key entries
    Env E0 EMax T0 TMax EnvTx Table Count Defined Storage Sorted) as Lookup.
  destruct (elements_write_wide_step W64 m bd dbase bw edge cursor (fee_lookup_value key entries) Frame)
    as (mf & Write & Effect).
  set (ready:=total_fee_ready bt txbase tableval (Z.of_nat(length entries)) (fee_lookup_value key entries) le) in *.
  assert (Written : Clight2.exec_stmt elements_ge (total_fee_locals bs ba) ready m total_fee_write_stmt
    Events.E0 ready mf Out_normal).
  { unfold total_fee_write_stmt;eapply exec_elements_helper_call with
      (id:=_simplicity_write64) (f:=jets.f_simplicity_write64)
      (vargs:=[Vptr bd (Ptrofs.repr dbase);Vlong(fee_lookup_value key entries)]) (vres:=Vundef).
    - unfold elements_core_helpers;cbn;tauto.
    - reflexivity.
    - eapply eval_Econs.
      + apply eval_Etempvar;unfold ready,total_fee_ready,total_fee_loaded;rewrite !PTree.gso by discriminate;exact Dst.
      + reflexivity.
      + eapply eval_Econs;[apply eval_Etempvar;unfold ready,total_fee_ready;apply PTree.gss|reflexivity|constructor].
    - reflexivity.
    - exact Write. }
  exists mf;split;[|exact Effect].
  unfold total_fee_after_read;eapply exec_Sseq_1 with (t1:=Events.E0) (t2:=Events.E0) (le1:=ready) (m1:=mf).
  - eapply exec_Sseq_1 with (t1:=Events.E0) (t2:=Events.E0);[exact Lookup|exact Written].
  - apply exec_Sreturn_some;constructor.
Qed.
