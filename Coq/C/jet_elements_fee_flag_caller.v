(** Intermediate C execution, not the canonical hash-based outputIsFee theorem.
    The script-empty flag is represented by actual script emptiness. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_elements_prim C.jet_elements_asset_jets C.jet_elements_fee_flag_exec.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_elements_effects.
Require Import C.jet_encoding C.jet_exec C.jets_elements C.jet_elements_linkage C.jet_elements_field_eval.
Require Import C.jet_elements_index_eval C.jet_elements_steps C.jet_elements_call C.jet_elements_transport.
Require Import C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr C.jet_elements_version_exec.
Require Import C.jet_elements_indexed_tag3_exec C.jet_elements_indexed_tag3_gen C.jet_elements_wrapper.
Require Import C.jet_elements_indexed_exec C.jet_word_repr.
Require C.jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 10.

Definition processed_fee_empty (o : txOutput) : bool :=
 match txoScript o with [] => true | _::_ => false end.
Definition processed_fee_bit (o : txOutput) : bool :=
 fee_classifier (processed_fee_empty o)
  (conf_prefix (clearPrf (txoAsset o))) (conf_prefix (clearPrf (txoAmount o))).
Definition processed_fee_rep (m : mem) (b : block) (ofs : Z) (o : txOutput) : Prop :=
 Mem.load Mint8unsigned m b (ofs+241) = Some (Vint (fee_bool_int (processed_fee_empty o))) /\
 Mem.load Mint32 m b (ofs+32) = Some (Vint (conf_prefix (clearPrf (txoAsset o)))) /\
 Mem.load Mint32 m b (ofs+136) = Some (Vint (conf_prefix (clearPrf (txoAmount o)))).
Definition processed_fee_pcells (o : txOutput) : list Cell := [Some (processed_fee_bit o)].
Definition processed_fee_pointer : expr :=
 Ebinop Oadd (Etempvar _t'5 (tptr (Tstruct _sigOutput noattr)))
  (Etempvar _i tulong) (tptr (Tstruct _sigOutput noattr)).
Definition processed_fee_setup_call : statement :=
 Ssequence
  (Sset _t'4 (Efield (Ederef (Etempvar _env (tptr (Tstruct _txEnv noattr)))
   (Tstruct _txEnv noattr)) _tx (tptr (Tstruct _elementsTransaction noattr))))
  (Ssequence
   (Sset _t'5 (Efield (Ederef (Etempvar _t'4 (tptr (Tstruct _elementsTransaction noattr)))
    (Tstruct _elementsTransaction noattr)) _output (tptr (Tstruct _sigOutput noattr))))
   (Scall (Some _t'2) (Evar _isFee (Tfunction
    (Tcons (tptr (Tstruct _sigOutput noattr)) Tnil) tbool cc_default)) [processed_fee_pointer])).
Definition processed_fee_then : statement :=
 Ssequence processed_fee_setup_call
  (Scall None (Evar _writeBit (Tfunction
   (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
   [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'2 tbool]).

Lemma processed_isFee_symbol :
 Genv.find_symbol (Clight.genv_genv elements_ge) _isFee=Some (elements_symbol_block _isFee).
Proof. vm_compute;reflexivity. Qed.
Lemma processed_isFee_funct :
 Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block _isFee) Ptrofs.zero)=
 Some (Internal f_isFee).
Proof. vm_compute;reflexivity. Qed.

Lemma eval_processed_fee_pointer e le m b base r :
 le!_t'5=Some (Vptr b (Ptrofs.repr base)) -> le!_i=Some (Vlong r) ->
 0<=base -> base+248*Int64.unsigned r+248<=Ptrofs.max_unsigned ->
 eval_expr elements_ge e le m processed_fee_pointer
  (Vptr b (Ptrofs.repr (base+248*Int64.unsigned r))).
Proof.
 intros HP HI H0 HM;unfold processed_fee_pointer.
 eapply eval_Ebinop with (v1:=Vptr b (Ptrofs.repr base)) (v2:=Vlong r).
 - apply eval_Etempvar;exact HP.
 - apply eval_Etempvar;exact HI.
 - cbn [typeof];unfold sem_binary_operation.
   rewrite (sem_add_ptr_long_sizeof (Clight.genv_cenv elements_ge) (Tstruct _sigOutput noattr)
    r (Ptrofs.repr base) b 248 m elements_sizeof_sigOutput).
   replace r with (Int64.repr (Int64.unsigned r)) by apply Int64.repr_unsigned.
   rewrite elements_ptr_index_repr;[|exact H0|lia|apply Int64.unsigned_range|lia].
   rewrite Int64.unsigned_repr by apply Int64.unsigned_range_2;reflexivity.
Qed.

Lemma exec_processed_fee_then bl le m o be ebase bt txbase bin inbase r bd dbase bw edge cur :
 le!_i=Some (Vlong r) -> le!_dst=Some (Vptr bd (Ptrofs.repr dbase)) ->
 le!_env=Some (Vptr be (Ptrofs.repr ebase)) ->
 0<=ebase -> ebase+88<=Ptrofs.max_unsigned ->
 0<=txbase -> txbase+760<=Ptrofs.max_unsigned ->
 0<=inbase -> inbase+248*Int64.unsigned r+248<=Ptrofs.max_unsigned ->
 Mem.load Mptr m be (ebase+0)=Some (Vptr bt (Ptrofs.repr txbase)) ->
 Mem.load Mptr m bt (txbase+8)=Some (Vptr bin (Ptrofs.repr inbase)) ->
 processed_fee_rep m bin (inbase+248*Int64.unsigned r) o ->
 write_frame_at m bd dbase bw edge cur 1 ->
 exists lef mf,
 Clight2.exec_stmt elements_ge (elements_version_locals bl) le m processed_fee_then E0 lef mf Out_normal /\
 write_effect m mf bd dbase bw edge cur 1 (processed_fee_pcells o).
Proof.
 intros HI HD HE He0 He1 Ht0 Ht1 Hb0 Hb1 Htx Harr (Flag & Asset & Amount) HF.
 set (ofs:=inbase+248*Int64.unsigned r).
 set (la:=PTree.set _t'4 (Vptr bt (Ptrofs.repr txbase)) le).
 set (lb:=PTree.set _t'5 (Vptr bin (Ptrofs.repr inbase)) la).
 set (lc:=PTree.set _t'2 (Vint (fee_bool_int (processed_fee_bit o))) lb).
 assert (Hsetup:Clight2.exec_stmt elements_ge (elements_version_locals bl) le m
  processed_fee_setup_call E0 lc m Out_normal).
 { unfold processed_fee_setup_call.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=la).
   - apply exec_Sset.
     eapply eval_elements_field_value with (sid:=_txEnv) (delta:=0) (chunk:=Mptr).
     + reflexivity.
     + exact elements_txEnv_tx.
     + reflexivity.
     + apply eval_elements_deref_struct;exact HE.
     + rewrite elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Htx].
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lb).
     + apply exec_Sset.
       eapply eval_elements_field_value with (sid:=_elementsTransaction) (delta:=8) (chunk:=Mptr).
       * reflexivity.
       * exact elements_elementsTransaction_output.
       * reflexivity.
       * apply eval_elements_deref_struct;unfold la;apply PTree.gss.
       * rewrite elements_ptr_add_repr by lia;apply elements_loadv_repr;[lia|exact Harr].
     + eapply exec_Scall with (vf:=Vptr (elements_symbol_block _isFee) Ptrofs.zero)
        (f:=Internal f_isFee) (vargs:=[Vptr bin (Ptrofs.repr ofs)])
        (vres:=Vint (fee_bool_int (processed_fee_bit o))).
       * reflexivity.
       * eapply eval_Elvalue.
         -- apply eval_Evar_global;[reflexivity|exact processed_isFee_symbol].
         -- apply deref_loc_reference;reflexivity.
       * eapply eval_Econs.
         -- apply eval_processed_fee_pointer;[unfold lb;apply PTree.gss| |exact Hb0|exact Hb1].
            unfold lb,la;rewrite PTree.gso by discriminate;rewrite PTree.gso by discriminate;exact HI.
         -- reflexivity.
         -- apply eval_Enil.
       * exact processed_isFee_funct.
       * reflexivity.
       * apply eval_processed_isFee;[unfold ofs;pose proof (Int64.unsigned_range r);lia|exact Hb1|
           exact Flag|exact Asset|exact Amount]. }
 destruct (elements_writeBit_step m bd dbase bw edge cur (processed_fee_bit o) HF)
  as (mf & Hwrite & Effect).
 exists lc,mf;split;[|exact Effect].
 unfold processed_fee_then.
 eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m) (le1:=lc);[exact Hsetup|].
 eapply exec_elements_helper_call with (id:=_writeBit) (f:=jets.f_writeBit)
  (vargs:=[Vptr bd (Ptrofs.repr dbase);Vint (fee_bool_int (processed_fee_bit o))])
  (vres:=Vint (fee_bool_int (processed_fee_bit o))).
 - unfold elements_core_helpers;simpl;tauto.
 - reflexivity.
 - eapply eval_Econs.
   + apply eval_Etempvar;unfold lc,lb,la.
     rewrite PTree.gso by discriminate;rewrite PTree.gso by discriminate;rewrite PTree.gso by discriminate;exact HD.
   + reflexivity.
   + eapply eval_Econs.
     * apply eval_Etempvar;unfold lc;apply PTree.gss.
     * destruct (processed_fee_bit o);reflexivity.
     * apply eval_Enil.
 - reflexivity.
 - exact Hwrite.
Qed.

Lemma processed_fee_wrapper_shape : elements_wrapper_shape f_simplicity_output_is_fee
 (elements_indexed_rest_tag3 _t'6 _t'7 _numOutputs processed_fee_then (elements_skip_stmt 1)).
Proof.
 repeat split;try reflexivity.
 intros x y HX HY Hxy;cbn in HX,HY.
 repeat match goal with H:_\/_ |- _ => destruct H end;subst;
  first [contradiction|vm_compute in Hxy;discriminate|congruence].
Qed.

Definition processed_fee_result (a : Ty.tySem Word32) (environment : Elements.env) :
 Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Ty.Unit)) :=
 match nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a)) with
 | Some o => inr (if processed_fee_bit o then inr tt else inl tt)
 | None => inl tt
 end.

Theorem elements_output_fee_flag_contract :
 application_jet_local_spec_sep f_simplicity_output_is_fee elements_ge Elements.env Word32
  (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Ty.Unit))
  (indexed_ptr_rep (fun e=>sigTxOut (Elements.envTx e)) processed_fee_rep 248 0 8 704)
  (fun a environment=>Some (processed_fee_result a environment)).
Proof.
 refine (elements_indexed_gen_local_tag3 (fun e=>sigTxOut (Elements.envTx e)) 1 processed_fee_pcells
  processed_fee_rep (Ty.Sum Ty.Unit Ty.Unit) _t'6 _t'7 _numOutputs 704 8 248
  processed_fee_then f_simplicity_output_is_fee
  ltac:(repeat split;discriminate) ltac:(repeat split;discriminate) ltac:(lia)
  ltac:(intro;reflexivity) elements_elementsTransaction_numOutputs
  ltac:(split;lia) ltac:(split;lia) ltac:(split;lia)
  _ _ processed_fee_wrapper_shape ltac:(reflexivity) _ _).
 - intros m1 m2 b ofs o (Flag & Asset & Amount) Loads;repeat split.
   + apply (Loads Mint8unsigned (ofs+241) _);[lia|change (size_chunk Mint8unsigned) with 1;lia|exact Flag].
   + apply (Loads Mint32 (ofs+32) _);[lia|change (size_chunk Mint32) with 4;lia|exact Asset].
   + apply (Loads Mint32 (ofs+136) _);[lia|change (size_chunk Mint32) with 4;lia|exact Amount].
 - intros bd dbase bw edge bl le m o be ebase bt txbase bin inbase r cur
    HI HD HE He0 He1 Ht0 Ht1 Hb0 Hb1 Htx Harr Rep S1 S2 S3 HF.
   exact (exec_processed_fee_then bl le m o be ebase bt txbase bin inbase r bd dbase bw edge cur
    HI HD HE He0 He1 Ht0 Ht1 Hb0 Hb1 Htx Harr Rep HF).
 - intros a environment;exists (processed_fee_result a environment);split;[reflexivity|].
   unfold processed_fee_result,indexed_ptr_cells;change (toZ32 a) with (toZ a).
   destruct (nth_error (sigTxOut (Elements.envTx environment)) (Z.to_nat (toZ a))) as [o|].
   + unfold processed_fee_pcells;destruct (processed_fee_bit o);reflexivity.
   + reflexivity.
Qed.
