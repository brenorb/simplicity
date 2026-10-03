(** Actual Bitcoin input_script_hash and input_script_sig_hash jets against
    the extended primitives InputScriptHash / InputScriptSigHash.  The
    environment representation asserts that the stored hash words of input [i]
    are the abstract per-input hash. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_version_exec C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_effects.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_index_eval.
Require Import C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_ptr_then C.jet_bitcoin_indexed_scalar.
Require Import C.jet_bitcoin_hash_write C.jet_bitcoin_hash_helpers C.jet_bitcoin_indexed_ptr.
Require Import C.jet_bitcoin_script_cmr_local C.jet_bitcoin_indexed_scalar_jets C.jet_bitcoin_indexed_ptr_jets C.jet_bitcoin_ext_prim.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Set Default Timeout 60.


(** [&(xp[i]).f1.f2] where [f1] and [f2] are struct-valued fields. *)
Lemma eval_bitcoin_elem_nested_field_addr e le m t4 ip sid sz f1 d1 sid1 f2 d2 sid2 b inbase r :
  sizeof (Clight.genv_cenv bitcoin_ge) (Tstruct sid noattr) = sz ->
  bitcoin_field_at sid f1 d1 -> bitcoin_field_at sid1 f2 d2 ->
  le!t4 = Some (Vptr b (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> 0 < sz <= 1000 -> 0 <= d1 -> 0 <= d2 ->
  inbase + sz * Int64.unsigned r + d1 + d2 <= Ptrofs.max_unsigned ->
  inbase + sz * Int64.unsigned r + 1 <= Ptrofs.max_unsigned ->
  eval_expr bitcoin_ge e le m
    (Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar t4 (tptr (Tstruct sid noattr))) (Etempvar ip tulong)
      (tptr (Tstruct sid noattr))) (Tstruct sid noattr)) f1 (Tstruct sid1 noattr)) f2 (Tstruct sid2 noattr))
      (tptr (Tstruct sid2 noattr)))
    (Vptr b (Ptrofs.repr (inbase + sz * Int64.unsigned r + (d1 + d2)))).
Proof.
  intros Hsz HF1 HF2 H4 HI HB HS Hd1 Hd2 HM HM1.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r)))) by (rewrite Int64.repr_unsigned; exact HI).
  assert (Hsr : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; [lia|exact HR]).
  pose proof (eval_bitcoin_index e le m t4 ip sid sz b inbase (Int64.unsigned r) Hsz H4 HI' HB HS HR
    ltac:(clear - HM1 Hsr; lia)) as HElem.
  eapply eval_Eaddrof.
  assert (Hr : Ptrofs.repr (inbase + sz * Int64.unsigned r + (d1 + d2)) =
    Ptrofs.add (Ptrofs.add (Ptrofs.repr (inbase + sz * Int64.unsigned r)) (Ptrofs.repr d1)) (Ptrofs.repr d2)).
  { rewrite bitcoin_ptr_add_repr by (clear - HM Hd1 Hd2 Hsr HB; lia).
    rewrite bitcoin_ptr_add_repr by (clear - HM Hd1 Hd2 Hsr HB; lia).
    f_equal. lia. }
  rewrite Hr.
  eapply eval_bitcoin_field_lvalue; [reflexivity|exact HF2|].
  eapply eval_bitcoin_field_struct; [reflexivity|exact HF1|exact HElem].
Qed.

Lemma bitcoin_sigInput_scriptSigHash : bitcoin_field_at _sigInput _scriptSigHash 32.
Proof. vm_compute; reflexivity. Qed.

Lemma encode_sum_inr_hash' (w : Ty.tySem Word256) :
  @encode (Ty.Sum Ty.Unit Word256) (inr w) = Some true :: @encode Word256 w.
Proof. reflexivity. Qed.

Definition hash_elem_rep (m : mem) (b : block) (ofs : Z) (h : hash256) : Prop :=
  uint32_array_at m b ofs (hash256_reg h).

Lemma hash_elem_rep_mono m1 m2 b ofs h :
  hash_elem_rep m1 b ofs h ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 32 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) ->
  hash_elem_rep m2 b ofs h.
Proof. intros Hr Hl. eapply uint32_array_at_mono; [exact (hash256_len _)|exact Hr|exact Hl]. Qed.

Lemma hash_elem_pay bd dbase bw outedge m' bin ofs (x : hash256) cur :
  hash_elem_rep m' bin ofs x -> 0 <= ofs -> ofs + 32 <= Ptrofs.max_unsigned ->
  out_sep bd dbase bw outedge cur 256 bin ofs (ofs + 32) ->
  write_frame_at m' bd dbase bw outedge cur 256 ->
  exists me, Clight2.eval_funcall bitcoin_ge m' (Internal f_writeHash)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
    write_effect m' me bd dbase bw outedge cur 256 (hash_cells (hash256_reg x)).
Proof.
  intros Hr H0 HM HSep HF.
  destruct (eval_bitcoin_writeHash_layout m' bin ofs bd dbase bw outedge cur (hash256_reg x)
    (hash256_len x) H0 HM HSep Hr HF) as (me & HC & HE).
  exists me. split; [exact HC|exact HE].
Qed.

Lemma hash_cells_len_256 (x : hash256) : Z.of_nat (length (hash_cells (hash256_reg x))) = 256.
Proof.
  rewrite hash_cells_length. rewrite (hash256_len x). reflexivity.
Qed.

(** * input_script_hash *)

Definition bitcoin_input_script_hash_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit Word256) :=
  PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InputScriptHash.

Definition bitcoin_ext_hash_result (hs : list hash256) (a : Ty.tySem Word32) : Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match nth_error hs (Z.to_nat (toZ a)) with
  | Some h => inr (from_hash256 h)
  | None => inl tt
  end.

Lemma bitcoin_input_script_hash_sem environment a :
  @bitcoin_input_script_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = Some (bitcoin_ext_hash_result (extInScriptHash environment) a).
Proof.
  unfold bitcoin_ext_hash_result.
  assert (H : @bitcoin_input_script_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = BitcoinExt.sem BitcoinExt.InputScriptHash a environment) by reflexivity.
  rewrite H. unfold BitcoinExt.sem. cbv zeta.
  destruct (nth_error (extInScriptHash environment) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition bitcoin_input_script_hash_pexpr : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _sigOutput noattr))
    _scriptPubKey (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma bitcoin_input_script_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_input_script_hash
    (bitcoin_indexed_rest _t'5 _t'6 _numInputs
      (bitcoin_indexed_then_ptr _t'3 _t'4 _input _sigInput bitcoin_input_script_hash_pexpr
        _writeHash (Tstruct _sha256_midstate noattr)) (bitcoin_skip_stmt 256)).
Proof. repeat split; try reflexivity. apply bitcoin_ptr_disjoint. Qed.

Theorem bitcoin_input_script_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_hash bitcoin_ge ext_environment Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep extInScriptHash hash_elem_rep 160 112 0 448)
    (fun a environment => @bitcoin_input_script_hash_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_indexed_ptr_local extInScriptHash 256
    (fun h => hash_cells (hash256_reg h)) hash_elem_rep Word256
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _writeHash (Tstruct _sha256_midstate noattr)
    448 0 160 112 32 bitcoin_input_script_hash_pexpr f_writeHash f_simplicity_bitcoin_input_script_hash
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) hash_cells_len_256 ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_writeHash_symbol bitcoin_writeHash_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_input_script_hash_shape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x Hr Hl. eapply hash_elem_rep_mono; [exact Hr|exact Hl].
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    exact (hash_elem_pay bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold bitcoin_input_script_hash_pexpr.
    pose proof (eval_bitcoin_elem_nested_field_addr e le' m' _t'4 _i _sigInput 160 _txo 104 _sigOutput
      _scriptPubKey 8 _sha256_midstate bin inbase r bitcoin_sizeof_sigInput bitcoin_sigInput_txo
      bitcoin_sigOutput_scriptPubKey H4 HI Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)) as H.
    exact H.
  - intros a environment. exists (bitcoin_ext_hash_result (extInScriptHash environment) a). split.
    + apply bitcoin_input_script_hash_sem.
    + unfold bitcoin_ext_hash_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (extInScriptHash environment) (Z.to_nat (toZ a))) as [h|].
      * rewrite encode_sum_inr_hash'. rewrite encode_from_hash256. reflexivity.
      * vm_compute. reflexivity.
Qed.

(** * input_script_sig_hash *)

Definition bitcoin_input_script_sig_hash_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit Word256) :=
  PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InputScriptSigHash.

Lemma bitcoin_input_script_sig_hash_sem environment a :
  @bitcoin_input_script_sig_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = Some (bitcoin_ext_hash_result (extInScriptSigHash environment) a).
Proof.
  unfold bitcoin_ext_hash_result.
  assert (H : @bitcoin_input_script_sig_hash_spec (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    a environment = BitcoinExt.sem BitcoinExt.InputScriptSigHash a environment) by reflexivity.
  rewrite H. unfold BitcoinExt.sem. cbv zeta.
  destruct (nth_error (extInScriptSigHash environment) (Z.to_nat (toZ a))); reflexivity.
Qed.

Definition bitcoin_input_script_sig_hash_pexpr : expr :=
  Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'4 (tptr (Tstruct _sigInput noattr))) (Etempvar _i tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _scriptSigHash
    (Tstruct _sha256_midstate noattr)) (tptr (Tstruct _sha256_midstate noattr)).

Lemma bitcoin_input_script_sig_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_input_script_sig_hash
    (bitcoin_indexed_rest _t'5 _t'6 _numInputs
      (bitcoin_indexed_then_ptr _t'3 _t'4 _input _sigInput bitcoin_input_script_sig_hash_pexpr
        _writeHash (Tstruct _sha256_midstate noattr)) (bitcoin_skip_stmt 256)).
Proof. repeat split; try reflexivity. apply bitcoin_ptr_disjoint. Qed.

Theorem bitcoin_input_script_sig_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_input_script_sig_hash bitcoin_ge ext_environment Word32
    (Ty.Sum Ty.Unit Word256)
    (indexed_ptr_rep extInScriptSigHash hash_elem_rep 160 32 0 448)
    (fun a environment => @bitcoin_input_script_sig_hash_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (bitcoin_indexed_ptr_local extInScriptSigHash 256
    (fun h => hash_cells (hash256_reg h)) hash_elem_rep Word256
    _t'5 _t'6 _t'3 _t'4 _numInputs _input _sigInput _writeHash (Tstruct _sha256_midstate noattr)
    448 0 160 32 32 bitcoin_input_script_sig_hash_pexpr f_writeHash f_simplicity_bitcoin_input_script_sig_hash
    ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) hash_cells_len_256 ltac:(reflexivity) ltac:(intros bl; reflexivity)
    bitcoin_writeHash_symbol bitcoin_writeHash_funct ltac:(reflexivity)
    bitcoin_bitcoinTransaction_numInputs bitcoin_bitcoinTransaction_input
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ _ bitcoin_input_script_sig_hash_shape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x Hr Hl. eapply hash_elem_rep_mono; [exact Hr|exact Hl].
  - intros bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF.
    exact (hash_elem_pay bd dbase bw outedge m' bin ofs x cur Hr H0 HM HSep HF).
  - intros e le' m' bin inbase r H4 HI Hi0 HM. unfold bitcoin_input_script_sig_hash_pexpr.
    exact (eval_bitcoin_elem_field_addr e le' m' _t'4 _i _sigInput 160 _scriptSigHash 32 _sha256_midstate bin inbase r
      bitcoin_sizeof_sigInput bitcoin_sigInput_scriptSigHash H4 HI Hi0 ltac:(split; lia) ltac:(lia)
      ltac:(clear - HM; lia) ltac:(clear - HM; lia)).
  - intros a environment. exists (bitcoin_ext_hash_result (extInScriptSigHash environment) a). split.
    + apply bitcoin_input_script_sig_hash_sem.
    + unfold bitcoin_ext_hash_result, indexed_ptr_cells. unfold toZ32.
      destruct (nth_error (extInScriptSigHash environment) (Z.to_nat (toZ a))) as [h|].
      * rewrite encode_sum_inr_hash'. rewrite encode_from_hash256. reflexivity.
      * vm_compute. reflexivity.
Qed.
