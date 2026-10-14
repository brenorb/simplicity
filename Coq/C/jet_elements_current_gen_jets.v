(** Elements current_amount, current_pegin and current_annex_hash against
    [primitive CurrentIndex >>> assert SPEC] (Programs/Transaction.hs), as
    instances of the generic current-input theorem: two helper calls on the
    current input, resp. a flag bit followed by the hash or padding.  The
    environment words re-read between writes are part of the footprint. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_uint32_array_init.
Require Import C.jets_elements C.jet_elements_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_elements_version_exec C.jet_elements_field_eval C.jet_elements_wrapper C.jet_elements_effects.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_index_eval.
Require Import C.jet_elements_indexed_exec C.jet_elements_indexed_ptr_then C.jet_elements_indexed_scalar.
Require Import C.jet_elements_hash_write C.jet_elements_hash_helpers C.jet_elements_indexed_ptr.
Require Import C.jet_elements_script_cmr_local C.jet_elements_indexed_scalar_jets.
Require Import C.jet_elements_indexed_ptr_jets C.jet_elements_input_hash_jets C.jet_elements_asset_helper.
Require Import C.jet_elements_asset_jets C.jet_elements_amt_helper C.jet_elements_amount_jets.
Require Import C.jet_elements_issuance_helper C.jet_elements_issuance_jets C.jet_elements_issuance_amount_jets.
Require Import C.jet_elements_current_exec C.jet_elements_current_spec C.jet_elements_current_ptr.
Require Import C.jet_elements_current_ptr_jets C.jet_elements_current_gen C.jet_elements_current_input_jets.
Require Import C.jet_elements_hash_elem C.jet_elements_steps C.jet_elements_env_load C.jet_output_layout_step.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Local Notation ConfTy a := (Ty.Sum (Ty.Prod (Ty.Sum Ty.Unit Ty.Unit) Word256) a).


Lemma elements_current9_disjoint :
  list_disjoint [_dst; _src; _env] [_t'9; _t'8; _t'7; _t'6; _t'5; _t'4; _t'3; _t'2; _t'1].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

(** * current_amount *)

Definition elements_current_amount_spec {alg : Primitive.Algebra} :
    alg Ty.Unit (Ty.Prod (ConfTy Word256) (ConfTy Word64)) :=
  elements_current_spec (@elements_input_amount_spec alg).

Definition current_amount_pexpr1 : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'5 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'6 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _utxo noattr))
    _asset (Tstruct _confidential noattr)) (tptr (Tstruct _confidential noattr)).

Definition current_amount_pexpr2 : expr :=
  Eaddrof (Efield (Efield (Ederef (Ebinop Oadd (Etempvar _t'2 (tptr (Tstruct _sigInput noattr))) (Etempvar _t'3 tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr)) _txo (Tstruct _utxo noattr))
    _amt (Tstruct _confAmount noattr)) (tptr (Tstruct _confAmount noattr)).

Definition current_amount_body : statement :=
  Ssequence
    (elements_current_load3 _t'4 _t'5 _t'6 _input _sigInput
      (elements_ptr_call _asset (Tstruct _confidential noattr) current_amount_pexpr1))
    (Ssequence
      (elements_current_load3 _t'1 _t'2 _t'3 _input _sigInput
        (elements_ptr_call _amt (Tstruct _confAmount noattr) current_amount_pexpr2))
      elements_return_one).

Lemma elements_current_amount_shape :
  elements_wrapper_shape f_simplicity_current_amount
    (elements_current_gen_rest _t'7 _t'8 _t'9 _numInputs current_amount_body).
Proof. repeat split; try reflexivity. apply elements_current9_disjoint. Qed.

Definition input_amount_elem_rep (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  asset_rep m b (ofs + 168) (utxoAsset (sigTxiTxo txi)) /\
  amount_rep m b (ofs + 208) (utxoAmount (sigTxiTxo txi)).

Definition input_amount_pcells (txi : sigTxInput) : list Cell :=
  asset_pcells (utxoAsset (sigTxiTxo txi)) ++ amount_pcells (utxoAmount (sigTxiTxo txi)).

Lemma input_amount_elem_rep_pres : forall m1 m2 b ofs x, input_amount_elem_rep m1 b ofs x ->
  (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + 544 ->
    Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> input_amount_elem_rep m2 b ofs x.
Proof.
  intros m1 m2 b ofs x [Hra Hrm] Hl. split.
  - eapply asset_rep_mono; [exact Hra|]. intros chunk o v H1 H2. apply Hl; lia.
  - eapply amount_rep_mono; [exact Hrm|]. intros chunk o v H1 H2. apply Hl; lia.
Qed.

Lemma encode_pair_conf (x : Ty.tySem (ConfTy Word256)) (y : Ty.tySem (ConfTy Word64)) :
  @encode (Ty.Prod (ConfTy Word256) (ConfTy Word64)) (x, y) =
    @encode (ConfTy Word256) x ++ @encode (ConfTy Word64) y.
Proof. reflexivity. Qed.

Theorem elements_current_amount_local_spec :
  application_jet_local_spec_sep f_simplicity_current_amount elements_ge Elements.env Ty.Unit
    (Ty.Prod (ConfTy Word256) (ConfTy Word64))
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) input_amount_elem_rep 544 0 696)
    (fun a environment => @elements_current_amount_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_current_gen_local (fun e => sigTxIn (Elements.envTx e)) 516 input_amount_pcells
    input_amount_elem_rep (Ty.Prod (ConfTy Word256) (ConfTy Word64))
    _t'7 _t'8 _t'9 _numInputs 696 0 544 current_amount_body f_simplicity_current_amount
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) elements_elementsTransaction_numInputs
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    input_amount_elem_rep_pres _ elements_current_amount_shape ltac:(reflexivity) _ _).
  - intros bd dbase bw outedge bl le mc x be ebase bt txbase bin inbase ixv cur
      HEnv HDst He0 He1 Ht0 Ht1 Hi0 HiM Hl0 Hl1 Hlix [Hra Hrm] S1 S2 S4 S5 HF.
    pose proof HF as [_ [_ [_ [HCur _]]]].
    assert (Hs0 : 0 <= 544 * Int64.unsigned ixv)
      by (apply Z.mul_nonneg_nonneg; [lia|apply Int64.unsigned_range]).
    set (ofs := inbase + 544 * Int64.unsigned ixv) in *.
    set (e := elements_version_locals bl).
    assert (HFa : write_frame_at mc bd dbase bw outedge cur 258).
    { eapply write_frame_at_shorter; [|exact HF]. lia. }
    assert (S5a : out_sep bd dbase bw outedge cur 258 bin (ofs + 168) (ofs + 168 + 36)).
    { eapply out_sep_range with (lo := ofs) (hi := ofs + 544); [|lia|lia].
      eapply out_sep_sub with (cursor := cur) (count := 516); [lia|lia|lia|lia|exact S5]. }
    destruct (asset_rep_runs bd dbase bw outedge mc bin (ofs + 168) _ cur Hra ltac:(lia) ltac:(lia) S5a HFa)
      as (m1 & HC1 & E1).
    set (la := PTree.set _t'6 (Vlong ixv) (PTree.set _t'5 (Vptr bin (Ptrofs.repr inbase))
      (PTree.set _t'4 (Vptr bt (Ptrofs.repr txbase)) le))).
    assert (HEla : la!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold la. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. exact HEnv. }
    assert (HDla : la!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold la. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. exact HDst. }
    assert (HP1 : eval_expr elements_ge e la mc current_amount_pexpr1 (Vptr bin (Ptrofs.repr (ofs + 168)))).
    { unfold current_amount_pexpr1.
      exact (eval_elements_elem_nested_field_addr e la mc _t'5 _t'6 _sigInput 544 _txo 136 _utxo
        _asset 32 _confidential bin inbase ixv elements_sizeof_sigInput elements_sigInput_txo
        elements_utxo_asset ltac:(unfold la; rewrite PTree.gso by discriminate; apply PTree.gss)
        ltac:(unfold la; apply PTree.gss) Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
        ltac:(unfold ofs in *; lia) ltac:(unfold ofs in *; lia)). }
    pose proof (exec_elements_current_load3 e le _t'4 _t'5 _t'6 _input 0 _sigInput
      (elements_ptr_call _asset (Tstruct _confidential noattr) current_amount_pexpr1) mc la m1 Out_normal
      be ebase bt txbase bin inbase ixv ltac:(discriminate) ltac:(discriminate) HEnv He0 He1 Ht0
      ltac:(lia) ltac:(lia) elements_elementsTransaction_input Hl0 Hl1 Hlix
      (exec_elements_ptr_call e la mc _asset (Tstruct _confidential noattr) f_asset current_amount_pexpr1
        (ofs + 168) bd dbase bin m1 ltac:(reflexivity) ltac:(reflexivity) elements_asset_symbol
        elements_asset_funct ltac:(reflexivity) HDla HP1 HC1)) as HEx1.
    assert (HLoad1 : forall chunk b lo hi o, out_sep bd dbase bw outedge cur 516 b lo hi ->
      lo <= o -> o + size_chunk chunk <= hi -> Mem.load chunk m1 b o = Mem.load chunk mc b o).
    { intros chunk b lo hi o Hs Hlo Hhi.
      eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
        (cursor := cur) (cursor0 := cur) (count0 := 516) (n := 258)
        (cells := asset_pcells (utxoAsset (sigTxiTxo x))) (lo := lo) (hi := hi);
        [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
    assert (Hrm1 : amount_rep m1 bin (ofs + 208) (utxoAmount (sigTxiTxo x))).
    { eapply amount_rep_mono; [exact Hrm|]. intros chunk o v Hlo Hhi Hl.
      rewrite (HLoad1 chunk bin ofs (ofs + 544) o S5 ltac:(lia) ltac:(lia)). exact Hl. }
    assert (Hm0 : Mem.load Mptr m1 be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
    { rewrite (HLoad1 Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia)
        ltac:(change (size_chunk Mptr) with 8; lia)). exact Hl0. }
    assert (Hm1 : Mem.load Mptr m1 bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
    { rewrite (HLoad1 Mptr bt (txbase + 0) (txbase + 0 + 8) (txbase + 0) S4 ltac:(lia)
        ltac:(change (size_chunk Mptr) with 8; lia)). exact Hl1. }
    assert (Hmix : Mem.load Mint64 m1 be (ebase + 80) = Some (Vlong ixv)).
    { rewrite (HLoad1 Mint64 be (ebase + 80) (ebase + 88) (ebase + 80) S2 ltac:(lia)
        ltac:(change (size_chunk Mint64) with 8; lia)). exact Hlix. }
    assert (HF2 : write_frame_at m1 bd dbase bw outedge (cur - 258) 258).
    { eapply write_frame_at_after_effect with (cells := asset_pcells (utxoAsset (sigTxiTxo x))) (m := mc);
        [exact (asset_cells_length_Z _ _ (asset_words_length _))|lia|exact HF|exact E1]. }
    assert (S5b : out_sep bd dbase bw outedge (cur - 258) 258 bin (ofs + 208) (ofs + 208 + 40)).
    { eapply out_sep_range with (lo := ofs) (hi := ofs + 544); [|lia|lia].
      eapply out_sep_sub with (cursor := cur) (count := 516); [lia|lia|lia|lia|exact S5]. }
    destruct (amount_rep_runs bd dbase bw outedge m1 bin (ofs + 208) _ (cur - 258) Hrm1 ltac:(lia) ltac:(lia)
      S5b HF2) as (me & HC2 & E2).
    set (lb := PTree.set _t'3 (Vlong ixv) (PTree.set _t'2 (Vptr bin (Ptrofs.repr inbase))
      (PTree.set _t'1 (Vptr bt (Ptrofs.repr txbase)) la))).
    assert (HDlb : lb!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold lb. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. exact HDla. }
    assert (HP2 : eval_expr elements_ge e lb m1 current_amount_pexpr2 (Vptr bin (Ptrofs.repr (ofs + 208)))).
    { unfold current_amount_pexpr2.
      exact (eval_elements_elem_nested_field_addr e lb m1 _t'2 _t'3 _sigInput 544 _txo 136 _utxo
        _amt 72 _confAmount bin inbase ixv elements_sizeof_sigInput elements_sigInput_txo
        elements_utxo_amt ltac:(unfold lb; rewrite PTree.gso by discriminate; apply PTree.gss)
        ltac:(unfold lb; apply PTree.gss) Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia)
        ltac:(unfold ofs in *; lia) ltac:(unfold ofs in *; lia)). }
    pose proof (exec_elements_current_load3 e la _t'1 _t'2 _t'3 _input 0 _sigInput
      (elements_ptr_call _amt (Tstruct _confAmount noattr) current_amount_pexpr2) m1 lb me Out_normal
      be ebase bt txbase bin inbase ixv ltac:(discriminate) ltac:(discriminate) HEla He0 He1 Ht0
      ltac:(lia) ltac:(lia) elements_elementsTransaction_input Hm0 Hm1 Hmix
      (exec_elements_ptr_call e lb m1 _amt (Tstruct _confAmount noattr) f_amt current_amount_pexpr2
        (ofs + 208) bd dbase bin me ltac:(reflexivity) ltac:(reflexivity) elements_amt_symbol
        elements_amt_funct ltac:(reflexivity) HDlb HP2 HC2)) as HEx2.
    exists lb, me. split.
    + unfold current_amount_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m1) (le1 := la); [exact HEx1|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lb); [exact HEx2|].
      apply exec_elements_return_one.
    + exact (write_effect_seq mc m1 me bd dbase bw outedge cur 258 258 _ _
        (asset_cells_length_Z _ _ (asset_words_length _)) ltac:(lia) HF E1 E2).
  - intros environment.
    destruct (elements_current_sem
      (fun a e => @elements_input_amount_spec (PrimitivePrimSem option_Monad_Zero) a e)
      (fun txi => (encode_asset (utxoAsset (sigTxiTxo txi)), encode_amount (utxoAmount (sigTxiTxo txi))))
      (fun a e => elements_input_amount_sem a e) environment) as (txi & Hn & Hs).
    exists txi. eexists. split; [exact Hn|]. split; [exact Hs|].
    unfold input_amount_pcells. rewrite encode_pair_conf, encode_conf_cells, encode_amount_cells. reflexivity.
Qed.

(** * current_pegin and current_annex_hash: a flag bit, then the hash or padding *)

Lemma elements_current11_disjoint :
  list_disjoint [_dst; _src; _env]
    [_t'1; _t'11; _t'10; _t'9; _t'8; _t'7; _t'6; _t'5; _t'4; _t'3; _t'2].
Proof.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Definition cur_elem (t ip : ident) : expr :=
  Ederef (Ebinop Oadd (Etempvar t (tptr (Tstruct _sigInput noattr))) (Etempvar ip tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr).

Definition flag_hash_pexpr (hashfield : ident) : expr :=
  Eaddrof (Efield (cur_elem _t'3 _t'4) hashfield (Tstruct _sha256_midstate noattr))
    (tptr (Tstruct _sha256_midstate noattr)).

Definition flag_hash_body (flagfield hashfield : ident) : statement :=
  Ssequence
    (elements_current_load3 _t'5 _t'6 _t'7 _input _sigInput
      (Ssequence (Sset _t'8 (Efield (cur_elem _t'6 _t'7) flagfield tbool))
        (Scall (Some _t'1)
          (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'8 tbool])))
    (Sifthenelse (Etempvar _t'1 tbool)
      (elements_current_load3 _t'2 _t'3 _t'4 _input _sigInput
        (elements_ptr_call _writeHash (Tstruct _sha256_midstate noattr) (flag_hash_pexpr hashfield)))
      (elements_skip_stmt 256)).

Definition flag_hash_tail (flagfield hashfield : ident) : statement :=
  Ssequence (flag_hash_body flagfield hashfield) elements_return_one.

Definition flag_bit (b : bool) : int := if b then Int.one else Int.zero.

Definition flag_hash_rep (g : sigTxInput -> option hash256) (foff hoff : Z)
    (m : mem) (b : block) (ofs : Z) (txi : sigTxInput) : Prop :=
  Mem.load Mint8unsigned m b (ofs + foff) = Some (Vint (flag_bit (opt_is_some (g txi)))) /\
  forall h, g txi = Some h -> hash_elem_rep m b (ofs + hoff) h.

Definition flag_hash_cells (g : sigTxInput -> option hash256) (txi : sigTxInput) : list Cell :=
  match g txi with
  | Some h => [Some true] ++ hash_cells (hash256_reg h)
  | None => [Some false] ++ repeat None 256
  end.

Lemma eval_cur_elem_flag e le m t ip flagfield foff bin inbase r (v : int) :
  elements_field_at _sigInput flagfield foff -> 0 <= foff -> foff + 1 <= 544 ->
  le!t = Some (Vptr bin (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> inbase + 544 * Int64.unsigned r + 544 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bin (inbase + 544 * Int64.unsigned r + foff) = Some (Vint v) ->
  eval_expr elements_ge e le m (Efield (cur_elem t ip) flagfield tbool) (Vint v).
Proof.
  intros HFd Hf0 Hf1 HT HI HB HM HL.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r))))
    by (rewrite Int64.repr_unsigned; exact HI).
  pose proof (eval_elements_index e le m t ip _sigInput 544 bin inbase (Int64.unsigned r)
    elements_sizeof_sigInput HT HI' HB ltac:(lia) HR ltac:(lia)) as HElem.
  eapply eval_elements_field_value with (sid := _sigInput) (delta := foff) (chunk := Mint8unsigned).
  - reflexivity.
  - exact HFd.
  - reflexivity.
  - exact HElem.
  - rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact HL].
Qed.

Theorem elements_current_flag_hash_local (g : sigTxInput -> option hash256)
    (flagfield hashfield : ident) (foff hoff : Z) (f : function)
    (HFf : elements_field_at _sigInput flagfield foff) (HFh : elements_field_at _sigInput hashfield hoff)
    (Hfb : 0 <= foff /\ foff + 1 <= 544) (Hhb : 0 <= hoff /\ hoff + 32 <= 544)
    (Hshape : elements_wrapper_shape f
      (elements_current_gen_rest _t'9 _t'10 _t'11 _numInputs (flag_hash_tail flagfield hashfield)))
    (t : Ty.tySem Word32 -> Elements.env -> option (Ty.tySem (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))))
    (Hres : forall a e, t a e = Some (match nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ a)) with
      | Some txi => inr (match g txi with Some h => inr (from_hash256 h) | None => inl tt end)
      | None => inl tt
      end)) :
  application_jet_local_spec_sep f elements_ge Elements.env Ty.Unit (Ty.Sum Ty.Unit Word256)
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep g foff hoff) 544 0 696)
    (fun a environment => @elements_current_spec (PrimitivePrimSem option_Monad_Zero) _ t a environment).
Proof.
  refine (elements_current_gen_local (fun e => sigTxIn (Elements.envTx e)) 257 (flag_hash_cells g)
    (flag_hash_rep g foff hoff) (Ty.Sum Ty.Unit Word256)
    _t'9 _t'10 _t'11 _numInputs 696 0 544 (flag_hash_tail flagfield hashfield) f
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(discriminate) ltac:(discriminate) ltac:(discriminate) ltac:(discriminate)
    ltac:(split; lia) elements_elementsTransaction_numInputs
    ltac:(split; lia) ltac:(split; lia) ltac:(split; lia)
    _ _ Hshape ltac:(reflexivity) _ _).
  - intros m1 m2 b ofs x [Hfl Hh] Hl. split.
    + apply (Hl Mint8unsigned (ofs + foff) _); [lia|change (size_chunk Mint8unsigned) with 1; lia|exact Hfl].
    + intros h Hg. eapply hash_elem_rep_mono; [exact (Hh h Hg)|].
      intros chunk o v H1 H2. apply Hl; lia.
  - intros bd dbase bw outedge bl le mc x be ebase bt txbase bin inbase ixv cur
      HEnv HDst He0 He1 Ht0 Ht1 Hi0 HiM Hl0 Hl1 Hlix [Hfl Hh] S1 S2 S4 S5 HF.
    pose proof HF as [_ [_ [_ [HCur _]]]].
    assert (Hs0 : 0 <= 544 * Int64.unsigned ixv)
      by (apply Z.mul_nonneg_nonneg; [lia|apply Int64.unsigned_range]).
    set (ofs := inbase + 544 * Int64.unsigned ixv) in *.
    set (e := elements_version_locals bl).
    set (b1 := opt_is_some (g x)) in *.
    assert (HF1 : write_frame_at mc bd dbase bw outedge cur 1).
    { eapply write_frame_at_shorter; [|exact HF]. lia. }
    destruct (elements_writeBit_step mc bd dbase bw outedge cur b1 HF1) as (mb & Hwb & E1).
    assert (HFb : write_frame_at mb bd dbase bw outedge (cur - 1) 256).
    { eapply write_frame_at_after_effect with (cells := [Some b1]); [reflexivity|lia|exact HF|exact E1]. }
    assert (HLoadB : forall chunk b lo hi o, out_sep bd dbase bw outedge cur 257 b lo hi ->
      lo <= o -> o + size_chunk chunk <= hi -> Mem.load chunk mb b o = Mem.load chunk mc b o).
    { intros chunk b lo hi o Hs Hlo Hhi.
      eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
        (cursor := cur) (cursor0 := cur) (count0 := 257) (n := 1) (cells := [Some b1]) (lo := lo) (hi := hi);
        [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
    set (la := PTree.set _t'7 (Vlong ixv) (PTree.set _t'6 (Vptr bin (Ptrofs.repr inbase))
      (PTree.set _t'5 (Vptr bt (Ptrofs.repr txbase)) le))).
    set (la8 := PTree.set _t'8 (Vint (flag_bit b1)) la).
    set (lc := PTree.set _t'1 (Vint (flag_bit b1)) la8).
    assert (HEla : la!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold la. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. exact HEnv. }
    assert (HDla : la!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold la. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. exact HDst. }
    assert (HElc : lc!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold lc, la8. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HEla. }
    assert (HDlc : lc!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold lc, la8. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HDla. }
    assert (HEx1 : Clight2.exec_stmt elements_ge e le mc
      (elements_current_load3 _t'5 _t'6 _t'7 _input _sigInput
        (Ssequence (Sset _t'8 (Efield (cur_elem _t'6 _t'7) flagfield tbool))
          (Scall (Some _t'1)
            (Evar _writeBit (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tbool Tnil)) tbool cc_default))
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'8 tbool])))
      E0 lc mb Out_normal).
    { eapply exec_elements_current_load3 with (be := be) (ebase := ebase) (bt := bt) (txbase := txbase)
        (bin := bin) (inbase := inbase) (ixv := ixv) (adelta := 0);
        [discriminate|discriminate|exact HEnv|exact He0|exact He1|exact Ht0|lia|lia|
         exact elements_elementsTransaction_input|exact Hl0|exact Hl1|exact Hlix|].
      fold la.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la8).
      - apply exec_set.
        eapply eval_cur_elem_flag with (bin := bin) (inbase := inbase) (r := ixv) (foff := foff).
        + exact HFf.
        + exact (proj1 Hfb).
        + exact (proj2 Hfb).
        + unfold la. rewrite PTree.gso by discriminate. apply PTree.gss.
        + unfold la. apply PTree.gss.
        + exact Hi0.
        + exact HiM.
        + exact Hfl.
      - change lc with (set_opttemp (Some _t'1) (Vint (flag_bit b1)) la8).
        eapply exec_elements_helper_call with (id := _writeBit) (f := jets.f_writeBit)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (flag_bit b1)]) (vres := Vint (flag_bit b1)).
        + unfold elements_core_helpers. simpl. tauto.
        + reflexivity.
        + eapply eval_Econs.
          * apply eval_Etempvar. unfold la8. rewrite PTree.gso by discriminate. exact HDla.
          * reflexivity.
          * eapply eval_Econs with (v1 := Vint (flag_bit b1)).
            -- apply eval_Etempvar. unfold la8. apply PTree.gss.
            -- destruct b1; reflexivity.
            -- apply eval_Enil.
        + reflexivity.
        + exact Hwb. }
    assert (HTail : exists le' me,
      Clight2.exec_stmt elements_ge e lc mb
        (if b1 then elements_current_load3 _t'2 _t'3 _t'4 _input _sigInput
           (elements_ptr_call _writeHash (Tstruct _sha256_midstate noattr) (flag_hash_pexpr hashfield))
         else elements_skip_stmt 256) E0 le' me Out_normal /\
      write_effect mc me bd dbase bw outedge cur 257 (flag_hash_cells g x)).
    { unfold flag_hash_cells. subst b1. destruct (g x) as [h|] eqn:Hg; cbn [opt_is_some] in *.
      - assert (Hrepb : hash_elem_rep mb bin (ofs + hoff) h).
        { eapply hash_elem_rep_mono; [exact (Hh h eq_refl)|]. intros chunk o v Hlo Hhi Hl.
          rewrite (HLoadB chunk bin ofs (ofs + 544) o S5 ltac:(lia) ltac:(lia)). exact Hl. }
        assert (HSp : out_sep bd dbase bw outedge (cur - 1) 256 bin (ofs + hoff) (ofs + hoff + 32)).
        { eapply out_sep_range with (lo := ofs) (hi := ofs + 544); [|lia|lia].
          eapply out_sep_sub with (cursor := cur) (count := 257); [lia|lia|lia|lia|exact S5]. }
        destruct (hash_elem_pay bd dbase bw outedge mb bin (ofs + hoff) h (cur - 1) Hrepb ltac:(lia) ltac:(lia)
          HSp HFb) as (me & HC2 & E2).
        assert (Hm0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
        { rewrite (HLoadB Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact Hl0. }
        assert (Hm1 : Mem.load Mptr mb bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
        { rewrite (HLoadB Mptr bt (txbase + 0) (txbase + 0 + 8) (txbase + 0) S4 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact Hl1. }
        assert (Hmix : Mem.load Mint64 mb be (ebase + 80) = Some (Vlong ixv)).
        { rewrite (HLoadB Mint64 be (ebase + 80) (ebase + 88) (ebase + 80) S2 ltac:(lia)
            ltac:(change (size_chunk Mint64) with 8; lia)). exact Hlix. }
        set (lb := PTree.set _t'4 (Vlong ixv) (PTree.set _t'3 (Vptr bin (Ptrofs.repr inbase))
          (PTree.set _t'2 (Vptr bt (Ptrofs.repr txbase)) lc))).
        assert (HDlb : lb!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold lb. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate.
          rewrite PTree.gso by discriminate. exact HDlc. }
        assert (HP : eval_expr elements_ge e lb mb (flag_hash_pexpr hashfield)
          (Vptr bin (Ptrofs.repr (ofs + hoff)))).
        { unfold flag_hash_pexpr, cur_elem.
          exact (eval_elements_elem_field_addr e lb mb _t'3 _t'4 _sigInput 544 hashfield hoff _sha256_midstate
            bin inbase ixv elements_sizeof_sigInput HFh
            ltac:(unfold lb; rewrite PTree.gso by discriminate; apply PTree.gss)
            ltac:(unfold lb; apply PTree.gss) Hi0 ltac:(split; lia) ltac:(lia)
            ltac:(unfold ofs in *; lia) ltac:(unfold ofs in *; lia)). }
        exists lb, me. split.
        + exact (exec_elements_current_load3 e lc _t'2 _t'3 _t'4 _input 0 _sigInput
            (elements_ptr_call _writeHash (Tstruct _sha256_midstate noattr) (flag_hash_pexpr hashfield))
            mb lb me Out_normal be ebase bt txbase bin inbase ixv ltac:(discriminate) ltac:(discriminate)
            HElc He0 He1 Ht0 ltac:(lia) ltac:(lia) elements_elementsTransaction_input Hm0 Hm1 Hmix
            (exec_elements_ptr_call e lb mb _writeHash (Tstruct _sha256_midstate noattr) f_writeHash
              (flag_hash_pexpr hashfield) (ofs + hoff) bd dbase bin me ltac:(reflexivity) ltac:(reflexivity)
              elements_writeHash_symbol elements_writeHash_funct ltac:(reflexivity) HDlb HP HC2)).
        + exact (write_effect_seq mc mb me bd dbase bw outedge cur 1 256 [Some true]
            (hash_cells (hash256_reg h)) eq_refl ltac:(lia) HF E1 E2).
      - destruct (elements_skipBits_step mb bd dbase bw outedge (cur - 1) 256%nat HFb) as (me & HCallS & E2).
        exists lc, me. split.
        + unfold elements_skip_stmt.
          assert (Hargs : eval_exprlist elements_ge e lc mb
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 256) tint]
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
            [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat 256))]).
          { eapply eval_Econs; [apply eval_Etempvar; exact HDlc|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
            apply elements_cast_const'; lia. }
          exact (exec_elements_helper_call e lc mb None _skipBits jets.f_skipBits
            _ _ _ _ _ _ me ltac:(unfold elements_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
            ltac:(reflexivity) HCallS).
        + exact (write_effect_seq mc mb me bd dbase bw outedge cur 1 256 [Some false]
            (repeat None 256) eq_refl ltac:(lia) HF E1 E2). }
    destruct HTail as (le' & me & HT & E).
    exists le', me. split; [|exact E].
    unfold flag_hash_tail, flag_hash_body.
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := le'); [|apply exec_elements_return_one].
    eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := lc); [exact HEx1|].
    eapply exec_Sifthenelse with (v1 := Vint (flag_bit b1)) (b := b1).
    + apply eval_Etempvar. unfold lc. apply PTree.gss.
    + destruct b1; reflexivity.
    + destruct b1; exact HT.
  - intros environment.
    destruct (elements_current_sem t
      (fun txi => match g txi with Some h => inr (from_hash256 h) | None => inl tt end) Hres environment)
      as (txi & Hn & Hs).
    exists txi. eexists. split; [exact Hn|]. split; [exact Hs|].
    unfold flag_hash_cells. destruct (g txi) as [h|].
    + rewrite encode_sum_inr_hash, encode_from_hash256. reflexivity.
    + reflexivity.
Qed.

(** ** current_pegin *)

Lemma elements_sigInput_isPegin' : elements_field_at _sigInput _isPegin 537.
Proof. vm_compute; reflexivity. Qed.
Lemma elements_sigInput_hasAnnex' : elements_field_at _sigInput _hasAnnex 536.
Proof. vm_compute; reflexivity. Qed.

Definition elements_input_pegin_spec' {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  Primitive.Combinators.prim Elements.InputPegin.

Definition elements_current_pegin_spec {alg : Primitive.Algebra} : alg Ty.Unit (Ty.Sum Ty.Unit Word256) :=
  elements_current_spec (@elements_input_pegin_spec' alg).

Lemma elements_current_pegin_shape :
  elements_wrapper_shape f_simplicity_current_pegin
    (elements_current_gen_rest _t'9 _t'10 _t'11 _numInputs (flag_hash_tail _isPegin _pegin)).
Proof. repeat split; try reflexivity. apply elements_current11_disjoint. Qed.

Theorem elements_current_pegin_local_spec :
  application_jet_local_spec_sep f_simplicity_current_pegin elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep sigTxiPegin 537 32) 544 0 696)
    (fun a environment => @elements_current_pegin_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_current_flag_hash_local sigTxiPegin _isPegin _pegin 537 32 f_simplicity_current_pegin
    elements_sigInput_isPegin' elements_sigInput_pegin ltac:(split; lia) ltac:(split; lia)
    elements_current_pegin_shape
    (fun a e => @elements_input_pegin_spec' (PrimitivePrimSem option_Monad_Zero) a e) _).
  intros a e.
  assert (H : @elements_input_pegin_spec' (PrimitivePrimSem option_Monad_Zero) a e =
    Elements.sem Elements.InputPegin a e) by reflexivity.
  rewrite H. unfold Elements.sem. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map. destruct (sigTxiPegin txi); reflexivity.
Qed.

(** ** current_annex_hash *)

Definition annex_hash_of (txi : sigTxInput) : option hash256 := option_map byteStringHash (sigTxiAnnex txi).

Definition elements_input_annex_hash_spec' {alg : Primitive.Algebra} :
    alg Word32 (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256)) :=
  Primitive.Combinators.prim Elements.InputAnnexHash.

Definition elements_current_annex_hash_spec {alg : Primitive.Algebra} : alg Ty.Unit (Ty.Sum Ty.Unit Word256) :=
  elements_current_spec (@elements_input_annex_hash_spec' alg).

Lemma elements_current_annex_hash_shape :
  elements_wrapper_shape f_simplicity_current_annex_hash
    (elements_current_gen_rest _t'9 _t'10 _t'11 _numInputs (flag_hash_tail _hasAnnex _annexHash)).
Proof. repeat split; try reflexivity. apply elements_current11_disjoint. Qed.

Theorem elements_current_annex_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_current_annex_hash elements_ge Elements.env Ty.Unit
    (Ty.Sum Ty.Unit Word256)
    (current_gen_rep (fun e => sigTxIn (Elements.envTx e)) (flag_hash_rep annex_hash_of 536 0) 544 0 696)
    (fun a environment => @elements_current_annex_hash_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  refine (elements_current_flag_hash_local annex_hash_of _hasAnnex _annexHash 536 0
    f_simplicity_current_annex_hash
    elements_sigInput_hasAnnex' elements_sigInput_annexHash ltac:(split; lia) ltac:(split; lia)
    elements_current_annex_hash_shape
    (fun a e => @elements_input_annex_hash_spec' (PrimitivePrimSem option_Monad_Zero) a e) _).
  intros a e.
  assert (H : @elements_input_annex_hash_spec' (PrimitivePrimSem option_Monad_Zero) a e =
    Elements.sem Elements.InputAnnexHash a e) by reflexivity.
  rewrite H. unfold Elements.sem, annex_hash_of. cbv zeta.
  destruct (nth_error (sigTxIn (Elements.envTx e)) (Z.to_nat (toZ a))) as [txi|]; [|reflexivity].
  unfold Datatypes.option_map. destruct (sigTxiAnnex txi); reflexivity.
Qed.
