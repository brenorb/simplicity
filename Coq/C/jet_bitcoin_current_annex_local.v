(** Actual Bitcoin current_annex_hash jet against the literal canonical program
    [primitive CurrentIndex >>> assert (primitive InputAnnexHash)].
    C: [if (env->tx->numInputs <= env->ix) return false;
        if (writeBit(dst, env->tx->input[env->ix].hasAnnex))
          writeHash(dst, &env->tx->input[env->ix].annexHash);
        else skipBits(dst, 256);
        return true;] *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jet_uint32_array_init C.jet_word_repr.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec.
Require Import C.jet_bitcoin_env_load C.jet_bitcoin_indexed_scalar C.jet_bitcoin_indexed_ptr.
Require Import C.jet_bitcoin_current_exec C.jet_bitcoin_current_spec.
Require Import C.jet_bitcoin_hash_write C.jet_bitcoin_hash_getters C.jet_bitcoin_script_cmr_local.
Require Import C.jet_bitcoin_ext_prim C.jet_bitcoin_ext_ptr_jets C.jet_bitcoin_ext_current_spec.
Require Import C.jet_bitcoin_annex_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Import PrimitiveBitcoinExt.Primitive.Coercions.
Import PrimitiveBitcoinExt.Primitive.CanonicalStructures.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 120.

Definition bitcoin_current_annex_hash_spec {alg : PrimitiveBitcoinExt.Primitive.Algebra} :
    alg Ty.Unit (Ty.Sum Ty.Unit Word256) :=
  ext_comp (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.CurrentIndex)
    (ext_assert_spec (PrimitiveBitcoinExt.Primitive.Combinators.prim BitcoinExt.InputAnnexHash)).

Definition current_annex_result (o : option hash256) : Ty.tySem (Ty.Sum Ty.Unit Word256) :=
  match o with Some h => inr (from_hash256 h) | None => inl tt end.

Definition current_annex_cells (o : option hash256) : list Cell :=
  match o with
  | Some h => Some true :: hash_cells (hash256_reg h)
  | None => Some false :: repeat None 256
  end.

Lemma encode_current_annex_result o : encode (current_annex_result o) = current_annex_cells o.
Proof.
  destruct o as [h|]; unfold current_annex_result, current_annex_cells.
  - rewrite encode_sum_inr_hash', encode_from_hash256. reflexivity.
  - vm_compute. reflexivity.
Qed.

Lemma bitcoin_current_annex_hash_sem (environment : ext_environment) :
  exists o, nth_error (extInAnnexHash environment) (ext_ix environment) = Some o /\
    @bitcoin_current_annex_hash_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) tt environment =
      Some (current_annex_result o).
Proof.
  pose proof (Bitcoin.envIxBounded (extBase environment)) as Hb.
  pose proof (extInAnnexHash_len environment) as Hl.
  destruct (nth_error (extInAnnexHash environment) (ext_ix environment)) as [o|] eqn:Hnth;
    [|apply nth_error_None in Hnth; unfold ext_ix in Hnth; lia].
  exists o. split; [reflexivity|].
  unfold bitcoin_current_annex_hash_spec. rewrite ext_comp_sem.
  assert (HCI : @PrimitiveBitcoinExt.Primitive.Combinators.prim Ty.Unit Word32
    (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    BitcoinExt.CurrentIndex tt environment =
    Some (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment)))) by reflexivity.
  rewrite HCI. rewrite ext_assert_sem.
  assert (HIV : @PrimitiveBitcoinExt.Primitive.Combinators.prim Word32
    (Ty.Sum Ty.Unit (Ty.Sum Ty.Unit Word256))
    (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero)
    BitcoinExt.InputAnnexHash (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment))) environment =
    BitcoinExt.sem BitcoinExt.InputAnnexHash (@fromZ (WordToZ 5) (Z.of_nat (ext_ix environment))) environment)
    by reflexivity.
  rewrite HIV. unfold BitcoinExt.sem. cbv zeta.
  unfold ext_ix in *.
  rewrite (bitcoin_ix_word (extBase environment)), Nat2Z.id. rewrite Hnth.
  destruct o; reflexivity.
Qed.

Definition elem_at (t ip : ident) : expr :=
  Ederef (Ebinop Oadd (Etempvar t (tptr (Tstruct _sigInput noattr))) (Etempvar ip tulong)
    (tptr (Tstruct _sigInput noattr))) (Tstruct _sigInput noattr).

Definition tx_input_expr (t : ident) : expr :=
  Efield (Ederef (Etempvar t (tptr (Tstruct _bitcoinTransaction noattr)))
    (Tstruct _bitcoinTransaction noattr)) _input (tptr (Tstruct _sigInput noattr)).

Definition current_annex_guard : statement :=
  Ssequence (Sset _t'9 bitcoin_env_tx_expr)
    (Ssequence
      (Sset _t'10 (Efield (Ederef (Etempvar _t'9 (tptr (Tstruct _bitcoinTransaction noattr)))
        (Tstruct _bitcoinTransaction noattr)) _numInputs tulong))
      (Ssequence (Sset _t'11 bitcoin_env_ix_expr)
        (Sifthenelse (Ebinop Ole (Etempvar _t'10 tulong) (Etempvar _t'11 tulong) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))).

Definition current_annex_cond : statement :=
  Ssequence (Sset _t'5 bitcoin_env_tx_expr)
    (Ssequence (Sset _t'6 (tx_input_expr _t'5))
      (Ssequence (Sset _t'7 bitcoin_env_ix_expr)
        (Ssequence (Sset _t'8 (Efield (elem_at _t'6 _t'7) _hasAnnex tbool))
          (Scall (Some _t'1) (Evar _writeBit writeBit_type)
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'8 tbool])))).

Definition current_annex_then : statement :=
  Ssequence (Sset _t'2 bitcoin_env_tx_expr)
    (Ssequence (Sset _t'3 (tx_input_expr _t'2))
      (Ssequence (Sset _t'4 bitcoin_env_ix_expr)
        (Scall None
          (Evar _writeHash (Tfunction
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr (Tstruct _sha256_midstate noattr)) Tnil))
            tvoid cc_default))
          [Etempvar _dst (tptr (Tstruct _frameItem noattr));
           Eaddrof (Efield (elem_at _t'3 _t'4) _annexHash (Tstruct _sha256_midstate noattr))
             (tptr (Tstruct _sha256_midstate noattr))]))).

Definition current_annex_rest : statement :=
  Ssequence current_annex_guard
    (Ssequence
      (Ssequence current_annex_cond
        (Sifthenelse (Etempvar _t'1 tbool) current_annex_then (bitcoin_skip_stmt 256)))
      (Sreturn (Some (Econst_int (Int.repr 1) tint)))).

Lemma bitcoin_current_annex_hash_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_current_annex_hash current_annex_rest.
Proof.
  repeat split; try reflexivity.
  intros x y HX HY Hxy. cbn in HX, HY.
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].
Qed.

Lemma eval_tx_input_expr e le m t bt txbase bin inbase :
  le!t = Some (Vptr bt (Ptrofs.repr txbase)) -> 0 <= txbase -> txbase + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  eval_expr bitcoin_ge e le m (tx_input_expr t) (Vptr bin (Ptrofs.repr inbase)).
Proof.
  intros HT H0 HM HL. unfold tx_input_expr.
  eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 0) (chunk := Mptr).
  - reflexivity.
  - exact bitcoin_bitcoinTransaction_input.
  - reflexivity.
  - apply eval_bitcoin_deref_struct. exact HT.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Lemma eval_elem_hasAnnex e le m t ip bin inbase r (v : int) :
  le!t = Some (Vptr bin (Ptrofs.repr inbase)) -> le!ip = Some (Vlong r) ->
  0 <= inbase -> inbase + 160 * Int64.unsigned r + 160 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bin (inbase + 160 * Int64.unsigned r + 152) = Some (Vint v) ->
  eval_expr bitcoin_ge e le m (Efield (elem_at t ip) _hasAnnex tbool) (Vint v).
Proof.
  intros HT HI HB HM HL.
  assert (HR : 0 <= Int64.unsigned r) by (apply Int64.unsigned_range).
  assert (HI' : le!ip = Some (Vlong (Int64.repr (Int64.unsigned r))))
    by (rewrite Int64.repr_unsigned; exact HI).
  pose proof (eval_bitcoin_index e le m t ip _sigInput 160 bin inbase (Int64.unsigned r)
    bitcoin_sizeof_sigInput HT HI' HB ltac:(lia) HR ltac:(lia)) as HElem.
  eapply eval_bitcoin_field_value with (sid := _sigInput) (delta := 152) (chunk := Mint8unsigned).
  - reflexivity.
  - exact bitcoin_sigInput_hasAnnex.
  - reflexivity.
  - exact HElem.
  - rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact HL].
Qed.

Definition bitcoin_current_annex_hash_env_rep (m : mem) (env : val) (e : ext_environment)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI ixv,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\ inbase + 160 * Z.of_nat (length (extInAnnexHash e)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + 448) = Some (Vlong nI) /\
    Mem.load Mint64 m be (ebase + 48) = Some (Vlong ixv) /\
    Int64.unsigned nI = Z.of_nat (length (extInAnnexHash e)) /\
    Int64.unsigned ixv = Z.of_nat (ext_ix e) /\
    (forall j o, nth_error (extInAnnexHash e) j = Some o ->
      annex_elem_rep m bin (inbase + 160 * Z.of_nat j) o) /\
    fp = [(be, ebase, ebase + 8); (be, ebase + 48, ebase + 56); (bt, txbase + 0, txbase + 8);
          (bin, inbase, inbase + 160 * Z.of_nat (length (extInAnnexHash e)))].

Theorem bitcoin_current_annex_hash_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_current_annex_hash bitcoin_ge ext_environment
    Ty.Unit (Ty.Sum Ty.Unit Word256) bitcoin_current_annex_hash_env_rep
    (fun a environment => @bitcoin_current_annex_hash_spec
      (PrimitiveBitcoinExt.Primitive.Theory.PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & txbase & bin & inbase & nI & ixv & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HLix & HnI & Hixv & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  set (annexes := extInAnnexHash environment) in *.
  set (nn := Z.of_nat (length annexes)) in *.
  assert (HB : Z.of_nat (bitSize (Ty.Sum Ty.Unit Word256)) = 257) by reflexivity.
  rewrite HB in HSep, HFrame.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 257 be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S2 : out_sep bd dbase bw outedge cursor 257 be (ebase + 48) (ebase + 56))
    by exact (HSep (be, ebase + 48, ebase + 56) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 257 bt (txbase + 0) (txbase + 8))
    by exact (HSep (bt, txbase + 0, txbase + 8) ltac:(simpl; auto)).
  assert (S5 : out_sep bd dbase bw outedge cursor 257 bin inbase (inbase + 160 * nn))
    by exact (HSep (bin, inbase, inbase + 160 * nn) ltac:(simpl; auto)).
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  destruct (bitcoin_current_annex_hash_sem environment) as (o & Hnth & Hspec).
  fold annexes in Hnth.
  assert (Hix_lt : (ext_ix environment < length annexes)%nat)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  assert (Hlt : Int64.ltu ixv nI = true).
  { unfold Int64.ltu. rewrite zlt_true; [reflexivity|]. rewrite Hixv, HnI. lia. }
  set (eofs := inbase + 160 * Int64.unsigned ixv).
  assert (Hm : 160 * Int64.unsigned ixv + 160 <= 160 * nn) by (rewrite Hixv; subst nn; lia).
  assert (Hr0 : 0 <= Int64.unsigned ixv) by apply Int64.unsigned_range.
  pose proof (HLelem _ _ Hnth) as HEl. rewrite <- Hixv in HEl. destruct HEl as [Hflag Hhash].
  set (b2 := is_some o).
  set (V := current_annex_cells o).
  pose proof HFrame as [_ [_ [_ [HCnt0 _]]]].
  assert (HMid : bitcoin_wrapper_mid f_simplicity_bitcoin_current_annex_hash current_annex_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 257 bytes).
  { unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    assert (HF1 : write_frame_at mc bd dbase bw outedge cursor 1).
    { eapply write_frame_at_shorter; [|exact HFrameC]. lia. }
    destruct (bitcoin_writeBit_step mc bd dbase bw outedge cursor b2 HF1) as (mb & Hwb1 & E1).
    assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 256).
    { eapply write_frame_at_after_effect with (cells := [Some b2]);
        [reflexivity|lia|exact HFrameC|exact E1]. }
    assert (HLoadB : forall chunk b0 lo hi ofs, out_sep bd dbase bw outedge cursor 257 b0 lo hi ->
      lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b0 ofs = Mem.load chunk mc b0 ofs).
    { intros chunk b0 lo hi ofs Hs Hlo Hhi.
      eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
        (cursor := cursor) (cursor0 := cursor) (count0 := 257) (n := 1)
        (cells := [Some b2]) (lo := lo) (hi := hi);
        [lia|lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
    set (le0 := bitcoin_wrapper_temps f_simplicity_bitcoin_current_annex_hash
      (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase).
    assert (HEnv0 : le0!_env = Some (Vptr be (Ptrofs.repr ebase)))
      by (unfold le0, bitcoin_wrapper_temps; apply PTree.gss).
    assert (HDst0 : le0!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold le0, bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss. }
    set (g1 := PTree.set _t'9 (Vptr bt (Ptrofs.repr txbase)) le0).
    set (g2 := PTree.set _t'10 (Vlong nI) g1).
    set (g3 := PTree.set _t'11 (Vlong ixv) g2).
    set (c1 := PTree.set _t'5 (Vptr bt (Ptrofs.repr txbase)) g3).
    set (c2 := PTree.set _t'6 (Vptr bin (Ptrofs.repr inbase)) c1).
    set (c3 := PTree.set _t'7 (Vlong ixv) c2).
    set (c4 := PTree.set _t'8 (Vint (bit_int b2)) c3).
    set (c5 := PTree.set _t'1 (Vint (bit_int b2)) c4).
    assert (HEg : forall l, (l = g1 \/ l = g2 \/ l = g3 \/ l = c1 \/ l = c2 \/ l = c3 \/ l = c4 \/ l = c5) ->
      l!_env = Some (Vptr be (Ptrofs.repr ebase)) /\ l!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { intros l Hl.
      repeat (destruct Hl as [Hl|Hl]); subst l;
        unfold c5, c4, c3, c2, c1, g3, g2, g1; repeat rewrite PTree.gso by discriminate;
        split; assumption. }
    assert (HGuard : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) le0 mc current_annex_guard
      E0 g3 mc Out_normal).
    { unfold current_annex_guard.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := g1).
      - apply exec_set. eapply eval_bitcoin_env_tx_expr; [exact HEnv0|exact He0|lia|exact (HLP _ _ _ _ HLtx)].
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := g2).
        + apply exec_set.
          eapply eval_bitcoin_field_value with (sid := _bitcoinTransaction) (delta := 448) (chunk := Mint64).
          * reflexivity.
          * exact bitcoin_bitcoinTransaction_numInputs.
          * reflexivity.
          * apply eval_bitcoin_deref_struct. unfold g1. apply PTree.gss.
          * rewrite bitcoin_ptr_add_repr by lia. apply bitcoin_loadv_repr; [lia|exact (HLP _ _ _ _ HLn)].
        + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := g3).
          * apply exec_set. eapply eval_bitcoin_env_ix;
              [exact (proj1 (HEg g2 ltac:(tauto)))|exact He0|exact He1|exact (HLP _ _ _ _ HLix)].
          * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
            -- eapply eval_Ebinop with (v1 := Vlong nI) (v2 := Vlong ixv).
               ++ apply eval_Etempvar. unfold g3. rewrite PTree.gso by discriminate. apply PTree.gss.
               ++ apply eval_Etempvar. unfold g3. apply PTree.gss.
               ++ change (Some (Val.of_bool (negb (Int64.ltu ixv nI))) = Some (Vint Int.zero)).
                  rewrite Hlt. reflexivity.
            -- reflexivity.
            -- apply exec_Sskip. }
    assert (HCond : Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) g3 mc current_annex_cond
      E0 c5 mb Out_normal).
    { unfold current_annex_cond.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := c1).
      - apply exec_set. eapply eval_bitcoin_env_tx_expr;
          [exact (proj1 (HEg g3 ltac:(tauto)))|exact He0|lia|exact (HLP _ _ _ _ HLtx)].
      - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := c2).
        + apply exec_set. eapply eval_tx_input_expr; [unfold c1; apply PTree.gss|exact Ht0|lia|
            exact (HLP _ _ _ _ HLin)].
        + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := c3).
          * apply exec_set. eapply eval_bitcoin_env_ix;
              [exact (proj1 (HEg c2 ltac:(tauto)))|exact He0|exact He1|exact (HLP _ _ _ _ HLix)].
          * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := c4).
            -- apply exec_set.
               eapply eval_elem_hasAnnex with (bin := bin) (inbase := inbase) (r := ixv).
               ++ unfold c3. rewrite PTree.gso by discriminate. unfold c2. apply PTree.gss.
               ++ unfold c3. apply PTree.gss.
               ++ exact Hi0.
               ++ lia.
               ++ exact (HLP _ _ _ _ Hflag).
            -- change c5 with (set_opttemp (Some _t'1) (Vint (bit_int b2)) c4).
               eapply exec_bitcoin_helper_call with (id := _writeBit) (f := jets.f_writeBit)
                 (vargs := [Vptr bd (Ptrofs.repr dbase); Vint (bit_int b2)]) (vres := Vint (bit_int b2)).
               ++ unfold bitcoin_core_helpers. simpl. tauto.
               ++ reflexivity.
               ++ eapply eval_Econs.
                  ** apply eval_Etempvar. exact (proj2 (HEg c4 ltac:(tauto))).
                  ** reflexivity.
                  ** eapply eval_Econs with (v1 := Vint (bit_int b2)).
                     --- apply eval_Etempvar. unfold c4. apply PTree.gss.
                     --- destruct b2; reflexivity.
                     --- apply eval_Enil.
               ++ reflexivity.
               ++ exact Hwb1. }
    assert (HTail : exists le'' me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) c5 mb
        (if b2 then current_annex_then else bitcoin_skip_stmt 256) E0 le'' me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 257 V).
    { destruct o as [h|].
      - change b2 with true in *.
        assert (Hrep : hash_elem_rep m bin eofs h) by (apply Hhash; reflexivity).
        assert (Hrepb : hash_elem_rep mb bin eofs h).
        { eapply hash_elem_rep_mono; [exact Hrep|].
          intros chunk o0 v Hlo Hhi Hl.
          rewrite (HLoadB chunk bin inbase (inbase + 160 * nn) o0 S5 ltac:(unfold eofs in Hlo; lia)
            ltac:(unfold eofs in Hhi; lia)).
          apply HLP. exact Hl. }
        assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
        { rewrite (HLoadB Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact (HLP _ _ _ _ HLtx). }
        assert (Hmb1 : Mem.load Mptr mb bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
        { rewrite (HLoadB Mptr bt (txbase + 0) (txbase + 8) (txbase + 0) S4 ltac:(lia)
            ltac:(change (size_chunk Mptr) with 8; lia)). exact (HLP _ _ _ _ HLin). }
        assert (Hmb2 : Mem.load Mint64 mb be (ebase + 48) = Some (Vlong ixv)).
        { rewrite (HLoadB Mint64 be (ebase + 48) (ebase + 56) (ebase + 48) S2 ltac:(lia)
            ltac:(change (size_chunk Mint64) with 8; lia)). exact (HLP _ _ _ _ HLix). }
        assert (HSp : out_sep bd dbase bw outedge (cursor - 1) 256 bin eofs (eofs + 32)).
        { eapply out_sep_range with (lo := inbase) (hi := inbase + 160 * nn);
            [|unfold eofs; lia|unfold eofs; lia].
          eapply out_sep_sub with (cursor := cursor) (count := 257); [lia|lia|lia|lia|exact S5]. }
        destruct (hash_elem_pay bd dbase bw outedge mb bin eofs h (cursor - 1) Hrepb
          ltac:(unfold eofs; lia) ltac:(unfold eofs; lia) HSp HFb) as (me & HCallP & E2).
        set (t1 := PTree.set _t'2 (Vptr bt (Ptrofs.repr txbase)) c5).
        set (t2 := PTree.set _t'3 (Vptr bin (Ptrofs.repr inbase)) t1).
        set (t3 := PTree.set _t'4 (Vlong ixv) t2).
        assert (HEt1 : t1!_env = Some (Vptr be (Ptrofs.repr ebase))).
        { unfold t1. rewrite PTree.gso by discriminate. exact (proj1 (HEg c5 ltac:(tauto))). }
        assert (HEt2 : t2!_env = Some (Vptr be (Ptrofs.repr ebase))).
        { unfold t2. rewrite PTree.gso by discriminate. exact HEt1. }
        exists t3, me. split.
        + unfold current_annex_then.
          eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := t1).
          * apply exec_set. eapply eval_bitcoin_env_tx_expr;
              [exact (proj1 (HEg c5 ltac:(tauto)))|exact He0|lia|exact Hmb0].
          * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := t2).
            -- apply exec_set. eapply eval_tx_input_expr; [unfold t1; apply PTree.gss|exact Ht0|lia|exact Hmb1].
            -- eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := t3).
               ++ apply exec_set. eapply eval_bitcoin_env_ix; [exact HEt2|exact He0|exact He1|exact Hmb2].
               ++ eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block _writeHash) Ptrofs.zero)
                    (f := Internal f_writeHash)
                    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr eofs)]) (vres := Vundef).
                  ** reflexivity.
                  ** eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact bitcoin_writeHash_symbol]|
                       apply deref_loc_reference; reflexivity].
                  ** eapply eval_Econs.
                     --- apply eval_Etempvar. unfold t3, t2, t1. repeat rewrite PTree.gso by discriminate.
                         exact (proj2 (HEg c5 ltac:(tauto))).
                     --- reflexivity.
                     --- eapply eval_Econs with (v1 := Vptr bin (Ptrofs.repr eofs)).
                         +++ pose proof (eval_bitcoin_elem_field_addr (bitcoin_version_locals bl) t3 mb
                               _t'3 _t'4 _sigInput 160 _annexHash 0 _sha256_midstate bin inbase ixv
                               bitcoin_sizeof_sigInput bitcoin_sigInput_annexHash
                               ltac:(unfold t3; rewrite PTree.gso by discriminate; unfold t2; apply PTree.gss)
                               ltac:(unfold t3; apply PTree.gss)
                               Hi0 ltac:(split; lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HAddr.
                             replace (inbase + 160 * Int64.unsigned ixv + 0) with eofs in HAddr
                               by (unfold eofs; lia).
                             exact HAddr.
                         +++ reflexivity.
                         +++ apply eval_Enil.
                  ** exact bitcoin_writeHash_funct.
                  ** reflexivity.
                  ** exact HCallP.
        + exact (write_effect_seq mc mb me bd dbase bw outedge cursor 1 256 [Some true]
            (hash_cells (hash256_reg h)) eq_refl ltac:(lia) HFrameC E1 E2).
      - change b2 with false in *.
        destruct (bitcoin_skipBits_step mb bd dbase bw outedge (cursor - 1) 256%nat HFb)
          as (me & HCallS & E2).
        exists c5, me. split.
        + unfold bitcoin_skip_stmt.
          assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) c5 mb
            [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr 256) tint]
            (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
            [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat 256))]).
          { eapply eval_Econs; [apply eval_Etempvar; exact (proj2 (HEg c5 ltac:(tauto)))|reflexivity|].
            eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
            apply bitcoin_cast_const'; lia. }
          exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) c5 mb None _skipBits jets.f_skipBits
            _ _ _ _ _ _ me ltac:(unfold bitcoin_core_helpers; simpl; tauto) ltac:(reflexivity) Hargs
            ltac:(reflexivity) HCallS).
        + exact (write_effect_seq mc mb me bd dbase bw outedge cursor 1 256 [Some false]
            (repeat None 256) eq_refl ltac:(lia) HFrameC E1 E2). }
    destruct HTail as (lef & me & HT & (c & p & fl & l & pm & vv)).
    exists lef, me.
    refine (conj _ (conj c (conj p (conj fl (conj _ (conj pm vv)))))).
    - unfold current_annex_rest.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := g3); [exact HGuard|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := me) (le1 := lef);
        [|apply exec_Sreturn_some, eval_Econst_int].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := c5); [exact HCond|].
      eapply exec_Sifthenelse with (v1 := Vint (bit_int b2)) (b := b2).
      + apply eval_Etempvar. unfold c5. apply PTree.gss.
      + destruct b2; reflexivity.
      + exact HT.
    - intros chunk b ofs _ H1' H2'. exact (l chunk b ofs H1' H2'). }
  destruct (bitcoin_wrapper_layout f_simplicity_bitcoin_current_annex_hash current_annex_rest V
    (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 257 bytes
    bitcoin_current_annex_hash_shape HBf HA HBytes ltac:(lia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (current_annex_result o). split; [exact Hspec|].
  split; [exact HCall|]. split; [rewrite encode_current_annex_result; exact HCells|].
  split; [exact HPrefix|]. rewrite HB. split; [exact HFields|]. exact HMem.
Qed.
