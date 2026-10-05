(** The Bitcoin jet input_utxo_hash against the literal inputUtxoHash program.
    The jet computes the SHA-256 of the spent output's value and script hash; the
    proof is conditional on [memcpy_model], and the environment relation
    includes the dispatch pointer and the counter bound. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Simplicity.Alg.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_memcpy_model C.jet_bitmachine_rep C.jet_application_sep.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_output_layout_step C.jet_write_layout C.jet_encoding.
Require Import C.jet_constant_layout C.jet_wide C.jet_complement_wide_layout.
Require Import C.jet_read32s_layout C.jet_write32s_layout C.jet_uint32_array_init C.jet_sha256_iv_init.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_transport C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_uchars_prep.
Require Import C.jet_sha_uchars_exec C.jet_sha_hash_exec C.jet_sha_finalize_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_add_n_calls C.jet_sha_add_n_exec C.jet_sha_ctx8_add_jets.
Require Import C.jet_sha_ctx8_finalize_jet.
Require Import C.jet_sha_tapdata_prep C.jet_sha_tapdata_jet.
Require Import C.jet_sha_ctx_abs C.jet_sha_ctxi C.jet_sha_tagged_ctx C.jet_sha_hash_io.
Require Import C.jet_bitcoin_make_tapleaf_exec.
Require Import C.jet_bitcoin_effects C.jet_bitcoin_env_load.
Require Import C.jet_sha_indexed_exec C.jet_sha_index_eval C.jet_sha_steps.
Require Import C.jet_forWhile_seq C.jet_bitcoin_ext_prim C.jet_bitcoin_full_prim.
Require Import C.jet_bitcoin_words_hash C.jet_bitcoin_composite_hash.
Require Import C.jet_bitcoin_vh_hash_spec C.jet_bitcoin_vh_hash_prep C.jet_bitcoin_output_hash_jet.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation SIT := (Tstruct _sigInput noattr).

Definition iu_env (bl bm bx br : block) : env :=
  PTree.set __res (br, CTX) (PTree.set _ctx (bx, CTX)
    (PTree.set _midstate (bm, MID) (PTree.set _src (bl, FR) empty_env))).

Definition iu_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase))
      (create_undef_temps (fn_temps f_simplicity_bitcoin_input_utxo_hash)))).

Definition iu_then : statement :=
  Ssequence
    (Ssequence (Sset _t'4 (Efield (Ederef (Etempvar _env (tptr ENVT)) ENVT) _tx (tptr TXT)))
      (Ssequence (Sset _t'5 (Efield (Ederef (Etempvar _t'4 (tptr TXT)) TXT) _input (tptr SIT)))
        (Sset _txo (Eaddrof (Efield (Ederef (Ebinop Oadd (Etempvar _t'5 (tptr SIT)) (Etempvar _i tulong)
          (tptr SIT)) SIT) _txo SOT) (tptr SOT)))))
    (Ssequence
      (Ssequence
        (Scall None (Evar _sha256_init init_ty)
          [Eaddrof (Evar __res CTX) CTXP; Efield (Evar _midstate MID) _s (tarray tuint 8)])
        (Sassign (Evar _ctx CTX) (Evar __res CTX)))
      (Ssequence
        (Ssequence (Sset _t'3 (Efield (Ederef (Etempvar _txo (tptr SOT)) SOT) _value tulong))
          (Scall None (Evar _sha256_u64be (Tfunction (Tcons CTXP (Tcons tulong Tnil)) tbool cc_default))
            [Eaddrof (Evar _ctx CTX) CTXP; Etempvar _t'3 tulong]))
        (Ssequence
          (Scall None (Evar _sha256_hash (Tfunction (Tcons CTXP (Tcons (tptr MID) Tnil)) tvoid cc_default))
            [Eaddrof (Evar _ctx CTX) CTXP;
             Eaddrof (Efield (Ederef (Etempvar _txo (tptr SOT)) SOT) _scriptPubKey MID) (tptr MID)])
          (Ssequence
            (Scall None (Evar _sha256_finalize (Tfunction (Tcons CTXP Tnil) tbool cc_default))
              [Eaddrof (Evar _ctx CTX) CTXP])
            (Scall None (Evar _writeHash (Tfunction (Tcons FRP (Tcons (tptr MID) Tnil)) tvoid cc_default))
              [Etempvar _dst FRP; Eaddrof (Evar _midstate MID) (tptr MID)]))))).

Definition iu_else : statement :=
  Scall None (Evar _skipBits (Tfunction (Tcons FRP (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst FRP; Econst_int (Int.repr 256) tint].

Lemma iu_body :
  fn_body f_simplicity_bitcoin_input_utxo_hash =
    Ssequence (Sassign (Evar _src FR) (Etempvar _src FR))
      (shx_indexed_rest _t'6 _t'7 _numInputs iu_then iu_else).
Proof. reflexivity. Qed.

Lemma iu_blocks bl bm bx br :
  blocks_of_env sha_ge (iu_env bl bm bx br) = [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (br, 0, 88)].
Proof. vm_compute. reflexivity. Qed.

Lemma iu_entry env m m1 m2 m3 m4 bl bm bx br bd dbase bs sbase :
  Mem.alloc m 0 16 = (m1, bl) -> Mem.alloc m1 0 32 = (m2, bm) -> Mem.alloc m2 0 88 = (m3, bx) ->
  Mem.alloc m3 0 88 = (m4, br) ->
  function_entry2 sha_ge f_simplicity_bitcoin_input_utxo_hash
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] m
    (iu_env bl bm bx br) (iu_temps env bd dbase bs sbase) m4.
Proof.
  intros HA HB HC HD. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction | vm_compute in Hxy; discriminate | congruence].
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bl); [change (Mem.alloc m 0 16 = (m1, bl)); exact HA|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bm); [change (Mem.alloc m1 0 32 = (m2, bm)); exact HB|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bx); [change (Mem.alloc m2 0 88 = (m3, bx)); exact HC|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := br); [change (Mem.alloc m3 0 88 = (m4, br)); exact HD|].
    constructor.
  - reflexivity.
Qed.

Lemma iu_copy m mc bl bm bx br bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (iu_env bl bm bx br) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
Proof.
  intros HB HS HD HL Hload Hstore.
  assert (HA : Ptrofs.unsigned (Ptrofs.repr sbase) = sbase).
  { apply Ptrofs.unsigned_repr. unfold frame_base_valid in HB; lia. }
  eapply exec_Sassign_copy.
  - apply eval_Evar_local; reflexivity.
  - apply eval_Etempvar; exact HL.
  - reflexivity.
  - eapply assign_loc_copy with (b' := bs) (ofs' := Ptrofs.repr sbase) (bytes := bytes).
    + reflexivity.
    + intros _. change (8 | Ptrofs.unsigned (Ptrofs.repr sbase)). rewrite HA; exact HS.
    + intros _. change (8 | 0); exists 0; reflexivity.
    + left; congruence.
    + change (Mem.loadbytes m bs (Ptrofs.unsigned (Ptrofs.repr sbase)) 16 = Some bytes).
      rewrite HA; exact Hload.
    + exact Hstore.
Qed.

Lemma iu_so_value : shx_field_at _sigOutput _value 0.
Proof. vm_compute; reflexivity. Qed.
Lemma iu_so_script : shx_field_at _sigOutput _scriptPubKey 8.
Proof. vm_compute; reflexivity. Qed.
Lemma iu_env_tx : shx_field_at _txEnv _tx 0.
Proof. vm_compute; reflexivity. Qed.
Lemma iu_sizeof_so : sizeof (Clight.genv_cenv sha_ge) SOT = 40.
Proof. vm_compute; reflexivity. Qed.
Lemma iu_in_skipBits : In (jets._skipBits, jets.f_skipBits) sha_core_helpers.
Proof. unfold sha_core_helpers. simpl. tauto. Qed.
Lemma iu_cast256 m : sem_cast (Vint (Int.repr 256)) tint tulong m = Some (Vlong (Int64.repr 256)).
Proof. vm_compute. reflexivity. Qed.

Lemma iu_encode_some (h : Ty.tySem (Word 8)) :
  @encode (Ty.Sum Ty.Unit (Word 8)) (inr h) = [Some true] ++ @encode (Word 8) h.
Proof. reflexivity. Qed.
Lemma iu_encode_none :
  @encode (Ty.Sum Ty.Unit (Word 8)) (inl tt) = [Some false] ++ repeat None 256.
Proof. vm_compute. reflexivity. Qed.

Local Opaque sha_ge ge0.

Definition iu_elem_rep (m : mem) (b : block) (ofs : Z) (xv : int64) (H : hash256) : Prop :=
  Mem.load Mint64 m b ofs = Some (Vlong xv) /\
  uint32_array_at m b (ofs + 8) (hash256_reg H).

Definition input_utxo_hash_rep (m : mem) (env : val) (e : ext_environment)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\
    inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx (extBase e)))) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + 448) = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length (sigTxIn (Bitcoin.envTx (extBase e)))) /\
    (forall j txi sh, nth_error (sigTxIn (Bitcoin.envTx (extBase e))) j = Some txi ->
      nth_error (extInScriptHash e) j = Some sh ->
      iu_elem_rep m bin (inbase + 160 * Z.of_nat j + 104) (sigTxiValue txi) sh) /\
    sha_globals_ok m /\
    fp = [(be, ebase, ebase + 8); (bt, txbase + 0, txbase + 8);
          (bin, inbase, inbase + 160 * Z.of_nat (length (sigTxIn (Bitcoin.envTx (extBase e)))));
          (GC, 0, 8); (GM, 0, 8)].

Theorem bitcoin_input_utxo_hash_local_spec : memcpy_model ->
  application_jet_local_spec_sep f_simplicity_bitcoin_input_utxo_hash sha_ge ext_environment
    (Word 5) (Ty.Sum Ty.Unit (Word 8)) input_utxo_hash_rep
    (fun a e => @vh_hash_spec (BitcoinFull.Base Bitcoin.InputValue)
      (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a e).
Proof.
  intros Hmodel env0 env m bd dbase bs sbase bi bw edge outedge cursor rc a fp
    (be & ebase & bt & txbase & bin & inbase & nI & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HnI & HLelem & [Hdisp HMaxC] & HFp)
    HSep HSbase HSAlign [HSE HSO] H0 Hmax Hin Hout.
  subst env fp.
  set (outs := sigTxIn (Bitcoin.envTx (extBase env0))) in *.
  set (nn := Z.of_nat (length outs)) in *.
  change (Z.of_nat (bitSize (Ty.Sum Ty.Unit (Word 8)))) with 257 in *.
  change (Z.of_nat (bitSize (Word 5))) with 32 in Hmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor 257 be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S2 : out_sep bd dbase bw outedge cursor 257 bt (txbase + 0) (txbase + 8))
    by exact (HSep (bt, txbase + 0, txbase + 8) ltac:(simpl; auto)).
  assert (S3 : out_sep bd dbase bw outedge cursor 257 bin inbase (inbase + 160 * nn))
    by exact (HSep (bin, inbase, inbase + 160 * nn) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor 257 GC 0 8)
    by exact (HSep (GC, 0, 8) ltac:(do 3 right; left; reflexivity)).
  assert (S5 : out_sep bd dbase bw outedge cursor 257 GM 0 8)
    by exact (HSep (GM, 0, 8) ltac:(do 4 right; left; reflexivity)).
  clear HSep.
  apply frame_input_word_at_encode in Hin.
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct (wide_input_first_load W32 m bi edge rc a Hin) as [w0i Hw0i].
  assert (Vi : Mem.valid_block m bi) by (eapply load_valid_block; exact Hw0i).
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 257 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMaxC).
  assert (Vbe : Mem.valid_block m be) by (eapply load_valid_block; exact HLtx).
  assert (Vbt : Mem.valid_block m bt) by (eapply load_valid_block; exact HLin).
  (* locals *)
  destruct (Mem.alloc m 0 16) as [ma1 bl] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bm] eqn:A2.
  destruct (Mem.alloc ma2 0 88) as [ma3 bx] eqn:A3.
  destruct (Mem.alloc ma3 0 88) as [m0 br] eqn:A4.
  assert (HAL : alloc_list m [16; 32; 88; 88] = (m0, [bl; bm; bx; br])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PL0 VL0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PM0 VM0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PX0 VX0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PR0 VR0] FA4]; subst. clear FA FA1 FA2 FA3 FA4 HAL.
  apply NoDup_cons_iff in ND. destruct ND as [N1 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N2 ND].
  apply NoDup_cons_iff in ND. destruct ND as [N3 _].
  pose proof (FRh bi Vi) as Nbi. pose proof (FRh bs Vs) as Nbs.
  pose proof (FRh bd Vd) as Nbd. pose proof (FRh bw Vw) as Nbw.
  pose proof (FRh GC VG) as NGC. pose proof (FRh GM VM) as NGM.
  set (e := iu_env bl bm bx br).
  set (le := iu_temps (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase).
  (* the frame copy *)
  assert (HSE0 : Mem.load Mptr m0 bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSO0 : Mem.load Mint64 m0 bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_loadbytes_at m0 bs sbase _ _ HSE0 HSO0) as [bytes HB0].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB0) as Hbyteslen.
  assert (PLW : Mem.range_perm m0 bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm m0 bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL0; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes m0 bl 0 bytes PLW) as [mc SC].
  destruct (frame_copy_fields_at m0 mc bs sbase bl bytes _ _ HB0 SC HSE0 HSO0) as [HLE HLO].
  assert (Kc : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mc b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    erewrite Mem.load_storebytes_other; [|exact SC|left; ne]. apply XL. exact Hv. }
  assert (Pc : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mc b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; eauto. }
  assert (Vc : forall b0, Mem.valid_block m0 b0 -> Mem.valid_block mc b0).
  { intros b0 Hv. eapply Mem.storebytes_valid_block_1; eauto. }
  assert (HCopy : Clight2.exec_stmt sha_ge e le m0 (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal).
  { apply (iu_copy m0 mc bl bm bx br bs sbase bytes le);
      [exact HSbase|exact HSAlign|ne|reflexivity|exact HB0|exact SC]. }
  (* read32 *)
  assert (HInputC : frame_input_word_at mc bi edge rc a).
  { eapply frame_input_bits_at_preserved; [|exact Hin].
    intros ofs w HL. rewrite Kc by exact Vi. exact HL. }
  assert (PLC : Mem.valid_access mc Mint64 bl (0 + 8) Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. change (size_chunk Mint64) with 8 in Hr.
    eapply Mem.perm_implies; [apply Pc, PL0; lia|constructor]. }
  destruct (eval_read_wide_word_at W32 mc bl 0 bi edge rc a HLocalBase ltac:(change (wide_bits W32) with 32; lia)
    (conj HLE HLO) HInputC PLC ltac:(ne))
    as (mr & r & Hread & Hr & HRFields & HRMem & HRPerm & HRValid).
  assert (Hr5 : Int64.unsigned r = @toZ (WordToZ 5) a) by exact Hr.
  destruct (wide_reader_helper W32) as [rid Hrin].
  apply (sha_transport_call _ _ Hrin) in Hread.
  change (wide_reader W32) with jets.f_simplicity_read32 in Hread.
  assert (Kr : forall ch b0 ofs, Mem.valid_block m b0 -> Mem.load ch mr b0 ofs = Mem.load ch m b0 ofs).
  { intros ch b0 ofs Hv. pose proof (FRh b0 Hv) as Nb.
    rewrite HRMem by (left; ne). apply Kc. exact Hv. }
  assert (Pr : forall b0 ofs kd p, Mem.perm m0 b0 ofs kd p -> Mem.perm mr b0 ofs kd p).
  { intros b0 ofs kd p Hp. apply HRPerm, Pc, Hp. }
  assert (Vr : forall b0, Mem.valid_block m b0 -> Mem.valid_block mr b0).
  { intros b0 Hv. apply HRValid, Vc, XV, Hv. }
  (* writeBit *)
  assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor 257).
  { eapply write_frame_at_preserved; [| |exact Hout].
    - intros ch b0 ofs v0 Hb HL. rewrite Kr; [exact HL|destruct Hb; subst; assumption].
    - intros b0 ofs kd p Hp. apply Pr, XP, Hp. }
  assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
  { eapply write_frame_at_shorter; [|exact HFrameR]. lia. }
  destruct (shx_writeBit_step mr bd dbase bw outedge cursor (Int64.ltu r nI) HF1) as (mb & Hwb1 & E1).
  assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) 256).
  { eapply write_frame_at_after_effect with (cells := [Some (Int64.ltu r nI)]);
      [reflexivity|lia|exact HFrameR|exact E1]. }
  assert (HLoadB : forall chunk b lo hi ofs, out_sep bd dbase bw outedge cursor 257 b lo hi ->
    lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b ofs = Mem.load chunk mr b ofs).
  { intros chunk b lo hi ofs Hs Hlo Hhi.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 257) (n := 1)
      (cells := [Some (Int64.ltu r nI)]) (lo := lo) (hi := hi);
      [lia|destruct HF1 as (_ & _ & _ & HC1 & _); lia|lia|lia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
  destruct E1 as (O1 & P1 & F1 & L1 & Pm1 & V1) eqn:HE1.
  assert (E1' : write_effect mr mb bd dbase bw outedge cursor 1 [Some (Int64.ltu r nI)])
    by exact (conj O1 (conj P1 (conj F1 (conj L1 (conj Pm1 V1))))).
  clear HE1.
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  assert (HE0 : Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)))
    by (rewrite Kr by exact Vbe; exact HLtx).
  assert (HE2 : Mem.load Mint64 mr bt (txbase + 448) = Some (Vlong nI))
    by (rewrite Kr by exact Vbt; exact HLn).
  set (specv := @vh_hash_spec (BitcoinFull.Base Bitcoin.InputValue)
    (BitcoinFull.Ext BitcoinExt.InputScriptHash) fullalg a env0).
  pose proof (extInScriptHash_len env0) as HShLen. fold outs in HShLen.
  (* the two branches *)
  assert (HTotal : exists V le1 me,
    specv = Some V /\
    Clight2.exec_stmt sha_ge e le mc (shx_indexed_rest _t'6 _t'7 _numInputs iu_then iu_else)
      E0 le1 me shx_returned_one /\
    frame_output_cells_at me bw outedge cursor (encode V) /\
    write_prefix_at mr me bw outedge cursor /\
    frame_fields_at me bd dbase bw outedge (cursor - 257) /\
    (forall ch b0 ofs, Mem.valid_block m b0 ->
      (b0 <> bd \/ ofs + size_chunk ch <= dbase + 8 \/ dbase + 16 <= ofs) ->
      (b0 <> bw \/ ofs + size_chunk ch <= outedge + 8 * ((cursor - 257) / 64) \/
        write_word_address outedge cursor + 8 <= ofs) ->
      Mem.load ch me b0 ofs = Mem.load ch mr b0 ofs) /\
    (forall b0 ofs kd p, Mem.perm mb b0 ofs kd p -> Mem.perm me b0 ofs kd p)).
  { destruct (Int64.ltu r nI) eqn:Hb.
    - (* in range *)
      assert (Hlt : Int64.unsigned r < nn).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [|discriminate].
        rewrite HnI in Hl. exact Hl. }
      destruct (nth_error outs (Z.to_nat (Int64.unsigned r))) as [o|] eqn:Hnth;
        [|apply nth_error_None in Hnth; unfold nn in Hlt; lia].
      destruct (nth_error (extInScriptHash env0) (Z.to_nat (Int64.unsigned r))) as [H|] eqn:HnthS;
        [|apply nth_error_None in HnthS; unfold nn in Hlt; lia].
      set (ofs := inbase + 160 * Int64.unsigned r + 104).
      assert (Hm : 160 * Int64.unsigned r + 160 <= 160 * nn) by lia.
      destruct (HLelem _ _ _ Hnth HnthS) as [HVal HScr]. rewrite Z2Nat.id in HVal, HScr by lia.
      fold ofs in HVal, HScr.
      set (xv := sigTxiValue o) in *.
      assert (Vbin : Mem.valid_block m bin) by (eapply load_valid_block; exact HVal).
      pose proof (FRh bin Vbin) as Nbin. pose proof (FRh be Vbe) as Nbe. pose proof (FRh bt Vbt) as Nbt.
      (* the specification *)
      assert (HSpec : specv = Some (inr (from_hash256 (sha256_bytes_of
        (vh_bytes (@fromZ (WordToZ 6) (Int64.signed xv)) (from_hash256 H)))))).
      { unfold specv. apply vh_hash_spec_some.
        - rewrite input_values_sem. unfold input_values_of, wz. fold outs.
          rewrite nth_error_map, <- Hr5, Hnth. reflexivity.
        - rewrite input_scripts_sem. unfold input_scripts_of, wz.
          rewrite nth_error_map, <- Hr5, HnthS. reflexivity. }
      (* memory facts after writeBit *)
      assert (Kb : forall ch b0 lo hi o0, out_sep bd dbase bw outedge cursor 257 b0 lo hi ->
        Mem.valid_block m b0 -> lo <= o0 -> o0 + size_chunk ch <= hi ->
        Mem.load ch mb b0 o0 = Mem.load ch m b0 o0).
      { intros ch b0 lo hi o0 Hs Hv Hlo Hhi. rewrite (HLoadB ch b0 lo hi o0 Hs Hlo Hhi). apply Kr. exact Hv. }
      assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
      { rewrite (Kb Mptr be ebase (ebase + 8)); [exact HLtx|exact S1|exact Vbe|lia|change (size_chunk Mptr) with 8; lia]. }
      assert (Hmb1 : Mem.load Mptr mb bt (txbase + 0) = Some (Vptr bin (Ptrofs.repr inbase))).
      { rewrite (Kb Mptr bt (txbase + 0) (txbase + 8)); [exact HLin|exact S2|exact Vbt|lia|change (size_chunk Mptr) with 8; lia]. }
      assert (Pb : forall b0 ofs0 kd p, Mem.perm m0 b0 ofs0 kd p -> Mem.perm mb b0 ofs0 kd p).
      { intros b0 ofs0 kd p Hp. apply Pm1, Pr, Hp. }
      assert (Vb : forall b0, Mem.valid_block m b0 -> Mem.valid_block mb b0).
      { intros b0 Hv. apply V1, Vr, Hv. }
      (* the context *)
      destruct (ctxi_init bx bm ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) mb br
        ltac:(ne) ltac:(ne) (Vb _ VG) (Vb _ VM) ltac:(ne) ltac:(ne)
        ltac:(intros o0 Hr1; apply Pb, PR0, Hr1) ltac:(intros o0 Hr1; apply Pb, PX0, Hr1)
        ltac:(intros o0 Hr1; apply Pb, PM0, Hr1))
        as (mi & mx & ibytes & HInit & HLBi & HSBi & HAx & HLx & HPx & HVx).
      { unfold sha_dispatch_ok.
        rewrite (Kb Mptr GC 0 8); [exact Hdisp|exact S4|exact VG|lia|change (size_chunk Mptr) with 8; lia]. }
      { rewrite (Kb Mint64 GM 0 8); [exact HMaxC|exact S5|exact VM|lia|change (size_chunk Mint64) with 8; lia]. }
      assert (Kx : forall ch b0 o0, Mem.valid_block m b0 -> Mem.load ch mx b0 o0 = Mem.load ch mb b0 o0).
      { intros ch b0 o0 Hv. pose proof (FRh b0 Hv) as Nb. apply HLx; [apply Vb; exact Hv|ne|ne|ne]. }
      pose proof (ctxi_u64be bx bm ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
        mx [] sha256_iv_words xv _ _ HAx) as HU7.
      cbv zeta in HU7. destruct HU7 as (m7 & HUc7 & HA7 & HL7 & HP7 & HV7).
      rewrite (absorb_i_small (c_be64_bytes xv) [] sha256_iv_words) in HA7 by (cbn; lia).
      cbn [fst snd app] in HA7.
      assert (K7 : forall ch b0 o0, Mem.valid_block m b0 -> Mem.load ch m7 b0 o0 = Mem.load ch mb b0 o0).
      { intros ch b0 o0 Hv. pose proof (FRh b0 Hv) as Nb.
        rewrite HL7; [apply Kx; exact Hv|apply HVx, Vb; exact Hv|ne|ne]. }
      assert (HofsU : Ptrofs.unsigned (Ptrofs.repr (ofs + 8)) = ofs + 8).
      { apply Ptrofs.unsigned_repr. unfold ofs. lia. }
      assert (HScr7 : forall j, (j < 8)%nat ->
        Mem.load Mint32 m7 bin (Ptrofs.unsigned (Ptrofs.repr (ofs + 8)) + 4 * Z.of_nat j) =
          Some (Vint (nth j (hash256_reg H) Int.zero))).
      { intros j Hj. rewrite HofsU, K7 by exact Vbin.
        rewrite (Kb Mint32 bin inbase (inbase + 160 * nn));
          [|exact S3|exact Vbin|unfold ofs; lia|change (size_chunk Mint32) with 4; unfold ofs; lia].
        apply (u32_nth m bin (ofs + 8) (hash256_reg H) HScr). rewrite (hash256_len H). exact Hj. }
      pose proof (ctxi_hash bx bm ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
        m7 bin (Ptrofs.repr (ofs + 8)) (c_be64_bytes xv) sha256_iv_words (hash256_reg H) _ _ HA7
        (hash256_len H) ltac:(rewrite HofsU; unfold ofs; lia) HScr7) as HH8.
      cbv zeta in HH8. destruct HH8 as (m8 & HHc8 & HA8 & HL8 & HP8 & HV8).
      assert (HbH : length (be_bytes (hash256_reg H)) = 32%nat)
        by (rewrite be_bytes_length, (hash256_len H); reflexivity).
      rewrite (absorb_i_small (be_bytes (hash256_reg H)) (c_be64_bytes xv) sha256_iv_words) in HA8
        by (rewrite HbH; cbn; lia).
      cbn [fst snd] in HA8.
      change (Int64.add (Int64.add Int64.zero (Int64.repr 8)) (Int64.repr 32)) with (Int64.repr 40) in HA8.
      destruct (ctxi_finalize bx bm ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) ltac:(ne) Hmodel
        m8 _ _ _ _ HA8) as (m9 & HFin9 & HReg9 & HL9 & HP9 & HV9).
      rewrite vh_regs_eq in HReg9.
      set (RES := sha256_bytes_of (vh_bytes (@fromZ (WordToZ 6) (Int64.signed xv)) (from_hash256 H))) in *.
      assert (K9 : forall ch b0 o0, Mem.valid_block m b0 -> Mem.load ch m9 b0 o0 = Mem.load ch mb b0 o0).
      { intros ch b0 o0 Hv. pose proof (FRh b0 Hv) as Nb.
        rewrite HL9; [|apply HV8, HV7, HVx, Vb; exact Hv|ne|ne].
        rewrite HL8; [|apply HV7, HVx, Vb; exact Hv|ne|ne]. apply K7. exact Hv. }
      assert (P9 : forall b0 o0 kd p, Mem.perm mb b0 o0 kd p -> Mem.perm m9 b0 o0 kd p).
      { intros b0 o0 kd p Hp.
        assert (Hpx : Mem.perm mx b0 o0 kd p) by (apply HPx, Hp).
        assert (Hp7 : Mem.perm m7 b0 o0 kd p) by (apply HP7; [eapply Mem.perm_valid_block; exact Hpx|exact Hpx]).
        assert (Hp8 : Mem.perm m8 b0 o0 kd p) by (apply HP8; [eapply Mem.perm_valid_block; exact Hp7|exact Hp7]).
        apply HP9; [eapply Mem.perm_valid_block; exact Hp8|exact Hp8]. }
      (* writeHash *)
      assert (HOut9 : write_frame_at m9 bd dbase bw outedge (cursor - 1) 256).
      { eapply write_frame_at_preserved; [| |exact HFb].
        - intros ch b0 o0 v0 Hb0 HL. rewrite K9; [exact HL|destruct Hb0; subst; assumption].
        - exact P9. }
      assert (HArr9 : uint32_array_at m9 bm 0 (hash256_reg RES)).
      { apply u32_of_nth. intros j Hj. rewrite (hash256_len RES) in Hj. apply HReg9. exact Hj. }
      destruct (eval_sha_writeHash m9 bm 0 bd dbase bw outedge (cursor - 1) (hash256_reg RES)
        (hash256_len RES) ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
        ltac:(ne) ltac:(ne) HArr9 HOut9)
        as (m10 & HWr & HCells & HPrefix & HFldE & HLoadsE & HPermE & HValE).
      assert (E2 : write_effect m9 m10 bd dbase bw outedge (cursor - 1) 256 (uint32_word_cells (hash256_reg RES)))
        by exact (conj HCells (conj HPrefix (conj HFldE (conj HLoadsE (conj HPermE HValE))))).
      destruct (write_cells_seq mr mb m9 m10 bd dbase bw outedge cursor 1 256 [Some true]
        (uint32_word_cells (hash256_reg RES)) eq_refl ltac:(lia) HFrameR E1'
        ltac:(intros ch o0; apply K9; exact Vw) E2) as (HC & HPf & HFl).
      exists (inr (from_hash256 RES)).
      (* execution of the branch *)
      destruct (exec_shx_indexed_rest _t'6 _t'7
        ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
        e le _numInputs 448 iu_then iu_else mc mr mb be ebase bt txbase bl bd dbase r nI
        (fun me => me = m10)) as (le1 & me & HEx & HPost).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact Hread.
      + exact He0.
      + lia.
      + exact Ht0.
      + lia.
      + lia.
      + exact shx_bitcoinTransaction_numInputs.
      + exact HE0.
      + exact HE2.
      + rewrite Hb. exact Hwb1.
      + intros le' Hi' Hd' He' _.
        set (le2 := PTree.set _t'4 (Vptr bt (Ptrofs.repr txbase)) le').
        set (le3 := PTree.set _t'5 (Vptr bin (Ptrofs.repr inbase)) le2).
        set (le4 := PTree.set _txo (Vptr bin (Ptrofs.repr ofs)) le3).
        set (le5 := PTree.set _t'3 (Vlong xv) le4).
        assert (Hd5 : le5!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
        { unfold le5, le4, le3, le2. rewrite !PTree.gso by discriminate. exact Hd'. }
        assert (Ho4 : le4!_txo = Some (Vptr bin (Ptrofs.repr ofs))) by (unfold le4; apply PTree.gss).
        assert (Ho5 : le5!_txo = Some (Vptr bin (Ptrofs.repr ofs))).
        { unfold le5. rewrite PTree.gso by discriminate. exact Ho4. }
        exists le5, m10. split; [|reflexivity].
        unfold iu_then.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mb).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mb).
          - apply exec_Sset.
            eapply eval_shx_field_value with (sid := _txEnv) (delta := 0) (chunk := Mptr).
            + reflexivity.
            + exact iu_env_tx.
            + reflexivity.
            + apply eval_shx_deref_struct. exact He'.
            + rewrite shx_ptr_add_repr by lia. apply shx_loadv_repr; [lia|exact Hmb0].
          - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le3) (m1 := mb).
            + apply exec_Sset.
              eapply eval_shx_field_value with (sid := _bitcoinTransaction) (delta := 0) (chunk := Mptr).
              * reflexivity.
              * exact shx_bitcoinTransaction_input.
              * reflexivity.
              * apply eval_shx_deref_struct. unfold le2. apply PTree.gss.
              * rewrite shx_ptr_add_repr by lia. apply shx_loadv_repr; [lia|exact Hmb1].
            + apply exec_Sset.
              apply (eval_shx_elem_field_addr e le3 mb _t'5 _i _sigInput 160 _txo 104 _sigOutput bin inbase r
                shx_sizeof_sigInput shx_sigInput_txo).
              * unfold le3. apply PTree.gss.
              * unfold le3, le2. rewrite !PTree.gso by discriminate. exact Hi'.
              * exact Hi0.
              * lia.
              * lia.
              * lia.
              * lia. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mx).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le4) (m1 := mi).
          - change le4 with (set_opttemp None Vundef le4) at 2.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
              (vargs := [Vptr br Ptrofs.zero; Vptr bm Ptrofs.zero]) (f := Internal jets.f_sha256_init).
            + reflexivity.
            + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact tap_init_symbol]|].
              apply deref_loc_reference; reflexivity.
            + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs; [apply eval_local_mid_s; reflexivity|reflexivity|apply eval_Enil].
            + exact tap_init_funct.
            + reflexivity.
            + exact HInit.
          - eapply (exec_ctx_struct_copy e le4 mi mx _ctx __res bx br ibytes);
              [reflexivity|reflexivity|ne|exact HLBi|exact HSBi]. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m7).
        { eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := mx).
          - apply exec_Sset.
            eapply eval_shx_field_value with (sid := _sigOutput) (delta := 0) (chunk := Mint64).
            + reflexivity.
            + exact iu_so_value.
            + reflexivity.
            + apply eval_shx_deref_struct. exact Ho4.
            + rewrite shx_ptr_add_repr by (unfold ofs; lia). apply shx_loadv_repr; [unfold ofs; lia|].
              rewrite Z.add_0_r, Kx by exact Vbin.
              rewrite (Kb Mint64 bin inbase (inbase + 160 * nn));
                [exact HVal|exact S3|exact Vbin|unfold ofs; lia|change (size_chunk Mint64) with 8; unfold ofs; lia].
          - match type of HUc7 with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
              change le5 with (set_opttemp None vr le5) at 2 end.
            eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_u64be) Ptrofs.zero)
              (vargs := [Vptr bx Ptrofs.zero; Vlong xv]) (f := Internal f_sha256_u64be).
            + reflexivity.
            + eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_u64be_symbol]|].
              apply deref_loc_reference; reflexivity.
            + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
              eapply eval_Econs; [apply eval_Etempvar; unfold le5; apply PTree.gss|reflexivity|apply eval_Enil].
            + exact sha_u64be_funct.
            + reflexivity.
            + exact HUc7. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m8).
        { change le5 with (set_opttemp None Vundef le5) at 2.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_hash) Ptrofs.zero)
            (vargs := [Vptr bx Ptrofs.zero; Vptr bin (Ptrofs.repr (ofs + 8))]) (f := Internal f_sha256_hash).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_hash_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
            eapply eval_Econs with (v1 := Vptr bin (Ptrofs.repr (ofs + 8))); [|reflexivity|apply eval_Enil].
            eapply eval_Eaddrof.
            rewrite <- (shx_ptr_add_repr ofs 8) by (unfold ofs; lia).
            eapply eval_shx_field_lvalue; [reflexivity|exact iu_so_script|].
            apply eval_shx_deref_struct. exact Ho5.
          - exact sha_hash_funct.
          - reflexivity.
          - exact HHc8. }
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le5) (m1 := m9).
        { match type of HFin9 with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
            change le5 with (set_opttemp None vr le5) at 2 end.
          eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_finalize) Ptrofs.zero)
            (vargs := [Vptr bx Ptrofs.zero]) (f := Internal f_sha256_finalize).
          - reflexivity.
          - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_finalize_symbol]|].
            apply deref_loc_reference; reflexivity.
          - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
          - exact sha_finalize_funct.
          - reflexivity.
          - exact HFin9. }
        change le5 with (set_opttemp None Vundef le5) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _writeHash) Ptrofs.zero)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bm Ptrofs.zero]) (f := Internal f_writeHash).
        * reflexivity.
        * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact hio_writeHash_symbol]|].
          apply deref_loc_reference; reflexivity.
        * eapply eval_Econs; [apply eval_Etempvar; exact Hd5|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
        * exact hio_writeHash_funct.
        * reflexivity.
        * exact HWr.
      + intros le' _ _ _ Hbf. rewrite Hb in Hbf. discriminate Hbf.
      + subst me. exists le1, m10. split; [exact HSpec|]. split; [exact HEx|].
        split.
        { rewrite iu_encode_some, <- uint32_cells_from_hash256. exact HC. }
        split; [exact HPf|]. split; [exact HFl|]. split.
        * intros ch b0 o0 Hv Hd Hw. pose proof (FRh b0 Hv) as Nb.
          rewrite HLoadsE.
          -- rewrite K9 by exact Hv. apply L1; [exact Hd|].
             destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw| |right; right; exact Hw].
             right; left.
             pose proof (Z.div_le_mono (cursor - 257) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia.
          -- exact Hd.
          -- destruct Hw as [Hw|[Hw|Hw]]; [left; exact Hw|right; left|right; right].
             ++ replace (cursor - 1 - 256) with (cursor - 257) by lia. exact Hw.
             ++ unfold write_word_address in *.
                pose proof (Z.div_le_mono (cursor - 1 - 1) (cursor - 1) 64 ltac:(lia) ltac:(lia)). lia.
        * intros b0 o0 kd p Hp. apply HPermE, P9, Hp.
    - (* out of range *)
      assert (Hge : nn <= Int64.unsigned r).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [discriminate|].
        rewrite HnI in Hnl. lia. }
      assert (Hnth : nth_error outs (Z.to_nat (Int64.unsigned r)) = None).
      { apply nth_error_None. unfold nn in Hge. lia. }
      assert (HSpec : specv = Some (inl tt)).
      { unfold specv.
        apply (vh_hash_spec_none _ _ a env0 (inl tt)).
        - rewrite input_values_sem. unfold input_values_of, wz. fold outs.
          rewrite nth_error_map, <- Hr5, Hnth. reflexivity.
        - assert (HnthS : nth_error (extInScriptHash env0) (Z.to_nat (Int64.unsigned r)) = None)
            by (apply nth_error_None; unfold nn in Hge; lia).
          rewrite input_scripts_sem. unfold input_scripts_of, wz.
          rewrite nth_error_map, <- Hr5, HnthS. reflexivity. }
      destruct (shx_skipBits_step mb bd dbase bw outedge (cursor - 1) 256 HFb) as (me & HCallS & E2).
      change (Z.of_nat 256) with 256 in HCallS, E2.
      pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 256 [Some false]
        (repeat None 256) eq_refl ltac:(lia) HFrameR E1' E2) as (HC & HPf & HFl & HLs & HPs & HVs).
      exists (inl tt).
      destruct (exec_shx_indexed_rest _t'6 _t'7
        ltac:(repeat split; discriminate) ltac:(repeat split; discriminate)
        e le _numInputs 448 iu_then iu_else mc mr mb be ebase bt txbase bl bd dbase r nI
        (fun me' => me' = me)) as (le1 & me' & HEx & HPost).
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + reflexivity.
      + exact Hread.
      + exact He0.
      + lia.
      + exact Ht0.
      + lia.
      + lia.
      + exact shx_bitcoinTransaction_numInputs.
      + exact HE0.
      + exact HE2.
      + rewrite Hb. exact Hwb1.
      + intros le' _ _ _ Hbf. rewrite Hb in Hbf. discriminate Hbf.
      + intros le' Hi' Hd' He' _. exists le', me. split; [|reflexivity].
        unfold iu_else.
        assert (Hargs : eval_exprlist sha_ge e le' mb
          [Etempvar _dst FRP; Econst_int (Int.repr 256) tint]
          (Tcons FRP (Tcons tulong Tnil))
          [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr 256)]).
        { eapply eval_Econs; [apply eval_Etempvar; exact Hd'|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int|apply iu_cast256|apply eval_Enil]. }
        exact (exec_shx_helper_call e le' mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me iu_in_skipBits ltac:(reflexivity) Hargs ltac:(reflexivity) HCallS).
      + subst me'. exists le1, me. split; [exact HSpec|]. split; [exact HEx|].
        split; [rewrite iu_encode_none; exact HC|].
        split; [exact HPf|]. split; [exact HFl|]. split.
        * intros ch b0 o0 Hv Hd Hw. apply HLs; assumption.
        * intros b0 o0 kd p Hp. destruct E2 as (_ & _ & _ & _ & Pm2 & _). apply Pm2, Hp. }
  destruct HTotal as (V & le1 & me & HSpec & HEx & HCells & HPrefix & HFields & HLoads & HPerm).
  (* freeing the locals *)
  destruct (free_list_blocks [(bx, 0, 88); (bl, 0, 16); (bm, 0, 32); (br, 0, 88)] me)
    as (mf & HFL & HLf & _ & _).
  { intros b0 lo hi HIn ofs Hr1. apply HPerm, Pm1, Pr. cbn [In] in HIn.
    destruct HIn as [E|[E|[E|[E|[]]]]]; injection E as <- <- <-;
      [apply PX0|apply PL0|apply PM0|apply PR0]; exact Hr1. }
  { cbn [map fst]. nd6. }
  cbn [map fst] in HLf.
  assert (HNl : forall b0, Mem.valid_block m b0 -> ~ In b0 [bx; bl; bm; br]).
  { intros b0 Hb0 HIn. apply (FRh b0 Hb0). cbn [In] in HIn |- *. tauto. }
  exists mf, V. split; [exact HSpec|]. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le1) (m2 := me)
      (out := shx_returned_one).
    + eapply iu_entry; eassumption.
    + rewrite iu_body. eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact HCopy|exact HEx].
    + cbn. split; [discriminate|reflexivity].
    + unfold e. rewrite iu_blocks. exact HFL.
  - eapply frame_output_cells_preserved; [|exact HCells].
    intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - eapply write_prefix_at_preserved; [| |exact HPrefix].
    + intros ofs w HL. rewrite Kr by exact Vw. exact HL.
    + intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
  - destruct HFields as [HE1' HE2']. split; rewrite HLf by (apply HNl; exact Vd); assumption.
  - intros ch b0 ofs Hv Hd Hw. rewrite HLf by (apply HNl; exact Hv).
    rewrite HLoads by assumption. apply Kr; exact Hv.
Qed.
