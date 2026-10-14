(** Execution of [copyOutput(result, output)] (bitcoin/env.c):
    [result->scriptPubKey] receives the SHA-256 state of the raw script and
    [result->value] the raw value.  First step towards
    [simplicity_bitcoin_mallocTransaction]. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_readBit_layout C.jet_bitmachine_rep.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_ctx8_model.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_add_n_init C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_hashbuffer.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Notation SOUT := (Tstruct _sigOutput noattr).
Notation ROUT := (Tstruct _rawBitcoinOutput noattr).

Lemma sha_hashBuffer_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _hashBuffer = Some (sha_symbol_block _hashBuffer).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_hashBuffer_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _hashBuffer) Ptrofs.zero) =
    Some (Internal f_hashBuffer).
Proof. vm_compute; reflexivity. Qed.

Lemma envu_sigOutput_value : envu_field_at _sigOutput _value 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_sigOutput_scriptPubKey : envu_field_at _sigOutput _scriptPubKey 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawBitcoinOutput_value : envu_field_at _rawBitcoinOutput _value 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_rawBitcoinOutput_scriptPubKey : envu_field_at _rawBitcoinOutput _scriptPubKey 8.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Local Opaque sha_ge.

Theorem eval_copyOutput (Hmodel : memcpy_model) m bres ores bout oout ba oa (bs : list int) (len : int)
    (value : int64) :
  0 <= ores -> ores + 40 <= Ptrofs.max_unsigned -> (8 | ores) ->
  Mem.range_perm m bres ores (ores + 40) Cur Writable ->
  bres <> GC -> bres <> GM -> ba <> bres -> bout <> bres ->
  Mem.valid_block m ba ->
  0 <= oout -> oout + 24 <= Ptrofs.max_unsigned ->
  Mem.load Mint64 m bout oout = Some (Vlong value) ->
  Mem.load Mptr m bout (oout + 8) = Some (Vptr ba oa) ->
  Mem.load Mint32 m bout (oout + 16) = Some (Vint len) ->
  Z.of_nat (length bs) = Int.unsigned len ->
  Ptrofs.unsigned oa + Z.of_nat (length bs) <= Ptrofs.max_unsigned ->
  (forall i, (i < length bs)%nat ->
     Mem.load Mint8unsigned m ba (Ptrofs.unsigned oa + Z.of_nat i) = Some (Vint (nth i bs Int.zero))) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_copyOutput)
      [Vptr bres (Ptrofs.repr ores); Vptr bout (Ptrofs.repr oout)] E0 m' Vundef /\
    Mem.load Mint64 m' bres ores = Some (Vlong value) /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 8 + 4 * Z.of_nat j) =
         Some (Vint (nth j (hash_buffer_regs bs) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 40 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Ho0 HoM HoA PRes NG NM Nares Nout Va Hq0 HqM HVal HBuf HLen Hlen HaM HBs Hdisp HMax.
  assert (Vout : Mem.valid_block m bout) by (eapply load_valid_block; exact HVal).
  assert (Vres : Mem.valid_block m bres) by (eapply Mem.perm_valid_block; apply (PRes ores); lia).
  set (obuf := Ptrofs.add (Ptrofs.repr oout) (Ptrofs.repr 8)).
  assert (Hobuf : Ptrofs.unsigned obuf = oout + 8).
  { unfold obuf. rewrite envu_ptr_add_repr by lia. apply Ptrofs.unsigned_repr. lia. }
  destruct (eval_hashBuffer Hmodel m bres (ores + 8) bout obuf ba oa bs len
    ltac:(lia) ltac:(lia) ltac:(apply Z.divide_add_r; [destruct HoA as [k ->]; exists (2 * k); lia|exists 2; reflexivity]))
    as (m1 & HCall & HReg & HL1 & HP1 & HV1); try assumption.
  { intros o Ho. apply PRes. lia. }
  { rewrite Hobuf. lia. }
  { rewrite Hobuf. exact HBuf. }
  { rewrite Hobuf. replace (oout + 8 + 8) with (oout + 16) by lia. exact HLen. }
  destruct (Mem.valid_access_store m1 Mint64 bres ores (Vlong value)) as [m2 HS].
  { split; [|exact HoA]. intros o Ho. change (size_chunk Mint64) with 8 in Ho. apply HP1, PRes. lia. }
  set (le := PTree.set _output (Vptr bout (Ptrofs.repr oout))
    (PTree.set _result (Vptr bres (Ptrofs.repr ores)) (create_undef_temps (fn_temps f_copyOutput)))).
  exists m2. split; [|split; [|split; [|split; [|split]]]].
  - eapply eval_funcall_internal with (e := empty_env) (le1 := le) (m1 := m) (m2 := m2)
      (le2 := PTree.set _t'1 (Vlong value) le) (out := Out_normal).
    + apply function_entry2_intro.
      * apply list_norepet_nil.
      * repeat constructor; simpl; intuition discriminate.
      * intros x0 y0 HX HY; cbn in HX, HY; intuition (subst; discriminate).
      * apply alloc_variables_nil.
      * reflexivity.
    + unfold f_copyOutput. cbn [fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := m1).
      { change le with (set_opttemp None Vundef le) at 2.
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _hashBuffer) Ptrofs.zero)
          (vargs := [Vptr bres (Ptrofs.repr (ores + 8)); Vptr bout obuf]) (f := Internal f_hashBuffer).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [apply PTree.gempty|exact sha_hashBuffer_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs.
          + eapply eval_Eaddrof. eapply eval_envu_field_lvalue;
              [reflexivity|exact envu_sigOutput_scriptPubKey|apply eval_envu_deref_struct; reflexivity].
          + rewrite envu_ptr_add_repr by lia. reflexivity.
          + eapply eval_Econs;
              [eapply eval_Eaddrof; eapply eval_envu_field_lvalue;
                 [reflexivity|exact envu_rawBitcoinOutput_scriptPubKey|apply eval_envu_deref_struct; reflexivity]
              |reflexivity|apply eval_Enil].
        - exact sha_hashBuffer_funct.
        - reflexivity.
        - exact HCall. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'1 (Vlong value) le) (m1 := m1).
      { apply exec_Sset. eapply eval_envu_field_value;
          [reflexivity|exact envu_rawBitcoinOutput_value|reflexivity|apply eval_envu_deref_struct; reflexivity|].
        rewrite envu_ptr_add_repr by lia. apply envu_loadv_repr; [lia|].
        rewrite Z.add_0_r. rewrite HL1; [exact HVal|exact Vout|left; exact Nout]. }
      eapply exec_Sassign with (v2 := Vlong value) (v := Vlong value).
      * eapply eval_envu_field_lvalue;
          [reflexivity|exact envu_sigOutput_value|apply eval_envu_deref_struct; reflexivity].
      * apply eval_Etempvar. apply PTree.gss.
      * reflexivity.
      * eapply assign_loc_value; [reflexivity|]. unfold Mem.storev.
        rewrite envu_ptr_add_repr by lia. rewrite Z.add_0_r, Ptrofs.unsigned_repr by lia. exact HS.
    + cbn. reflexivity.
    + reflexivity.
  - rewrite (Mem.load_store_same _ _ _ _ _ _ HS). reflexivity.
  - intros j Hj. rewrite (Mem.load_store_other _ _ _ _ _ _ HS)
      by (right; right; change (size_chunk Mint64) with 8; lia).
    replace (ores + 8 + 4 * Z.of_nat j) with ((ores + 8) + 4 * Z.of_nat j) by lia. apply HReg, Hj.
  - intros ch b ofs Hb Hr. rewrite (Mem.load_store_other _ _ _ _ _ _ HS).
    + apply HL1; [exact Hb|]. destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; lia|right; right; lia].
    + destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr|right; left; exact Hr|right; right; change (size_chunk Mint64) with 8; lia].
  - intros b ofs k p Hp. eapply Mem.perm_store_1; [exact HS|apply HP1, Hp].
  - intros b Hb. eapply Mem.store_valid_block_1; [exact HS|apply HV1, Hb].
Qed.
