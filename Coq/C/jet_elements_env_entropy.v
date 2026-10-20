(** Execution of [simplicity_generateIssuanceEntropy(op, contract)]
    (elements/ops.c): the midstate
      compress(iv, sha256(sha256(txid bytes ++ le32(ix))) words ++ contract)
    built with two local SHA-256 contexts, [memcpy] of the contract hash and
    one compression from the initial state. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_struct_copy_loads.
Require Import C.jets_elements C.jet_elements_support_sha_linkage C.jet_elements_support_sha_block_local C.jet_elements_support_sha_block_exec C.jet_elements_support_sha_compress_call.
Require Import C.jet_sha_ctx8_model C.jet_elements_support_sha_be32_write C.jet_elements_support_sha_be64_exec C.jet_elements_support_sha_hash_exec.
Require Import C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_add_n_init C.jet_elements_support_sha_finalize_exec C.jet_elements_support_sha_tapdata_prep.
Require Import C.jet_elements_support_sha_ctx_abs C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_uchars_exec C.jet_elements_support_sha_ctxi.
Require Import C.jet_env_store_words C.jet_elements_calc_field_eval C.jet_elements_calc_field_eval.
Require Import C.jet_elements_env_ctxo C.jet_elements_env_ctxo_more C.jet_elements_env_ctxo_le.
Require Import C.jet_elements_env_ctxo_uchars C.jet_elements_env_le32_write C.jet_elements_env_u32le_exec.
Require Import C.jet_elements_env_tx_calls C.jet_elements_entropy_hash_model C.jet_elements_calculate_asset_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 300.

Local Notation BLK := (tarray tuint 16).
Local Notation BUFT := (tarray tuchar 32).
Local Notation OPT := (Tstruct _outpoint noattr).
Local Notation RS := (Efield (Evar _result MID) _s (tarray tuint 8)).
Local Notation TINIT :=
  (Tfunction (Tcons CTXP (Tcons (tptr tuint) Tnil)) tvoid
     {| cc_vararg := None; cc_unproto := false; cc_structret := true |}).

Definition ent_init_stmt (idres idctx : ident) (aout : expr) : statement :=
  Ssequence (Scall None (Evar _sha256_init TINIT) [Eaddrof (Evar idres CTX) CTXP; aout])
    (Sassign (Evar idctx CTX) (Evar idres CTX)).
Definition ent_from_stmt (asrc : expr) : statement :=
  Scall None (Evar _sha256_fromMidstate (Tfunction (Tcons (tptr tuchar) (Tcons (tptr tuint) Tnil)) tvoid cc_default))
    [Evar _buf BUFT; asrc].
Definition ent_uchars_stmt (idctx : ident) : statement :=
  Scall None (Evar _sha256_uchars (Tfunction (Tcons CTXP (Tcons (tptr tuchar) (Tcons tulong Tnil))) tbool cc_default))
    [Eaddrof (Evar idctx CTX) CTXP; Evar _buf BUFT; Econst_int (Int.repr 32) tint].
Definition ent_u32le_stmt (idctx : ident) : statement :=
  Scall None (Evar _sha256_u32le (Tfunction (Tcons CTXP (Tcons tulong Tnil)) tbool cc_default))
    [Eaddrof (Evar idctx CTX) CTXP; Etempvar _t'2 tulong].
Definition ent_final_stmt (idctx : ident) : statement :=
  Scall None (Evar _sha256_finalize (Tfunction (Tcons CTXP Tnil) tbool cc_default))
    [Eaddrof (Evar idctx CTX) CTXP].
Definition ent_memcpy : statement :=
  Scall None
    (Evar _memcpy (Tfunction (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tulong Tnil))) (tptr tvoid) cc_default))
    [Ebinop Oadd (Evar _block BLK) (Econst_int (Int.repr 8) tint) (tptr tuint);
     Efield (Ederef (Etempvar _contract (tptr MID)) MID) _s (tarray tuint 8);
     Esizeof (tarray tuint 8) tulong].
Definition ent_optx : expr :=
  Efield (Efield (Ederef (Etempvar _op (tptr OPT)) OPT) _txid MID) _s (tarray tuint 8).
Definition ent_block0 : expr := Ebinop Oadd (Evar _block BLK) (Econst_int (Int.repr 0) tint) (tptr tuint).

Definition ent_phase1 : statement :=
  Ssequence (ent_init_stmt __res__2 _ctx RS)
    (Ssequence (ent_from_stmt ent_optx)
      (Ssequence (ent_uchars_stmt _ctx)
        (Ssequence
          (Ssequence (Sset _t'2 (Efield (Ederef (Etempvar _op (tptr OPT)) OPT) _ix tulong))
             (ent_u32le_stmt _ctx))
          (ent_final_stmt _ctx)))).
Definition ent_phase2 : statement :=
  Ssequence (ent_init_stmt __res__1 _ctx__1 ent_block0)
    (Ssequence (ent_from_stmt RS)
      (Ssequence (ent_uchars_stmt _ctx__1) (ent_final_stmt _ctx__1))).

Lemma entropy_body_shape :
  fn_body f_simplicity_generateIssuanceEntropy =
    Ssequence ent_phase1 (Ssequence ent_phase2 (Ssequence ent_memcpy (calc_tail _t'1))).
Proof. reflexivity. Qed.

Lemma sha_u32le_symbol_e :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_u32le = Some (sha_symbol_block _sha256_u32le).
Proof. vm_compute; reflexivity. Qed.
Lemma sha_u32le_funct_e :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_u32le) Ptrofs.zero) =
    Some (Internal f_sha256_u32le).
Proof. vm_compute; reflexivity. Qed.

Definition ent_env (bB bBuf bR bC bC1 bR1 bR2 : block) : env :=
  PTree.set __res__2 (bR2, CTX) (PTree.set __res__1 (bR1, CTX) (PTree.set _ctx__1 (bC1, CTX)
    (PTree.set _ctx (bC, CTX) (PTree.set _result (bR, MID) (PTree.set _buf (bBuf, BUFT)
      (PTree.set _block (bB, BLK) empty_env)))))).

Lemma ent_blocks bB bBuf bR bC bC1 bR1 bR2 :
  blocks_of_env sha_ge (ent_env bB bBuf bR bC bC1 bR1 bR2) =
    [(bC1, 0, 88); (bC, 0, 88); (bR2, 0, 88); (bR1, 0, 88); (bBuf, 0, 32); (bB, 0, 64); (bR, 0, 32)].
Proof. vm_compute. reflexivity. Qed.

Lemma envu_outpoint_txid_e : envu_field_at _outpoint _txid 0.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.
Lemma envu_outpoint_ix_e : envu_field_at _outpoint _ix 32.
Proof. apply envu_field_offset_at. vm_compute; reflexivity. Qed.

Lemma ent_entry m m1 m2 m3 m4 m5 m6 m7 bB bBuf bR bC bC1 bR1 bR2 vres vop vcon :
  Mem.alloc m 0 64 = (m1, bB) -> Mem.alloc m1 0 32 = (m2, bBuf) -> Mem.alloc m2 0 32 = (m3, bR) ->
  Mem.alloc m3 0 88 = (m4, bC) -> Mem.alloc m4 0 88 = (m5, bC1) -> Mem.alloc m5 0 88 = (m6, bR1) ->
  Mem.alloc m6 0 88 = (m7, bR2) ->
  function_entry2 sha_ge f_simplicity_generateIssuanceEntropy [vres; vop; vcon] m
    (ent_env bB bBuf bR bC bC1 bR1 bR2)
    (PTree.set _contract vcon (PTree.set _op vop (PTree.set __res vres
       (create_undef_temps (fn_temps f_simplicity_generateIssuanceEntropy))))) m7.
Proof.
  intros A1 A2 A3 A4 A5 A6 A7. constructor.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - cbn. repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy. cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst; try contradiction; discriminate.
  - eapply alloc_variables_cons with (m1 := m1) (b1 := bB); [change (Mem.alloc m 0 64 = (m1, bB)); exact A1|].
    eapply alloc_variables_cons with (m1 := m2) (b1 := bBuf); [change (Mem.alloc m1 0 32 = (m2, bBuf)); exact A2|].
    eapply alloc_variables_cons with (m1 := m3) (b1 := bR); [rewrite calc_sizeof_MID; exact A3|].
    eapply alloc_variables_cons with (m1 := m4) (b1 := bC); [change (Mem.alloc m3 0 88 = (m4, bC)); exact A4|].
    eapply alloc_variables_cons with (m1 := m5) (b1 := bC1); [change (Mem.alloc m4 0 88 = (m5, bC1)); exact A5|].
    eapply alloc_variables_cons with (m1 := m6) (b1 := bR1); [change (Mem.alloc m5 0 88 = (m6, bR1)); exact A6|].
    eapply alloc_variables_cons with (m1 := m7) (b1 := bR2); [change (Mem.alloc m6 0 88 = (m7, bR2)); exact A7|].
    constructor.
  - reflexivity.
Qed.

Local Opaque sha_ge.

(** One hashing phase with a local context [idctx] (scratch [idres]) whose
    output is [(bo, obase)], through the byte buffer [_buf]. *)
Section Phase.
Variable Hmodel : memcpy_model.
Variables (e : env) (idctx idres : ident) (bx br bBuf bo : block) (obase : Z).
Hypothesis Hx : e!idctx = Some (bx, CTX).
Hypothesis Hr : e!idres = Some (br, CTX).
Hypothesis Hb : e!_buf = Some (bBuf, BUFT).
Hypothesis Hg1 : e!_sha256_init = None.
Hypothesis Hg2 : e!_sha256_fromMidstate = None.
Hypothesis Hg3 : e!_sha256_uchars = None.
Hypothesis Hg4 : e!_sha256_u32le = None.
Hypothesis Hg5 : e!_sha256_finalize = None.
Hypothesis Hox : bo <> bx.
Hypothesis Hrx : br <> bx.
Hypothesis Hro : br <> bo.
Hypothesis Hbx : bBuf <> bx.
Hypothesis Hbo : bBuf <> bo.
Hypothesis Hgx : GC <> bx.
Hypothesis Hgo : GC <> bo.
Hypothesis Hcx : GM <> bx.
Hypothesis Hco : GM <> bo.
Hypothesis Hgr : GC <> br.
Hypothesis Hcr : GM <> br.
Hypothesis Hgb : GC <> bBuf.
Hypothesis Hcb : GM <> bBuf.
Hypothesis Hob : 0 <= obase /\ obase + 32 <= Ptrofs.max_unsigned.
Hypothesis HoA : (4 | obase).

Lemma ent_init_exec le m (aout : expr) :
  (forall m', eval_expr sha_ge e le m' aout (Vptr bo (Ptrofs.repr obase))) ->
  (forall m', sem_cast (Vptr bo (Ptrofs.repr obase)) (typeof aout) (tptr tuint) m' =
              Some (Vptr bo (Ptrofs.repr obase))) ->
  Mem.valid_block m GC -> Mem.valid_block m GM ->
  Mem.range_perm m br 0 88 Cur Freeable -> Mem.range_perm m bx 0 88 Cur Freeable ->
  Mem.range_perm m bo obase (obase + 32) Cur Writable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists mx,
    Clight2.exec_stmt sha_ge e le m (ent_init_stmt idres idctx aout) E0 le mx Out_normal /\
    ctxo mx bx bo obase [] sha256_iv_words Int64.zero false /\
    (forall ch b ofs, Mem.valid_block m b -> b <> br -> b <> bx ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch mx b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm mx b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block mx b).
Proof.
  intros HA HCa VG VM PR PX PO Hdisp HMax.
  destruct ctxo_init with (bx := bx) (bo := bo) (obase := obase) (m := m) (br := br)
    as (mi & mx & bytes & HInit & HLB & HSB & HC & HL & HP & HV); try assumption.
  exists mx. split; [|split; [exact HC|split; [exact HL|split; [exact HP|exact HV]]]].
  unfold ent_init_stmt.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi).
  - change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_init) Ptrofs.zero)
      (vargs := [Vptr br Ptrofs.zero; Vptr bo (Ptrofs.repr obase)]) (f := Internal jets.f_sha256_init).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg1|exact tap_init_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hr|reflexivity|].
      eapply eval_Econs; [apply HA|apply HCa|apply eval_Enil].
    + exact tap_init_funct.
    + reflexivity.
    + exact HInit.
  - eapply (exec_ctx_struct_copy e le mi mx idctx idres bx br bytes);
      [exact Hx|exact Hr|apply not_eq_sym; exact Hrx|exact HLB|exact HSB].
Qed.

Lemma ent_ev_buf le m : eval_expr sha_ge e le m (Evar _buf BUFT) (Vptr bBuf Ptrofs.zero).
Proof. eapply eval_Elvalue; [apply eval_Evar_local; exact Hb|apply deref_loc_reference; reflexivity]. Qed.

(** [sha256_fromMidstate(buf, src); sha256_uchars(&ctx, buf, 32);] *)
Lemma ent_from_uchars_exec le m (asrc : expr) bsrc osrc (regsS l regs : list int) c ovf :
  ctxo m bx bo obase l regs c ovf ->
  (forall m', eval_expr sha_ge e le m' asrc (Vptr bsrc osrc)) ->
  (forall m', sem_cast (Vptr bsrc osrc) (typeof asrc) (tptr tuint) m' = Some (Vptr bsrc osrc)) ->
  bBuf <> bsrc -> length regsS = 8%nat -> Ptrofs.unsigned osrc + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bsrc (Ptrofs.unsigned osrc + 4 * Z.of_nat j) = Some (Vint (nth j regsS Int.zero))) ->
  Mem.range_perm m bBuf 0 32 Cur Writable ->
  exists m1 m2,
    Clight2.exec_stmt sha_ge e le m (ent_from_stmt asrc) E0 le m1 Out_normal /\
    Clight2.exec_stmt sha_ge e le m1 (ent_uchars_stmt idctx) E0 le m2 Out_normal /\
    ctxo m2 bx bo obase (fst (absorb_i l regs (be_bytes regsS))) (snd (absorb_i l regs (be_bytes regsS)))
      (Int64.add c (Int64.repr 32)) (uc_overflow ovf c (Int64.repr 32)) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx -> b <> bBuf ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m2 b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m2 b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m2 b).
Proof.
  intros HC HA HCa Hbs HlenS HsM HS PB.
  destruct (eval_sha_fromMidstate m bBuf Ptrofs.zero bsrc osrc regsS Hbs HlenS
    ltac:(change (Ptrofs.unsigned Ptrofs.zero) with 0; change Ptrofs.max_unsigned with 18446744073709551615; lia)
    HsM HS PB) as (m1 & HF & HBy & L1 & P1 & V1).
  change (Ptrofs.unsigned Ptrofs.zero) with 0 in HBy, L1.
  assert (HC1 : ctxo m1 bx bo obase l regs c ovf).
  { eapply ctxo_other with (m := m); try assumption.
    all: try (intros ch b ofs Hw; apply L1; left;
              destruct Hw as [->|[->|[->|[-> _]]]]; first [assumption|apply not_eq_sym; assumption]).
    all: try (intros b ofs k p _ Hp; apply P1, Hp). }
  assert (HLb : length (be_bytes regsS) = 32%nat) by (rewrite be_bytes_length, HlenS; reflexivity).
  destruct ctxo_uchars with (bx := bx) (bo := bo) (obase := obase) (m := m1) (ba := bBuf) (oa := Ptrofs.zero)
    (l := l) (regs := regs) (bs := be_bytes regsS) (c := c) (ovf := ovf)
    as (m2 & HU & HC2 & L2 & P2 & V2); try assumption.
  { rewrite HLb. change (Ptrofs.unsigned Ptrofs.zero) with 0. change (Z.of_nat 32) with 32.
    change Ptrofs.max_unsigned with 18446744073709551615. lia. }
  { intros i Hi. change (Ptrofs.unsigned Ptrofs.zero) with 0. rewrite Z.add_0_l. apply HBy. lia. }
  rewrite HLb in HU, HC2. change (Z.of_nat 32) with 32 in HU, HC2.
  exists m1, m2. split; [|split; [|split; [exact HC2|split; [|split]]]].
  - unfold ent_from_stmt. change le with (set_opttemp None Vundef le) at 2.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_fromMidstate) Ptrofs.zero)
      (vargs := [Vptr bBuf Ptrofs.zero; Vptr bsrc osrc]) (f := Internal f_sha256_fromMidstate).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg2|exact sha_fromMidstate_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [apply ent_ev_buf|reflexivity|].
      eapply eval_Econs; [apply HA|apply HCa|apply eval_Enil].
    + exact sha_fromMidstate_funct.
    + reflexivity.
    + exact HF.
  - unfold ent_uchars_stmt.
    match type of HU with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
      change le with (set_opttemp None vr le) at 2 end.
    eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
      (vargs := [Vptr bx (Ptrofs.repr 0); Vptr bBuf Ptrofs.zero; Vlong (Int64.repr 32)])
      (f := Internal f_sha256_uchars).
    + reflexivity.
    + eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg3|exact sha_uchars_symbol]|].
      apply deref_loc_reference; reflexivity.
    + eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hx|reflexivity|].
      eapply eval_Econs; [apply ent_ev_buf|reflexivity|].
      eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
    + exact sha_uchars_funct.
    + reflexivity.
    + exact HU.
  - intros ch b ofs Hv Nx Nb Ho. rewrite L2 by (try (apply V1; exact Hv); assumption).
    apply L1. left. exact Nb.
  - intros b ofs k p Hv Hp. apply P2; [apply V1, Hv|apply P1, Hp].
  - intros b Hv. apply V2, V1, Hv.
Qed.

(** [sha256_u32le(&ctx, t'2);] *)
Lemma ent_u32le_exec le m (x : int64) l regs c ovf :
  ctxo m bx bo obase l regs c ovf -> le!_t'2 = Some (Vlong x) ->
  exists m',
    Clight2.exec_stmt sha_ge e le m (ent_u32le_stmt idctx) E0 le m' Out_normal /\
    ctxo m' bx bo obase (fst (absorb_i l regs (c_le32_bytes x))) (snd (absorb_i l regs (c_le32_bytes x)))
      (Int64.add c (Int64.repr 4)) (uc_overflow ovf c (Int64.repr 4)) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC Ht.
  destruct ctxo_u32le with (bx := bx) (bo := bo) (obase := obase) (m := m) (l := l) (regs := regs)
    (x := x) (c := c) (ovf := ovf) as (m' & HU & HC' & L' & P' & V'); try assumption.
  exists m'. split; [|split; [exact HC'|split; [exact L'|split; [exact P'|exact V']]]].
  unfold ent_u32le_stmt.
  match type of HU with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
    change le with (set_opttemp None vr le) at 2 end.
  eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_u32le) Ptrofs.zero)
    (vargs := [Vptr bx (Ptrofs.repr 0); Vlong x]) (f := Internal f_sha256_u32le).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact Hg4|exact sha_u32le_symbol_e]|].
    apply deref_loc_reference; reflexivity.
  - eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; exact Hx|reflexivity|].
    eapply eval_Econs; [apply eval_Etempvar; exact Ht|reflexivity|apply eval_Enil].
  - exact sha_u32le_funct_e.
  - reflexivity.
  - exact HU.
Qed.

(** [sha256_finalize(&ctx);] *)
Lemma ent_final_exec le m l regs c ovf :
  ctxo m bx bo obase l regs c ovf ->
  exists m',
    Clight2.exec_stmt sha_ge e le m (ent_final_stmt idctx) E0 le m' Out_normal /\
    (forall i, (i < 8)%nat ->
       Mem.load Mint32 m' bo (obase + 4 * Z.of_nat i) =
         Some (Vint (nth i (snd (absorb_i l regs (sha_pad c))) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bx ->
       (b <> bo \/ ofs + size_chunk ch <= obase \/ obase + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HC.
  destruct ctxo_finalize with (bx := bx) (bo := bo) (obase := obase) (m := m) (l := l) (regs := regs)
    (c := c) (ovf := ovf) as (m' & HF & HR & L' & P' & V'); try assumption.
  exists m'. split; [|split; [exact HR|split; [exact L'|split; [exact P'|exact V']]]].
  unfold ent_final_stmt. eapply mt_call_finalize; [exact Hg5|exact Hx|exact HF].
Qed.
End Phase.

Definition entropy_h1 (txid : list int) (ix : int64) : list int :=
  hash_buffer_regs (be_bytes txid ++ c_le32_bytes ix).

Definition entropy_regs (txid : list int) (ix : int64) (con : list int) : list int :=
  SHA256.hash_block sha256_iv_words (hash_buffer_regs (be_bytes (entropy_h1 txid ix)) ++ con).

Lemma hash_buffer_regs_length bs : length (hash_buffer_regs bs) = 8%nat.
Proof.
  unfold hash_buffer_regs.
  destruct (absorb_i_len bs [] sha256_iv_words ltac:(cbn; lia) eq_refl) as (_ & H1 & H2).
  exact (proj2 (proj2 (absorb_i_len _ _ _ H1 H2))).
Qed.

Lemma ent_optx_value e le bop oop :
  le!_op = Some (Vptr bop (Ptrofs.repr oop)) ->
  forall m, eval_expr sha_ge e le m ent_optx (Vptr bop (Ptrofs.repr oop)).
Proof.
  intros HO m. unfold ent_optx.
  replace (Ptrofs.repr oop) with (Ptrofs.add (Ptrofs.add (Ptrofs.repr oop) (Ptrofs.repr 0)) (Ptrofs.repr 0))
    by (change (Ptrofs.repr 0) with Ptrofs.zero; rewrite !Ptrofs.add_zero; reflexivity).
  eapply eval_envu_field_array;
    [reflexivity|exact envu_sha256_midstate_s|intros ch; discriminate|reflexivity|].
  eapply eval_envu_field_struct;
    [reflexivity|exact envu_outpoint_txid_e|apply eval_envu_deref_struct; exact HO].
Qed.

Ltac ne7 :=
  let E := fresh "E" in
  intro E; subst;
  match goal with H : ~ In _ _ |- _ => apply H; cbn [In]; tauto end.

(** [lia] without the block disequalities of the context (they are
    disequalities of positives, which make it very slow). *)
Ltac zl :=
  repeat match goal with
         | H : ?a <> ?b |- _ => match type of a with block => clear H end
         end; lia.

Theorem eval_generateIssuanceEntropy (Hmodel : memcpy_model) m bres ores bop oop bcon ocon
    (txid con : list int) (ix : int64) :
  0 <= ores -> ores + 32 <= Ptrofs.max_unsigned -> (4 | ores) ->
  Mem.range_perm m bres ores (ores + 32) Cur Writable ->
  0 <= oop -> oop + 40 <= Ptrofs.max_unsigned -> length txid = 8%nat ->
  (forall j, (j < 8)%nat -> Mem.load Mint32 m bop (oop + 4 * Z.of_nat j) = Some (Vint (nth j txid Int.zero))) ->
  Mem.load Mint64 m bop (oop + 32) = Some (Vlong ix) ->
  length con = 8%nat -> Ptrofs.unsigned ocon + 32 <= Ptrofs.max_unsigned ->
  (forall j, (j < 8)%nat ->
     Mem.load Mint32 m bcon (Ptrofs.unsigned ocon + 4 * Z.of_nat j) = Some (Vint (nth j con Int.zero))) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_generateIssuanceEntropy)
      [Vptr bres (Ptrofs.repr ores); Vptr bop (Ptrofs.repr oop); Vptr bcon ocon] E0 m' Vundef /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 4 * Z.of_nat j) = Some (Vint (nth j (entropy_regs txid ix con) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Ho0 HoM HoA PRes Hp0 HpM Htx HTx HIx Hcon HcM HCon Hdisp HMax.
  assert (VG : Mem.valid_block m GC).
  { unfold sha_dispatch_ok in Hdisp. eapply Mem.perm_valid_block.
    apply (proj1 (Mem.load_valid_access _ _ _ _ _ Hdisp) 0). cbn. zl. }
  assert (VM : Mem.valid_block m GM).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HMax) 0). cbn. zl. }
  assert (Vres : Mem.valid_block m bres) by (eapply Mem.perm_valid_block; apply (PRes ores); zl).
  assert (Vop : Mem.valid_block m bop).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HIx) (oop + 32)). cbn. zl. }
  assert (Vcon : Mem.valid_block m bcon).
  { eapply Mem.perm_valid_block.
    apply (proj1 (Mem.load_valid_access _ _ _ _ _ (HCon 0%nat ltac:(zl))) (Ptrofs.unsigned ocon + 4 * Z.of_nat 0)).
    cbn. zl. }
  destruct (Mem.alloc m 0 64) as [ma1 bB] eqn:A1.
  destruct (Mem.alloc ma1 0 32) as [ma2 bBuf] eqn:A2.
  destruct (Mem.alloc ma2 0 32) as [ma3 bR] eqn:A3.
  destruct (Mem.alloc ma3 0 88) as [ma4 bC] eqn:A4.
  destruct (Mem.alloc ma4 0 88) as [ma5 bC1] eqn:A5.
  destruct (Mem.alloc ma5 0 88) as [ma6 bR1] eqn:A6.
  destruct (Mem.alloc ma6 0 88) as [m0 bR2] eqn:A7.
  assert (HAL : alloc_list m [64; 32; 32; 88; 88; 88; 88] = (m0, [bB; bBuf; bR; bC; bC1; bR1; bR2])).
  { cbn [alloc_list]. rewrite A1, A2, A3, A4, A5, A6, A7. reflexivity. }
  destruct (alloc_list_props _ _ _ _ HAL) as ((XV & XL & XP & XA) & FRh & ND & FA).
  inversion FA as [|? ? ? ? [PB0 VB0] FA1]; subst.
  inversion FA1 as [|? ? ? ? [PBuf0 VBuf0] FA2]; subst.
  inversion FA2 as [|? ? ? ? [PR0 VR0] FA3]; subst.
  inversion FA3 as [|? ? ? ? [PC0 VC0] FA4]; subst.
  inversion FA4 as [|? ? ? ? [PC10 VC10] FA5]; subst.
  inversion FA5 as [|? ? ? ? [PR10 VR10] FA6]; subst.
  inversion FA6 as [|? ? ? ? [PR20 VR20] FA7]; subst. clear FA FA1 FA2 FA3 FA4 FA5 FA6 FA7 HAL.
  repeat match goal with H : NoDup (_ :: _) |- _ => apply NoDup_cons_iff in H; destruct H as [? H] end.
  assert (NF : forall b, Mem.valid_block m b ->
    b <> bB /\ b <> bBuf /\ b <> bR /\ b <> bC /\ b <> bC1 /\ b <> bR1 /\ b <> bR2).
  { intros b Hb. pose proof (FRh b Hb) as HN. cbn [In] in HN.
    repeat split; intro E; apply HN; rewrite E; tauto. }
  destruct (NF GC VG) as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  destruct (NF GM VM) as (M1 & M2 & M3 & M4 & M5 & M6 & M7).
  destruct (NF bop Vop) as (O1 & O2 & O3 & O4 & O5 & O6 & O7).
  destruct (NF bcon Vcon) as (N1 & N2 & N3 & N4 & N5 & N6 & N7).
  destruct (NF bres Vres) as (S1 & S2 & S3 & S4 & S5 & S6 & S7).
  assert (D_R_C : bR <> bC) by ne7. assert (D_R2_C : bR2 <> bC) by ne7.
  assert (D_R2_R : bR2 <> bR) by ne7. assert (D_Buf_C : bBuf <> bC) by ne7.
  assert (D_Buf_R : bBuf <> bR) by ne7.
  assert (D_B_C1 : bB <> bC1) by ne7. assert (D_R1_C1 : bR1 <> bC1) by ne7.
  assert (D_R1_B : bR1 <> bB) by ne7. assert (D_Buf_C1 : bBuf <> bC1) by ne7.
  assert (D_Buf_B : bBuf <> bB) by ne7. assert (D_B_R : bB <> bR) by ne7.
  assert (D_R_R1 : bR <> bR1) by ne7. assert (D_R_C1 : bR <> bC1) by ne7.
  assert (D_R_B : bR <> bB) by ne7. assert (D_B_C : bB <> bC) by ne7.
  assert (D_B_Buf : bB <> bBuf) by ne7. assert (D_B_R2 : bB <> bR2) by ne7.
  assert (D_C1_C : bC1 <> bC) by ne7. assert (D_C1_R2 : bC1 <> bR2) by ne7.
  assert (D_R1_C : bR1 <> bC) by ne7. assert (D_R1_R2 : bR1 <> bR2) by ne7.
  assert (D_R1_Buf : bR1 <> bBuf) by ne7. assert (D_C1_Buf : bC1 <> bBuf) by ne7.
  assert (D_R_Buf : bR <> bBuf) by ne7.
  set (e := ent_env bB bBuf bR bC bC1 bR1 bR2).
  set (le := PTree.set _contract (Vptr bcon ocon) (PTree.set _op (Vptr bop (Ptrofs.repr oop))
    (PTree.set __res (Vptr bres (Ptrofs.repr ores))
       (create_undef_temps (fn_temps f_simplicity_generateIssuanceEntropy))))).
  set (le2 := PTree.set _t'2 (Vlong ix) le).
  assert (Hob0 : 0 <= 0 /\ 0 + 32 <= Ptrofs.max_unsigned)
    by (change Ptrofs.max_unsigned with 18446744073709551615; zl).
  assert (HoA0 : (4 | 0)) by (exists 0; reflexivity).
  assert (Hdisp0 : sha_dispatch_ok m0) by (unfold sha_dispatch_ok; rewrite XL by exact VG; exact Hdisp).
  assert (HMax0 : Mem.load Mint64 m0 GM 0 = Some (Vlong sha_max_counter)) by (rewrite XL by exact VM; exact HMax).
  assert (HRS : forall le' m', eval_expr sha_ge e le' m' (Efield (Evar _result MID) _s (tarray tuint 8))
    (Vptr bR (Ptrofs.repr 0))) by (intros; apply calc_eval_local_mid_s; reflexivity).
  (* ---- phase 1: result = sha256(txid ++ le32(ix)) ---- *)
  destruct ent_init_exec with (e := e) (idctx := _ctx) (idres := __res__2) (bx := bC) (br := bR2) (bo := bR)
    (obase := 0) (le := le) (m := m0) (aout := Efield (Evar _result MID) _s (tarray tuint 8))
    as (mx1 & X1 & C1 & L1 & P1 & V1); try assumption; try reflexivity; try (apply XV; assumption).
  { intros m'. apply HRS. }
  { intros o Ho. eapply Mem.perm_implies; [apply PR0; zl|constructor]. }
  assert (K1 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch mx1 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (NF b Hb) as (? & ? & ? & ? & ? & ? & ?).
    rewrite L1 by (try (apply XV; exact Hb); try assumption; left; assumption). apply XL, Hb. }
  destruct ent_from_uchars_exec with (e := e) (idctx := _ctx) (br := bR2) (bx := bC) (bBuf := bBuf) (bo := bR) (obase := 0)
    (le := le) (m := mx1) (asrc := ent_optx) (bsrc := bop) (osrc := Ptrofs.repr oop) (regsS := txid)
    (l := @nil int) (regs := sha256_iv_words) (c := Int64.zero) (ovf := false)
    as (ma & m2 & XF1 & XU1 & C2 & L2 & P2 & V2); try assumption; try reflexivity.
  { apply ent_optx_value. reflexivity. }
  { apply not_eq_sym. exact O2. }
  { rewrite Ptrofs.unsigned_repr by zl. zl. }
  { intros j Hj. rewrite Ptrofs.unsigned_repr by zl. rewrite K1 by exact Vop. exact (HTx j Hj). }
  { intros o Ho. apply P1. eapply Mem.perm_implies; [apply PBuf0, Ho|constructor]. }
  assert (K2 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m2 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (NF b Hb) as (? & ? & ? & ? & ? & ? & ?).
    rewrite L2 by (try (apply V1, XV; exact Hb); try assumption; left; assumption). apply K1, Hb. }
  assert (XS : Clight2.exec_stmt sha_ge e le m2
    (Sset _t'2 (Efield (Ederef (Etempvar _op (tptr OPT)) OPT) _ix tulong)) E0 le2 m2 Out_normal).
  { apply exec_Sset. eapply eval_envu_field_value;
      [reflexivity|exact envu_outpoint_ix_e|reflexivity|apply eval_envu_deref_struct; reflexivity|].
    rewrite envu_ptr_add_repr by zl. apply envu_loadv_repr; [zl|]. rewrite K2 by exact Vop. exact HIx. }
  destruct ent_u32le_exec with (e := e) (idctx := _ctx) (bx := bC) (bo := bR) (obase := 0) (le := le2) (m := m2)
    (x := ix) (l := fst (absorb_i [] sha256_iv_words (be_bytes txid)))
    (regs := snd (absorb_i [] sha256_iv_words (be_bytes txid)))
    (c := Int64.add Int64.zero (Int64.repr 32)) (ovf := uc_overflow false Int64.zero (Int64.repr 32))
    as (m3 & XL1 & C3 & L3 & P3 & V3); try assumption; try reflexivity.
  destruct ent_final_exec with (e := e) (idctx := _ctx) (bx := bC) (bo := bR) (obase := 0) (le := le2) (m := m3)
    (l := fst (absorb_i (fst (absorb_i [] sha256_iv_words (be_bytes txid)))
                 (snd (absorb_i [] sha256_iv_words (be_bytes txid))) (c_le32_bytes ix)))
    (regs := snd (absorb_i (fst (absorb_i [] sha256_iv_words (be_bytes txid)))
                 (snd (absorb_i [] sha256_iv_words (be_bytes txid))) (c_le32_bytes ix)))
    (c := Int64.add (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 4))
    (ovf := uc_overflow (uc_overflow false Int64.zero (Int64.repr 32))
              (Int64.add Int64.zero (Int64.repr 32)) (Int64.repr 4))
    as (m4 & XFi1 & HR4 & L4 & P4 & V4); try assumption; try reflexivity.
  assert (HH1 : forall i, (i < 8)%nat ->
    Mem.load Mint32 m4 bR (0 + 4 * Z.of_nat i) = Some (Vint (nth i (entropy_h1 txid ix) Int.zero))).
  { intros i Hi. rewrite (HR4 i Hi). do 2 f_equal.
    unfold entropy_h1, hash_buffer_regs. rewrite absorb_i_app.
    rewrite app_length, be_bytes_length, Htx. reflexivity. }
  assert (V4' : forall b, Mem.valid_block m0 b -> Mem.valid_block m4 b).
  { intros b Hb. apply V4, V3, V2, V1, Hb. }
  assert (P4' : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m4 b ofs k p).
  { intros b ofs k p Hp. assert (Hb : Mem.valid_block m0 b) by (eapply Mem.perm_valid_block; exact Hp).
    apply P4; [apply V3, V2, V1, Hb|]. apply P3; [apply V2, V1, Hb|]. apply P2; [apply V1, Hb|]. apply P1, Hp. }
  assert (K4 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m4 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (NF b Hb) as (? & ? & ? & ? & ? & ? & ?).
    rewrite L4 by (try (apply V3, V2, V1, XV; exact Hb); try assumption; left; assumption).
    rewrite L3 by (try (apply V2, V1, XV; exact Hb); try assumption; left; assumption). apply K2, Hb. }
  (* ---- phase 2: block[0..8] = sha256(result bytes) ---- *)
  assert (HB0e : forall le' m', eval_expr sha_ge e le' m' ent_block0 (Vptr bB (Ptrofs.repr 0))).
  { intros le' m'. unfold ent_block0.
    eapply eval_Ebinop with (v1 := Vptr bB Ptrofs.zero);
      [eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity]
      |apply eval_Econst_int|reflexivity]. }
  destruct ent_init_exec with (e := e) (idctx := _ctx__1) (idres := __res__1) (bx := bC1) (br := bR1) (bo := bB)
    (obase := 0) (le := le2) (m := m4) (aout := ent_block0)
    as (mx2 & X2 & C5 & L5 & P5 & V5); try assumption; try reflexivity; try (apply V4', XV; assumption).
  { intros m'. apply HB0e. }
  { intros o Ho. apply P4', PR10, Ho. }
  { intros o Ho. apply P4', PC10, Ho. }
  { intros o Ho. apply P4'. eapply Mem.perm_implies; [apply PB0; zl|constructor]. }
  { unfold sha_dispatch_ok. rewrite K4 by exact VG. exact Hdisp. }
  { rewrite K4 by exact VM. exact HMax. }
  pose proof (hash_buffer_regs_length (be_bytes txid ++ c_le32_bytes ix)) as HlenH1.
  fold (entropy_h1 txid ix) in HlenH1.
  destruct ent_from_uchars_exec with (e := e) (idctx := _ctx__1) (br := bR1) (bx := bC1) (bBuf := bBuf) (bo := bB) (obase := 0)
    (le := le2) (m := mx2) (asrc := Efield (Evar _result MID) _s (tarray tuint 8)) (bsrc := bR)
    (osrc := Ptrofs.repr 0) (regsS := entropy_h1 txid ix)
    (l := @nil int) (regs := sha256_iv_words) (c := Int64.zero) (ovf := false)
    as (mb & m5 & XF2 & XU2 & C6 & L6 & P6 & V6); try assumption; try reflexivity.
  { intros m'. apply HRS. }
  { change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0. change Ptrofs.max_unsigned with 18446744073709551615. zl. }
  { intros j Hj. change (Ptrofs.unsigned (Ptrofs.repr 0)) with 0.
    rewrite L5 by (try (apply V4'; exact VR0); try assumption; left; assumption). exact (HH1 j Hj). }
  { intros o Ho. apply P5, P4'. eapply Mem.perm_implies; [apply PBuf0, Ho|constructor]. }
  destruct ent_final_exec with (e := e) (idctx := _ctx__1) (bx := bC1) (bo := bB) (obase := 0) (le := le2) (m := m5)
    (l := fst (absorb_i [] sha256_iv_words (be_bytes (entropy_h1 txid ix))))
    (regs := snd (absorb_i [] sha256_iv_words (be_bytes (entropy_h1 txid ix))))
    (c := Int64.add Int64.zero (Int64.repr 32)) (ovf := uc_overflow false Int64.zero (Int64.repr 32))
    as (m6 & XFi2 & HR6 & L6' & P6' & V6'); try assumption; try reflexivity.
  set (W2 := hash_buffer_regs (be_bytes (entropy_h1 txid ix))).
  assert (HH2 : forall i, (i < 8)%nat ->
    Mem.load Mint32 m6 bB (4 * Z.of_nat i) = Some (Vint (nth i W2 Int.zero))).
  { intros i Hi. replace (4 * Z.of_nat i) with (0 + 4 * Z.of_nat i) by zl. rewrite (HR6 i Hi). do 2 f_equal.
    unfold W2, hash_buffer_regs. rewrite be_bytes_length, HlenH1. reflexivity. }
  assert (V6'' : forall b, Mem.valid_block m0 b -> Mem.valid_block m6 b).
  { intros b Hb. apply V6', V6, V5, V4', Hb. }
  assert (P6'' : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m6 b ofs k p).
  { intros b ofs k p Hp. assert (Hb : Mem.valid_block m0 b) by (eapply Mem.perm_valid_block; exact Hp).
    apply P6'; [apply V6, V5, V4', Hb|]. apply P6; [apply V5, V4', Hb|]. apply P5, P4', Hp. }
  assert (K6 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m6 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb. destruct (NF b Hb) as (? & ? & ? & ? & ? & ? & ?).
    rewrite L6' by (try (apply V6, V5, V4', XV; exact Hb); try assumption; left; assumption).
    rewrite L6 by (try (apply V5, V4', XV; exact Hb); try assumption; left; assumption).
    rewrite L5 by (try (apply V4', XV; exact Hb); try assumption; left; assumption). apply K4, Hb. }
  (* ---- memcpy(&block[8], contract->s, 32) ---- *)
  assert (HRc : Mem.range_perm m6 bcon (Ptrofs.unsigned ocon) (Ptrofs.unsigned ocon + 32) Cur Readable).
  { intros o Ho.
    set (j := Z.to_nat ((o - Ptrofs.unsigned ocon) / 4)).
    assert (Hj : (j < 8)%nat).
    { unfold j. apply Nat2Z.inj_lt. rewrite Z2Nat.id by (apply Z.div_pos; zl).
      apply Z.div_lt_upper_bound; zl. }
    pose proof (HCon j Hj) as HLj. rewrite <- (K6 Mint32 bcon _ Vcon) in HLj.
    apply (proj1 (Mem.load_valid_access _ _ _ _ _ HLj)).
    unfold j. rewrite Z2Nat.id by (apply Z.div_pos; zl). change (size_chunk Mint32) with 4.
    pose proof (Z.div_mod (o - Ptrofs.unsigned ocon) 4 ltac:(zl)) as HD.
    pose proof (Z.mod_pos_bound (o - Ptrofs.unsigned ocon) 4 ltac:(zl)) as HB. zl. }
  destruct (Mem.range_perm_loadbytes m6 bcon (Ptrofs.unsigned ocon) 32 HRc) as [bytes HBy].
  pose proof (Ptrofs.unsigned_range ocon) as HocR.
  destruct (Hmodel (Clight.genv_genv sha_ge) m6 bB (Ptrofs.repr 32) bcon ocon 32 bytes) as (m7 & HSB & HXm).
  { apply V6'', XV, Vcon. }
  { apply V6'', VB0. }
  { exact HBy. }
  { change (Ptrofs.unsigned (Ptrofs.repr 32)) with 32. intros o Ho. apply P6''.
    eapply Mem.perm_implies; [apply PB0; zl|constructor]. }
  { left. exact N1. }
  { change Int64.max_unsigned with 18446744073709551615. zl. }
  { zl. }
  { change (Ptrofs.unsigned (Ptrofs.repr 32)) with 32. change Ptrofs.max_unsigned with 18446744073709551615. zl. }
  change (Ptrofs.unsigned (Ptrofs.repr 32)) with 32 in HSB.
  pose proof (Mem.loadbytes_length _ _ _ _ _ HBy) as HBL. change (Z.to_nat 32) with 32%nat in HBL.
  assert (HB7 : Mem.loadbytes m7 bB 32 32 = Some bytes).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ HSB) as HSame. rewrite HBL in HSame. exact HSame. }
  assert (L7 : forall ch b ofs, b <> bB -> Mem.load ch m7 b ofs = Mem.load ch m6 b ofs).
  { intros ch b ofs Hb. apply (Mem.load_storebytes_other _ _ _ _ _ HSB). left. exact Hb. }
  assert (P7 : forall b ofs k p, Mem.perm m6 b ofs k p -> Mem.perm m7 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_storebytes_1; [exact HSB|exact Hp]. }
  assert (V7 : forall b, Mem.valid_block m6 b -> Mem.valid_block m7 b).
  { intros b Hb. eapply Mem.storebytes_valid_block_1; [exact HSB|exact Hb]. }
  assert (HlenH2 : length W2 = 8%nat) by apply hash_buffer_regs_length.
  assert (HBlk : forall j, (j < 16)%nat ->
    Mem.load Mint32 m7 bB (4 * Z.of_nat j) = Some (Vint (nth j (W2 ++ con) Int.zero))).
  { intros j Hj. destruct (lt_dec j 8) as [Hlt|Hge].
    - rewrite app_nth1 by zl.
      rewrite (Mem.load_storebytes_other _ _ _ _ _ HSB)
        by (right; left; change (size_chunk Mint32) with 4; zl). exact (HH2 j Hlt).
    - rewrite app_nth2 by zl. rewrite HlenH2.
      replace (4 * Z.of_nat j) with (32 + 4 * Z.of_nat (j - 8)) by zl.
      apply (equal_loadbytes_field Mint32 m6 m7 bcon bB (Ptrofs.unsigned ocon) 32 32 (4 * Z.of_nat (j - 8)) bytes);
        [zl|change (size_chunk Mint32) with 4; zl|exact HBy|exact HB7
        |change (align_chunk Mint32) with 4; exists (8 + Z.of_nat (j - 8)); zl|].
      rewrite K6 by exact Vcon. apply HCon. zl. }
  (* ---- sha256_iv, compression, return ---- *)
  assert (HresL : forall v, (PTree.set _t'1 v le2)!__res = Some (Vptr bres (Ptrofs.repr ores)))
    by (intros v; reflexivity).
  assert (PRes7 : Mem.range_perm m7 bres ores (ores + 32) Cur Writable).
  { intros o Ho. apply P7, P6'', XP, PRes, Ho. }
  assert (PR7 : Mem.range_perm m7 bR 0 32 Cur Writable).
  { intros o Ho. apply P7, P6''. eapply Mem.perm_implies; [apply PR0, Ho|constructor]. }
  assert (NRres : bR <> bres) by (apply not_eq_sym; exact S3).
  assert (NBres : bB <> bres) by (apply not_eq_sym; exact S1).
  assert (Hblk : length (W2 ++ con) = 16%nat) by (rewrite app_length, HlenH2, Hcon; reflexivity).
  assert (Hdisp7 : sha_dispatch_ok m7).
  { unfold sha_dispatch_ok. rewrite L7 by exact G1. rewrite K6 by exact VG. exact Hdisp. }
  destruct calc_tail_exec with (e := e) (bB := bB) (bR := bR) (td := _t'1) (le := le2) (m := m7)
    (bres := bres) (ores := ores) (blk := W2 ++ con)
    as (le' & m8 & XT & HRes & L8 & P8 & V8); try assumption; try reflexivity.
  assert (P8' : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m8 b ofs k p).
  { intros b ofs k p Hp. apply P8, P7, P6'', Hp. }
  destruct (free_list_blocks
    [(bC1, 0, 88); (bC, 0, 88); (bR2, 0, 88); (bR1, 0, 88); (bBuf, 0, 32); (bB, 0, 64); (bR, 0, 32)] m8)
    as (mf & HFL & HLf & HPf & HVf).
  { intros b0 lo hi HIn o Ho. cbn [In] in HIn. apply P8'.
    destruct HIn as [E|[E|[E|[E|[E|[E|[E|[]]]]]]]]; injection E as <- <- <-;
      [apply PC10|apply PC0|apply PR20|apply PR10|apply PBuf0|apply PB0|apply PR0]; exact Ho. }
  { cbn [map fst]. repeat (apply NoDup_cons; [cbn [In]; intros HIn;
      repeat (destruct HIn as [HIn|HIn]; [revert HIn; ne7|]); exact HIn|]). apply NoDup_nil. }
  cbn [map fst] in HLf, HPf.
  assert (NIn : forall b, Mem.valid_block m b -> ~ In b [bC1; bC; bR2; bR1; bBuf; bB; bR]).
  { intros b Hb HIn. destruct (NF b Hb) as (? & ? & ? & ? & ? & ? & ?). cbn [In] in HIn.
    repeat (destruct HIn as [HIn|HIn]; [symmetry in HIn; contradiction|]). exact HIn. }
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le') (m2 := m8)
      (out := Out_return None).
    + eapply ent_entry; eassumption.
    + rewrite entropy_body_shape.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m4).
      { unfold ent_phase1.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X1|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XF1|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XU1|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [|exact XFi1].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XS|exact XL1]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m6).
      { unfold ent_phase2.
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact X2|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XF2|].
        eapply exec_Sseq_1 with (t1 := E0) (t2 := E0); [exact XU2|exact XFi2]. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m7); [|exact XT].
      unfold ent_memcpy. change le2 with (set_opttemp None (Vptr bB (Ptrofs.repr 32)) le2) at 2.
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _memcpy) Ptrofs.zero)
        (vargs := [Vptr bB (Ptrofs.repr 32); Vptr bcon ocon; Vlong (Int64.repr 32)]).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_memcpy_symbol]|].
        apply deref_loc_reference; reflexivity.
      * eapply eval_Econs.
        -- eapply eval_Ebinop with (v1 := Vptr bB Ptrofs.zero);
             [eapply eval_Elvalue; [apply eval_Evar_local; reflexivity|apply deref_loc_reference; reflexivity]
             |apply eval_Econst_int|reflexivity].
        -- reflexivity.
        -- eapply eval_Econs.
           ++ eapply eval_envu_field_array with (b := bcon) (ofs := ocon);
                [reflexivity|exact envu_sha256_midstate_s|intros ch; discriminate|reflexivity
                |apply eval_envu_deref_struct; reflexivity].
           ++ rewrite Ptrofs.add_zero. reflexivity.
           ++ eapply eval_Econs; [apply eval_Esizeof|reflexivity|apply eval_Enil].
      * exact sha_memcpy_funct.
      * reflexivity.
      * apply eval_funcall_external. exact HXm.
    + reflexivity.
    + unfold e. rewrite ent_blocks. exact HFL.
  - intros j Hj. rewrite HLf by (apply NIn, Vres). exact (HRes j Hj).
  - intros ch b ofs Hb Hr. destruct (NF b Hb) as (? & ? & ? & ? & ? & ? & ?).
    rewrite HLf by (apply NIn, Hb).
    rewrite L8 by (try (apply V7, V6'', XV; exact Hb); try assumption).
    rewrite L7 by assumption. apply K6, Hb.
  - intros b ofs k p Hb Hp. apply HPf; [apply NIn, Hb|]. apply P8', XP, Hp.
  - intros b Hb. apply HVf, V8, V7, V6'', XV, Hb.
Qed.
