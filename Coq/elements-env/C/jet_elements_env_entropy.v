(** Execution of [simplicity_generateIssuanceEntropy(op, contract)]
    (elements/ops.c): the midstate
      compress(iv, sha256(sha256(txid bytes ++ le32(ix))) words ++ contract)
    built with two local SHA-256 contexts, [memcpy] of the contract hash and
    one compression from the initial state. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_struct_copy_loads.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_block_exec C.jet_sha_compress_call.
Require Import C.jet_sha_ctx8_model C.jet_sha_be32_write C.jet_sha_be64_exec C.jet_sha_hash_exec.
Require Import C.jet_sha_uchars_prep C.jet_sha_add_n_init C.jet_sha_finalize_exec C.jet_sha_tapdata_prep.
Require Import C.jet_sha_ctx_abs C.jet_sha_uchars_exec C.jet_sha_uchars_exec C.jet_sha_ctxi.
Require Import C.jet_env_store_words C.jet_elements_env_field_eval C.jet_elements_make_tapleaf_exec.
Require Import C.jet_elements_env_ctxo C.jet_elements_env_ctxo_more C.jet_elements_env_ctxo_le.
Require Import C.jet_elements_env_ctxo_uchars C.jet_elements_env_le32_write C.jet_elements_env_u32le_exec.
Require Import C.jet_elements_env_tx_calls C.jet_elements_env_hashbuffer C.jet_elements_env_calc.
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
