(** [simplicity_bitcoin_mallocTransaction]: one
      sha256_context ctx_X = sha256_init(tx->X.s);
    as a step that adds a fresh context to the live ones, for any of the
    twelve contexts of the function. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init C.jet_bitmachine_rep.
Require C.jets.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_add_n_init C.jet_sha_ctx8_model.
Require Import C.jet_sha_uchars_prep C.jet_sha_uchars_exec C.jet_sha_tapdata_prep C.jet_sha_ctx_abs.
Require Import C.jet_bitcoin_env_field_eval C.jet_bitcoin_env_ctxo C.jet_bitcoin_env_ctxs.
Require Import C.jet_bitcoin_env_tapenv_prelude C.jet_bitcoin_env_tapenv_fill C.jet_bitcoin_env_tapenv_path.
Require Import C.jet_bitcoin_env_tx_prelude.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Notation TXD := (Ederef (Etempvar _tx (tptr TX)) TX).

Local Opaque sha_ge.

(** [tx->f.s] and [&tx->f] for a midstate member at offset [delta]. *)
Lemma ev_tx_mid_s e le m bA f delta :
  le!_tx = Some (Vptr bA Ptrofs.zero) -> envu_field_at _bitcoinTransaction f delta ->
  eval_expr sha_ge e le m (Efield (Efield TXD f MID) _s A8) (Vptr bA (Ptrofs.repr delta)).
Proof.
  intros Hle Hf.
  pose proof (eval_envu_field_array e le m (Efield TXD f MID) _sha256_midstate _s 0 A8 bA
    (Ptrofs.repr delta) eq_refl envu_sha256_midstate_s ltac:(intros chunk; discriminate) eq_refl) as HE.
  rewrite Ptrofs.add_zero in HE. apply HE.
  pose proof (eval_envu_field_struct e le m TXD _bitcoinTransaction f delta _sha256_midstate bA Ptrofs.zero
    eq_refl Hf (eval_envu_deref_struct e le m _tx _bitcoinTransaction bA Ptrofs.zero Hle)) as HE2.
  rewrite Ptrofs.add_zero_l in HE2. exact HE2.
Qed.

Lemma ev_tx_mid_addr e le m bA f delta :
  le!_tx = Some (Vptr bA Ptrofs.zero) -> envu_field_at _bitcoinTransaction f delta ->
  eval_expr sha_ge e le m (Eaddrof (Efield TXD f MID) (tptr MID)) (Vptr bA (Ptrofs.repr delta)).
Proof.
  intros Hle Hf. rewrite <- (Ptrofs.add_zero_l (Ptrofs.repr delta)).
  eapply eval_Eaddrof. eapply eval_envu_field_lvalue; [reflexivity|exact Hf|apply eval_envu_deref_struct; exact Hle].
Qed.

(** A frame that excludes two blocks keeps the live contexts. *)
Theorem ctxs_frame2 m m' bo (cs : list ctx_entry) (bx0 bx1 : block) (ob0 : Z) :
  ctxs m bo cs ->
  GC <> bx0 -> GM <> bx0 -> bo <> bx0 -> GC <> bx1 -> GM <> bx1 -> bo <> bx1 -> GC <> bo -> GM <> bo ->
  (forall c, In c cs -> ctx_block c <> bx0 /\ ctx_block c <> bx1 /\ ctx_block c <> bo /\
     (ctx_out c + 32 <= ob0 \/ ob0 + 32 <= ctx_out c)) ->
  (forall ch b ofs, Mem.valid_block m b -> b <> bx0 -> b <> bx1 ->
     (b <> bo \/ ofs + size_chunk ch <= ob0 \/ ob0 + 32 <= ofs) ->
     Mem.load ch m' b ofs = Mem.load ch m b ofs) ->
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) ->
  ctxs m' bo cs.
Proof.
  intros HC NG0 NM0 NB0 NG1 NM1 NB1 NGo NMo HD HL HP.
  assert (HV : forall c, In c cs -> Mem.valid_block m (ctx_block c) /\ Mem.valid_block m bo /\
    Mem.valid_block m GC /\ Mem.valid_block m GM).
  { intros c Hc. unfold ctxs in HC. rewrite Forall_forall in HC. specialize (HC c Hc).
    destruct c as [[[[[bx ob] l] regs] cnt] ovf]. cbn [ctx_holds ctx_block] in *.
    destruct HC as (HOut & _ & _ & _ & HRegs & _ & _ & _ & _ & Hdisp & HMax).
    split; [eapply load_valid_block; exact HOut|].
    split; [eapply load_valid_block; exact (proj1 (HRegs 0%nat ltac:(lia)))|].
    split; eapply load_valid_block; eassumption. }
  eapply ctxs_other; [exact HC| |].
  - intros c ch b ofs Hc Hb. destruct (HV c Hc) as (V1 & V2 & V3 & V4). destruct (HD c Hc) as (D0 & D1 & Do & D2).
    destruct Hb as [->|[->|[->|[-> Hr]]]].
    + apply HL; [exact V1|exact D0|exact D1|left; exact Do].
    + apply HL; [exact V3|exact NG0|exact NG1|left; exact NGo].
    + apply HL; [exact V4|exact NM0|exact NM1|left; exact NMo].
    + apply HL; [exact V2|exact NB0|exact NB1|right; lia].
  - intros c b ofs k p Hc _ Hp. apply HP, Hp.
Qed.

Section InitStep.
Variables (e : env) (bA : block).
Hypothesis HeI : e!_sha256_init = None.
Hypothesis NGA : GC <> bA.
Hypothesis NMA : GM <> bA.

(** One initialisation: the new context is added to the live ones. *)
Theorem mt_init_step le m (idres idctx f : ident) (bR bC : block) (delta : Z) (cs : list ctx_entry) :
  e!idres = Some (bR, CTX) -> e!idctx = Some (bC, CTX) ->
  le!_tx = Some (Vptr bA Ptrofs.zero) ->
  envu_field_at _bitcoinTransaction f delta -> 0 <= delta /\ delta + 32 <= 488 -> (4 | delta) ->
  bA <> bC -> bA <> bR -> bR <> bC -> GC <> bC -> GM <> bC -> GC <> bR -> GM <> bR ->
  Mem.range_perm m bR 0 88 Cur Freeable -> Mem.range_perm m bC 0 88 Cur Freeable ->
  Mem.range_perm m bA delta (delta + 32) Cur Writable ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  ctxs m bA cs ->
  (forall c, In c cs -> ctx_block c <> bR /\ ctx_block c <> bC /\ ctx_block c <> bA /\
     (ctx_out c + 32 <= delta \/ delta + 32 <= ctx_out c)) ->
  exists m',
    Clight2.exec_stmt sha_ge e le m
      (Ssequence
        (Scall None (Evar _sha256_init
           (Tfunction (Tcons CTXP (Tcons (tptr tuint) Tnil)) tvoid
              {| cc_vararg := None; cc_unproto := false; cc_structret := true |}))
           [Eaddrof (Evar idres CTX) CTXP; Efield (Efield TXD f MID) _s A8])
        (Sassign (Evar idctx CTX) (Evar idres CTX))) E0 le m' Out_normal /\
    ctxs m' bA ((bC, delta, [], sha256_iv_words, Int64.zero, false) :: cs) /\
    (forall ch b ofs, Mem.valid_block m b -> b <> bR -> b <> bC ->
       (b <> bA \/ ofs + size_chunk ch <= delta \/ delta + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros HeR HeC Hle Hf Hd HdA NAC NAR NRC NGC NMC NGR NMR PR PC PA Hdisp HMax HCs HDis.
  assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
  assert (Hob : 0 <= delta /\ delta + 32 <= Ptrofs.max_unsigned)
    by (change Ptrofs.max_unsigned with 18446744073709551615; lia).
  destruct (ctxo_init bC bA delta NAC NGC NGA NMC NMA Hob m bR (not_eq_sym NAR) NRC HdA VG VM NGR NMR PR PC PA Hdisp HMax)
    as (mi & mx & bytes & HInit & HLB & HSB & HC0 & HLx & HPx & HVx).
  exists mx. split; [|split; [|split; [|split]]].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mi).
    + pose proof (ev_tx_mid_s e le m bA f delta Hle Hf) as HEv.
      exact (te_call_init e le m mi idres (Efield (Efield TXD f MID) _s A8) bR bA (Ptrofs.repr delta)
               HeI HeR HEv eq_refl HInit).
    + exact (exec_ctx_struct_copy e le mi mx idctx idres bC bR bytes HeC HeR (not_eq_sym NRC) HLB HSB).
  - constructor; [exact HC0|].
    refine (ctxs_frame2 m mx bA cs bR bC delta HCs NGR NMR NAR NGC NMC NAC NGA NMA _ _ HPx).
    + intros c Hc. destruct (HDis c Hc) as (D1 & D2 & D3 & D4). repeat split; assumption.
    + intros ch b ofs Hb H1 H2 Hr. apply HLx; assumption.
  - intros ch b ofs Hb H1 H2 Hr. apply HLx; assumption.
  - exact HPx.
  - exact HVx.
Qed.
End InitStep.

(** ** A run of initialisations *)

(** Result temporary, context variable, member, its offset, and the blocks of
    the two local variables. *)
Definition init_item : Type := (ident * ident * ident * Z * block * block)%type.

Definition item_stmt (it : init_item) : statement :=
  let '(r, c, f, d, bR, bC) := it in
  Ssequence
    (Scall None (Evar _sha256_init
       (Tfunction (Tcons CTXP (Tcons (tptr tuint) Tnil)) tvoid
          {| cc_vararg := None; cc_unproto := false; cc_structret := true |}))
       [Eaddrof (Evar r CTX) CTXP; Efield (Efield TXD f MID) _s A8])
    (Sassign (Evar c CTX) (Evar r CTX)).

Fixpoint inits_stmt (its : list init_item) (rest : statement) : statement :=
  match its with
  | [] => rest
  | it :: l => Ssequence (item_stmt it) (inits_stmt l rest)
  end.

Definition item_entry (it : init_item) : ctx_entry :=
  let '(r, c, f, d, bR, bC) := it in (bC, d, [], sha256_iv_words, Int64.zero, false).

Section Inits.
Variables (e : env) (bA : block).
Hypothesis HeI : e!_sha256_init = None.
Hypothesis NGA : GC <> bA.
Hypothesis NMA : GM <> bA.

Definition item_ok (it : init_item) : Prop :=
  let '(r, c, f, d, bR, bC) := it in
  e!r = Some (bR, CTX) /\ e!c = Some (bC, CTX) /\
  envu_field_at _bitcoinTransaction f d /\ (0 <= d /\ d + 32 <= 488) /\ (4 | d) /\
  bA <> bC /\ bA <> bR /\ bR <> bC /\ GC <> bC /\ GM <> bC /\ GC <> bR /\ GM <> bR.

Definition item_sep (it : init_item) (c : ctx_entry) : Prop :=
  let '(r, cx, f, d, bR, bC) := it in
  ctx_block c <> bR /\ ctx_block c <> bC /\ ctx_block c <> bA /\
  (ctx_out c + 32 <= d \/ d + 32 <= ctx_out c).

Fixpoint items_wf (its : list init_item) (cs : list ctx_entry) : Prop :=
  match its with
  | [] => True
  | it :: l => item_ok it /\ (forall c, In c cs -> item_sep it c) /\ items_wf l (item_entry it :: cs)
  end.

Definition item_perms (m : mem) (it : init_item) : Prop :=
  let '(r, c, f, d, bR, bC) := it in
  Mem.range_perm m bR 0 88 Cur Freeable /\ Mem.range_perm m bC 0 88 Cur Freeable /\
  Mem.range_perm m bA d (d + 32) Cur Writable.

Definition item_untouched (it : init_item) (ch : memory_chunk) (b : block) (ofs : Z) : Prop :=
  let '(r, c, f, d, bR, bC) := it in
  b <> bR /\ b <> bC /\ (b <> bA \/ ofs + size_chunk ch <= d \/ d + 32 <= ofs).

Lemma item_perms_mono m m' it :
  (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) -> item_perms m it -> item_perms m' it.
Proof.
  destruct it as [[[[[r c] f] d] bR] bC]. intros HP (P1 & P2 & P3).
  repeat split; intros o Ho; apply HP; [apply P1|apply P2|apply P3]; exact Ho.
Qed.

Theorem inits_exec (its : list init_item) : forall (cs : list ctx_entry) le m,
  items_wf its cs -> le!_tx = Some (Vptr bA Ptrofs.zero) ->
  (forall it, In it its -> item_perms m it) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  ctxs m bA cs ->
  exists m',
    ctxs m' bA (rev (map item_entry its) ++ cs) /\
    (forall ch b ofs, Mem.valid_block m b -> (forall it, In it its -> item_untouched it ch b ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b) /\
    (forall rest t le' mf out,
       Clight2.exec_stmt sha_ge e le m' rest t le' mf out ->
       Clight2.exec_stmt sha_ge e le m (inits_stmt its rest) t le' mf out).
Proof.
  induction its as [|it l IH]; intros cs le m HWf Hle HPerm Hdisp HMax HCs.
  - exists m. cbn [map rev app inits_stmt]. repeat split; auto.
  - destruct HWf as (HOk & HSep & HWf').
    pose proof (HPerm it (or_introl eq_refl)) as HPit.
    destruct it as [[[[[r c] f] d] bR] bC].
    destruct HOk as (HeR & HeC & Hf & Hd & HdA & NAC & NAR & NRC & NGC & NMC & NGR & NMR).
    destruct HPit as (PR & PC & PA).
    assert (VG : Mem.valid_block m GC) by (eapply load_valid_block; exact Hdisp).
    assert (VM : Mem.valid_block m GM) by (eapply load_valid_block; exact HMax).
    destruct (mt_init_step e bA HeI NGA NMA le m r c f bR bC d cs HeR HeC Hle Hf Hd HdA
      NAC NAR NRC NGC NMC NGR NMR PR PC PA Hdisp HMax HCs)
      as (m1 & HEx1 & HCs1 & HL1 & HP1 & HV1).
    { intros c0 Hc0. exact (HSep c0 Hc0). }
    destruct (IH ((bC, d, [], sha256_iv_words, Int64.zero, false) :: cs) le m1 HWf' Hle)
      as (m' & HCs' & HL' & HP' & HV' & HK').
    { intros it' Hit'. eapply item_perms_mono; [exact HP1|]. apply HPerm. right. exact Hit'. }
    { unfold sha_dispatch_ok. rewrite HL1; [exact Hdisp|exact VG|exact NGR|exact NGC|left; exact NGA]. }
    { rewrite HL1; [exact HMax|exact VM|exact NMR|exact NMC|left; exact NMA]. }
    { exact HCs1. }
    exists m'. split; [|split; [|split; [|split]]].
    + cbn [map rev]. rewrite <- app_assoc. exact HCs'.
    + intros ch b ofs Hb HU.
      rewrite HL'; [|apply HV1, Hb|intros it' Hit'; apply HU; right; exact Hit'].
      destruct (HU _ (or_introl eq_refl)) as (U1 & U2 & U3). apply HL1; assumption.
    + intros b ofs k p Hp. apply HP', HP1, Hp.
    + intros b Hb. apply HV', HV1, Hb.
    + intros rest t le' mf out HR. cbn [inits_stmt].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := t); [exact HEx1|apply HK'; exact HR].
Qed.
End Inits.
