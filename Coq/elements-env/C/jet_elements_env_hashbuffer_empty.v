(** [hashBuffer(result, buffer)] (elements/env.c) for the zero buffer
    [(rawElementsBuffer){0}] (NULL data pointer, length 0): the result is
    the SHA-256 state of the empty string, [hash_buffer_regs []].  The
    theorem [eval_hashBuffer] excludes the NULL data pointer; this is that
    case, which [copyOutput] and [copyInput] reach for absent proofs. *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jet_exec C.jet_memcpy_model C.jet_uint32_array_init C.jet_sha256_iv_init.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_block_local C.jet_sha_compress_call.
Require Import C.jet_sha_ctx8_model C.jet_sha_be64_exec C.jet_sha_uchars_prep C.jet_sha_uchars_exec.
Require Import C.jet_sha_add_n_init C.jet_sha_finalize_exec C.jet_sha_ctx_abs.
Require Import C.jet_elements_env_field_eval C.jet_elements_env_ctxo C.jet_elements_env_uchars_null.
Require Import C.jet_elements_env_tx_calls C.jet_elements_env_hashbuffer C.jet_elements_env_entropy.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque sha_ge.
Set Default Timeout 300.

Local Notation RBUF := (Tstruct _rawElementsBuffer noattr).

Theorem eval_hashBuffer_empty (Hmodel : memcpy_model) m bres ores bbuf obuf :
  0 <= ores -> ores + 32 <= Ptrofs.max_unsigned -> (4 | ores) ->
  Mem.range_perm m bres ores (ores + 32) Cur Writable ->
  GC <> bres -> GM <> bres ->
  0 <= obuf -> obuf + 16 <= Ptrofs.max_unsigned ->
  Mem.load Mptr m bbuf obuf = Some (Vlong Int64.zero) ->
  Mem.load Mint32 m bbuf (obuf + 8) = Some (Vint Int.zero) ->
  (bbuf <> bres \/ obuf + 16 <= ores \/ ores + 32 <= obuf) ->
  sha_dispatch_ok m -> Mem.load Mint64 m GM 0 = Some (Vlong sha_max_counter) ->
  exists m',
    Clight2.eval_funcall sha_ge m (Internal f_hashBuffer)
      [Vptr bres (Ptrofs.repr ores); Vptr bbuf (Ptrofs.repr obuf)] E0 m' Vundef /\
    (forall j, (j < 8)%nat ->
       Mem.load Mint32 m' bres (ores + 4 * Z.of_nat j) = Some (Vint (nth j (hash_buffer_regs []) Int.zero))) /\
    (forall ch b ofs, Mem.valid_block m b ->
       (b <> bres \/ ofs + size_chunk ch <= ores \/ ores + 32 <= ofs) ->
       Mem.load ch m' b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, Mem.valid_block m b -> Mem.perm m b ofs k p -> Mem.perm m' b ofs k p) /\
    (forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof.
  intros Ho0 HoM HoA PRes Hgo Hco Hb0 HbM HBuf HLen Hsep Hdisp HMax.
  assert (Hob : 0 <= ores /\ ores + 32 <= Ptrofs.max_unsigned) by (split; assumption).
  assert (VG : Mem.valid_block m GC).
  { unfold sha_dispatch_ok in Hdisp. eapply Mem.perm_valid_block.
    apply (proj1 (Mem.load_valid_access _ _ _ _ _ Hdisp) 0). cbn. lia. }
  assert (VM : Mem.valid_block m GM).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HMax) 0). cbn. lia. }
  assert (Vres : Mem.valid_block m bres) by (eapply Mem.perm_valid_block; apply (PRes ores); lia).
  assert (Vbuf : Mem.valid_block m bbuf).
  { eapply Mem.perm_valid_block. apply (proj1 (Mem.load_valid_access _ _ _ _ _ HBuf) obuf). cbn. lia. }
  destruct (Mem.alloc m 0 88) as [m1 bC] eqn:A1.
  destruct (Mem.alloc m1 0 88) as [m0 bR] eqn:A2.
  assert (NC : forall b, Mem.valid_block m b -> b <> bC).
  { intros b Hb E. subst b. exact (Mem.fresh_block_alloc _ _ _ _ _ A1 Hb). }
  assert (NR : forall b, Mem.valid_block m b -> b <> bR).
  { intros b Hb E. subst b. apply (Mem.fresh_block_alloc _ _ _ _ _ A2).
    eapply Mem.valid_block_alloc; [exact A1|exact Hb]. }
  assert (Hrx : bR <> bC).
  { intros E. apply (Mem.fresh_block_alloc _ _ _ _ _ A2). rewrite E. eapply Mem.valid_new_block. exact A1. }
  assert (L0 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch m0 b ofs = Mem.load ch m b ofs).
  { intros ch b ofs Hb.
    rewrite (Mem.load_alloc_unchanged _ _ _ _ _ A2) by (eapply Mem.valid_block_alloc; [exact A1|exact Hb]).
    eapply Mem.load_alloc_unchanged; [exact A1|exact Hb]. }
  assert (P0 : forall b ofs k p, Mem.perm m b ofs k p -> Mem.perm m0 b ofs k p).
  { intros b ofs k p Hp. eapply Mem.perm_alloc_1; [exact A2|]. eapply Mem.perm_alloc_1; [exact A1|exact Hp]. }
  assert (V0 : forall b, Mem.valid_block m b -> Mem.valid_block m0 b).
  { intros b Hb. eapply Mem.valid_block_alloc; [exact A2|]. eapply Mem.valid_block_alloc; [exact A1|exact Hb]. }
  assert (PC0 : Mem.range_perm m0 bC 0 88 Cur Freeable).
  { intros o Ho. eapply Mem.perm_alloc_1; [exact A2|]. eapply Mem.perm_alloc_2; [exact A1|exact Ho]. }
  assert (PR0 : Mem.range_perm m0 bR 0 88 Cur Freeable).
  { intros o Ho. eapply Mem.perm_alloc_2; [exact A2|exact Ho]. }
  assert (Hox : bres <> bC) by (apply NC, Vres).
  assert (Hro : bR <> bres) by (apply not_eq_sym, NR, Vres).
  assert (Hgx : GC <> bC) by (apply NC, VG).
  assert (Hcx : GM <> bC) by (apply NC, VM).
  assert (Hgr : GC <> bR) by (apply NR, VG).
  assert (Hcr : GM <> bR) by (apply NR, VM).
  set (e := hb_env bC bR).
  set (le := hb_temps (Vptr bres (Ptrofs.repr ores)) (Vptr bbuf (Ptrofs.repr obuf))).
  assert (VG0 : Mem.valid_block m0 GC) by (apply V0, VG).
  assert (VM0 : Mem.valid_block m0 GM) by (apply V0, VM).
  assert (PRes0 : Mem.range_perm m0 bres ores (ores + 32) Cur Writable).
  { intros o Ho. apply P0, PRes, Ho. }
  assert (Hdisp0 : sha_dispatch_ok m0) by (unfold sha_dispatch_ok; rewrite L0 by exact VG; exact Hdisp).
  assert (HMax0 : Mem.load Mint64 m0 GM 0 = Some (Vlong sha_max_counter)) by (rewrite L0 by exact VM; exact HMax).
  destruct ent_init_exec with (e := e) (idctx := _ctx) (idres := __res) (bx := bC) (br := bR) (bo := bres)
    (obase := ores) (le := le) (m := m0)
    (aout := Efield (Ederef (Etempvar _result (tptr MID)) MID) _s (tarray tuint 8))
    as (mx & X1 & C1 & L1 & P1 & V1); try assumption; try reflexivity.
  { intros m'. pose proof (eval_ptr_mid_s e le m' _result bres (Ptrofs.repr ores) eq_refl) as HE.
    rewrite Ptrofs.add_zero in HE. exact HE. }
  assert (HBufx : Mem.load Mptr mx bbuf obuf = Some (Vlong Int64.zero)).
  { rewrite L1; [rewrite L0 by exact Vbuf; exact HBuf|apply V0, Vbuf|apply NR, Vbuf|apply NC, Vbuf|].
    change (size_chunk Mptr) with 8. destruct Hsep as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
  assert (HLenx : Mem.load Mint32 mx bbuf (obuf + 8) = Some (Vint Int.zero)).
  { rewrite L1; [rewrite L0 by exact Vbuf; exact HLen|apply V0, Vbuf|apply NR, Vbuf|apply NC, Vbuf|].
    change (size_chunk Mint32) with 4. destruct Hsep as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia]. }
  destruct ctxo_uchars_null with (bx := bC) (bo := bres) (obase := ores) (m := mx) (l := @nil int)
    (regs := sha256_iv_words) (c := Int64.zero) (ovf := false)
    as (m2 & HU & C2 & L2 & P2 & V2); try assumption.
  set (le2 := PTree.set _t'2 (Vint Int.zero) (PTree.set _t'1 (Vlong Int64.zero) le)).
  destruct ent_final_exec with (e := e) (idctx := _ctx) (bx := bC) (bo := bres) (obase := ores) (le := le2) (m := m2)
    (l := @nil int) (regs := sha256_iv_words) (c := Int64.add Int64.zero Int64.zero)
    (ovf := uc_overflow false Int64.zero Int64.zero)
    as (m3 & XF & HR3 & L3 & P3 & V3); try assumption; try reflexivity.
  assert (P3' : forall b ofs k p, Mem.perm m0 b ofs k p -> Mem.perm m3 b ofs k p).
  { intros b ofs k p Hp. apply P3; [apply V2, V1; eapply Mem.perm_valid_block; exact Hp|]. apply P2, P1, Hp. }
  destruct (free_list_blocks [(bC, 0, 88); (bR, 0, 88)] m3) as (mf & HFL & HLf & HPf & HVf).
  { intros b lo hi HIn o Ho. apply P3'. cbn [In] in HIn.
    destruct HIn as [E|[E|[]]]; injection E as <- <- <-; [apply PC0|apply PR0]; exact Ho. }
  { cbn [map fst]. apply NoDup_cons; [intros [E|[]]; exact (Hrx E)|].
    apply NoDup_cons; [intros []|apply NoDup_nil]. }
  cbn [map fst] in HLf, HPf.
  assert (NIn : forall b, Mem.valid_block m b -> ~ In b [bC; bR]).
  { intros b Hb [E|[E|[]]]; [exact (NC b Hb (eq_sym E))|exact (NR b Hb (eq_sym E))]. }
  exists mf. split; [|split; [|split; [|split]]].
  - eapply eval_funcall_internal with (e := e) (le1 := le) (m1 := m0) (le2 := le2) (m2 := m3) (out := Out_normal).
    + eapply hb_entry; eassumption.
    + unfold f_hashBuffer. cbn [fn_body].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le) (m1 := mx); [exact X1|].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := m2); [|exact XF].
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := PTree.set _t'1 (Vlong Int64.zero) le) (m1 := mx).
      { apply exec_Sset. eapply eval_buffer_buf; [reflexivity|].
        rewrite Ptrofs.add_zero, Ptrofs.unsigned_repr by lia. exact HBufx. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le2) (m1 := mx).
      { apply exec_Sset. eapply eval_buffer_len; [reflexivity|].
        rewrite envu_ptr_add_repr, Ptrofs.unsigned_repr by lia. exact HLenx. }
      match type of HU with Clight2.eval_funcall _ _ _ _ _ _ ?vr =>
        change le2 with (set_opttemp None vr le2) at 2 end.
      eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha256_uchars) Ptrofs.zero)
        (vargs := [Vptr bC (Ptrofs.repr 0); Vlong Int64.zero; Vlong Int64.zero]) (f := Internal f_sha256_uchars).
      * reflexivity.
      * eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact sha_uchars_symbol]|].
        apply deref_loc_reference; reflexivity.
      * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
        eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
        eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|apply eval_Enil].
      * exact sha_uchars_funct.
      * reflexivity.
      * exact HU.
    + reflexivity.
    + unfold e. rewrite hb_blocks. exact HFL.
  - intros j Hj. rewrite HLf by (apply NIn, Vres). rewrite (HR3 j Hj). do 2 f_equal.
  - intros ch b ofs Hb Hr. rewrite HLf by (apply NIn, Hb).
    rewrite L3 by (try (apply V2, V1, V0; exact Hb); try (apply NC; exact Hb); exact Hr).
    rewrite L2 by (apply NC, Hb).
    rewrite L1 by (try (apply V0; exact Hb); try (apply NR; exact Hb); try (apply NC; exact Hb); exact Hr).
    apply L0, Hb.
  - intros b ofs k p Hb Hp. apply HPf; [apply NIn, Hb|]. apply P3', P0, Hp.
  - intros b Hb. apply HVf, V3, V2, V1, V0, Hb.
Qed.
