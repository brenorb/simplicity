(** End-to-end composition for the original calculation frame jets. *)
From Coq Require Import ZArith List Lia Permutation.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_memcpy_model C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_output_layout.
Require Import C.jet_write_layout C.jet_encoding C.jet_constant_layout C.jet_bitmachine_rep.
Require Import C.jet_struct_copy_loads C.jet_uint32_array_init C.jet_elements_support_sha_compress_call.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_issuance_calc_spec.
Require Import C.jet_calculation_calls_calculation_calls.
Require Import C.jet_calculation_lifecycle_entry C.jet_calculation_lifecycle_allocation C.jet_calculation_lifecycle_shape.
Require Import C.jet_calculation_lifecycle_read C.jet_calculation_lifecycle_writer.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition calculation_jet_local_spec (f : function) (spec : Ty.tySem Word256 -> Ty.tySem Word256) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor rc (h : Ty.tySem Word256),
    elements_calculation_dispatch_ok m ->
    frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m bs sbase bi edge rc ->
    0 <= rc -> rc + 256 <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge rc (@encode Word256 h) ->
    write_frame_at m bd dbase bw outedge cursor 256 ->
    exists mf,
      Clight2.eval_funcall elements_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env] E0 mf (Vint Int.one) /\
      frame_output_cells_at mf bw outedge cursor (@encode Word256 (spec h)) /\
      write_prefix_at m mf bw outedge cursor /\
      frame_fields_at mf bd dbase bw outedge (cursor - 256) /\
      (forall ch b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk ch <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/ ofs + size_chunk ch <= outedge + 8 * ((cursor - 256) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load ch mf b ofs = Mem.load ch m b ofs).

Lemma calculation_jet_from_helper f jid p cf spec :
  calculation_frame_header f -> fn_body f = calc_body jid p ->
  (forall bl bh br bt, (calculation_frame_env bl bh br bt)!jid = None) ->
  Genv.find_symbol (Clight.genv_genv elements_ge) jid = Some (elements_symbol_block jid) ->
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block jid) Ptrofs.zero) = Some (Internal cf) ->
  type_of_fundef (Internal cf) = Tfunction (Tcons calc_mid_ptr (Tcons calc_mid_ptr (calc_suffix_types p))) tvoid calc_cc ->
  elements_calculation_word_call cf (calc_suffix_values p) spec ->
  calculation_jet_local_spec f spec.
Proof.
  intros HHeader HBody HNone HSym HFun HType HCall.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc h HD HB HA HF H0 HM HI HO.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact (proj1 HF)).
  pose proof HO as [HDB [[HDE HDO] HRest]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 256 ltac:(lia) HO)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (Vg : Mem.valid_block m (elements_symbol_block _simplicity_sha256_compression))
    by (eapply load_valid_block; exact HD).
  destruct (calc_read_prefix m bs sbase bi edge rc h HB HA HF H0 HM HI)
    as (m1 & m2 & m3 & m4 & bl & bh & br & bt & bytes0 & mcp & mr &
        A1 & A2 & A3 & A4 & B0 & S0 & HCRead & HInput & HSource & XR & Fresh & ND & Owned).
  destruct XR as (VR & KR & PR & AR).
  pose proof Owned as Own. repeat rewrite Forall2_cons_iff in Own.
  destruct Own as [[PL VL] [[PH VH] [[PRl VRl] [[PT VT] _]]]].
  assert (HDr : elements_calculation_dispatch_ok mr).
  { unfold elements_calculation_dispatch_ok in *. rewrite KR by exact Vg. exact HD. }
  destruct (HCall mr bt 0 bh Ptrofs.zero h
    ltac:(lia) ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)
    ltac:(exists 0; reflexivity)
    ltac:(intros ofs Hr; eapply Mem.perm_implies; [apply PT; lia|constructor])
    ltac:(change Ptrofs.max_unsigned with 18446744073709551615; change (0 + 32 <= 18446744073709551615); lia)
    HInput HDr) as (mt & HCHelper & HResult & Kt & HPt & HVt).
  assert (Phelp : forall b ofs k q, Mem.perm mr b ofs k q -> Mem.perm mt b ofs k q).
  { intros b ofs k q H. apply HPt; [eapply Mem.perm_valid_block; exact H|exact H]. }
  assert (Kt0 : forall ch b ofs, Mem.valid_block m b -> Mem.load ch mt b ofs = Mem.load ch m b ofs).
  { intros ch b ofs V. rewrite Kt; [apply KR; exact V|apply VR; exact V|].
    left. intro E; subst b. apply (Fresh bt V). right; right; right; left; reflexivity. }
  assert (PTR : Mem.range_perm mt bt 0 (0 + 32) Cur Readable).
  { intros ofs Hr. apply Phelp. eapply Mem.perm_implies; [apply PT; lia|constructor; constructor]. }
  destruct (Mem.range_perm_loadbytes mt bt 0 32 PTR) as [bytes1 B1].
  pose proof (Mem.loadbytes_length _ _ _ _ _ B1) as HLen.
  assert (PRW : Mem.range_perm mt br 0 (0 + Z.of_nat (length bytes1)) Cur Writable).
  { rewrite HLen. change (Mem.range_perm mt br 0 32 Cur Writable).
    intros ofs Hr. apply Phelp. eapply Mem.perm_implies; [apply PRl; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes mt br 0 bytes1 PRW) as [mc S1].
  assert (BC : Mem.loadbytes mc br 0 32 = Some bytes1).
  { pose proof (Mem.loadbytes_storebytes_same _ _ _ _ _ S1) as H. rewrite HLen in H. exact H. }
  assert (HResultC : uint32_array_at mc br 0 (hash256_reg (to_hash256 (spec h)))).
  { intros j x Hx. assert (Hj : (j < 8)%nat).
    { rewrite <- (hash256_len (to_hash256 (spec h))). apply nth_error_Some. rewrite Hx; discriminate. }
    eapply equal_loadbytes_field with (m1 := mt) (b1 := bt) (base1 := 0) (base2 := 0)
      (n := 32) (delta := 4 * Z.of_nat j) (bytes := bytes1).
    - lia.
    - change (size_chunk Mint32) with 4. lia.
    - exact B1.
    - exact BC.
    - change (4 | 0 + 4 * Z.of_nat j). exists (Z.of_nat j); lia.
    - exact (HResult j x Hx). }
  assert (Pc : forall b ofs k q, Mem.perm mr b ofs k q -> Mem.perm mc b ofs k q).
  { intros b ofs k q H. eapply Mem.perm_storebytes_1; [exact S1|apply Phelp; exact H]. }
  assert (Vc : forall b, Mem.valid_block mr b -> Mem.valid_block mc b).
  { intros b V. eapply Mem.storebytes_valid_block_1; [exact S1|apply HVt; exact V]. }
  assert (Kc : forall ch b ofs, Mem.valid_block m b -> Mem.load ch mc b ofs = Mem.load ch m b ofs).
  { intros ch b ofs V. erewrite Mem.load_storebytes_other; [apply Kt0; exact V|exact S1|].
    left. intro E; subst b. apply (Fresh br V). right; right; left; reflexivity. }
  assert (HOc : write_frame_at mc bd dbase bw outedge cursor 256).
  { eapply write_frame_at_preserved; [| |exact HO].
    - intros ch b ofs v E HL. rewrite Kc; [exact HL|destruct E; subst; assumption].
    - intros b ofs k q H. apply Pc, PR; exact H. }
  assert (Hrd : br <> bd).
  { intro E; subst bd. apply (Fresh br Vd). right; right; left; reflexivity. }
  assert (Hrw : br <> bw).
  { intro E; subst bw. apply (Fresh br Vw). right; right; left; reflexivity. }
  destruct (calc_writehash_from_frame mc br bd dbase bw outedge cursor (spec h) Hrd Hrw HResultC HOc)
    as (me & HCWrite & HCells & HPrefix & HFields & HLoads & HPe & HVe).
  assert (OwnedE : Forall2 (fun b z => Mem.range_perm me b 0 z Cur Freeable /\ Mem.valid_block me b)
    [bl; bh; br; bt] [16; 32; 32; 32]).
  { eapply calc_owned_preserved; [| |exact Owned].
    - intros b ofs k q H. apply HPe, Pc; exact H.
    - intros b V. apply HVe, Vc; exact V. }
  repeat rewrite Forall2_cons_iff in OwnedE.
  destruct OwnedE as [[PLE VLE] [[PHE VHE] [[PRE VRE] [[PTE VTE] _]]]].
  assert (PF : forall b lo hi, In (b, lo, hi) [(bl, 0, 16); (bh, 0, 32); (bt, 0, 32); (br, 0, 32)] ->
    Mem.range_perm me b lo hi Cur Freeable).
  { intros b lo hi H. cbn in H.
    destruct H as [E|[E|[E|[E|[]]]]]; injection E as <- <- <-; assumption. }
  destruct (free_list_blocks [(bl, 0, 16); (bh, 0, 32); (bt, 0, 32); (br, 0, 32)] me PF)
    as (mf & HFree & KFree & PFree & VFree).
  { change (NoDup [bl; bh; bt; br]).
    eapply Permutation_NoDup; [|exact ND]. apply perm_skip, perm_skip, perm_swap. }
  assert (Kf : forall ch b ofs, Mem.valid_block m b -> Mem.load ch mf b ofs = Mem.load ch me b ofs).
  { intros ch b ofs V. apply KFree. change (~ In b [bl; bh; bt; br]).
    intro H. apply (Fresh b V). destruct H as [E|[E|[E|[E|[]]]]].
    - left; exact E.
    - right; left; exact E.
    - right; right; right; left; exact E.
    - right; right; left; exact E. }
  exists mf. split.
  - eapply calc_function_composes with (jid := jid) (p := p) (cf := cf)
      (m1 := m1) (m2 := m2) (m3 := m3) (m4 := m4) (mcp := mcp) (mr := mr)
      (mt := mt) (mc := mc) (me := me) (bl := bl) (bh := bh) (br := br) (bt := bt)
      (bytes0 := bytes0) (bytes1 := bytes1); try eassumption.
    + apply HNone.
    + intro E; subst bs. apply (Fresh bl Vs). left; reflexivity.
    + repeat rewrite NoDup_cons_iff in ND. cbn in ND. intuition congruence.
  - split.
    + eapply frame_output_cells_preserved; [|exact HCells].
      intros ofs w HL. rewrite Kf by exact Vw. exact HL.
    + split.
      * eapply write_prefix_at_preserved; [| |exact HPrefix].
        -- intros ofs w HL. rewrite Kc by exact Vw. exact HL.
        -- intros ofs w HL. rewrite Kf by exact Vw. exact HL.
      * split.
        -- destruct HFields as [HE HC]. split; rewrite Kf by exact Vd; assumption.
        -- intros ch b ofs V Hbd Hbw. rewrite Kf by exact V.
           rewrite HLoads by assumption. apply Kc; exact V.
Qed.

Lemma calc_asset_not_local bl bh br bt :
  (calculation_frame_env bl bh br bt)!_simplicity_calculateAsset = None.
Proof. reflexivity. Qed.
Lemma calc_token_not_local bl bh br bt :
  (calculation_frame_env bl bh br bt)!_simplicity_calculateToken = None.
Proof. reflexivity. Qed.

Lemma calc_asset_link :
  Genv.find_symbol (Clight.genv_genv elements_ge) _simplicity_calculateAsset =
    Some (elements_symbol_block _simplicity_calculateAsset) /\
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _simplicity_calculateAsset) Ptrofs.zero) = Some (Internal f_simplicity_calculateAsset) /\
  type_of_fundef (Internal f_simplicity_calculateAsset) =
    Tfunction (Tcons calc_mid_ptr (Tcons calc_mid_ptr (calc_suffix_types None))) tvoid calc_cc.
Proof. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|reflexivity]. Qed.

Lemma calc_token_link :
  Genv.find_symbol (Clight.genv_genv elements_ge) _simplicity_calculateToken =
    Some (elements_symbol_block _simplicity_calculateToken) /\
  Genv.find_funct (Clight.genv_genv elements_ge)
    (Vptr (elements_symbol_block _simplicity_calculateToken) Ptrofs.zero) = Some (Internal f_simplicity_calculateToken) /\
  type_of_fundef (Internal f_simplicity_calculateToken) =
    Tfunction (Tcons calc_mid_ptr (Tcons calc_mid_ptr (calc_suffix_types (Some 1)))) tvoid calc_cc.
Proof. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|reflexivity]. Qed.

Theorem calculate_asset_local_spec (Hmodel : memcpy_model) :
  calculation_jet_local_spec f_simplicity_calculate_asset (@calculate_asset_spec Alg.CoreFunSem).
Proof.
  destruct calc_asset_link as [HS [HF HT]].
  eapply calculation_jet_from_helper with (jid := _simplicity_calculateAsset) (p := None)
    (cf := f_simplicity_calculateAsset).
  - exact calculate_asset_frame_header.
  - exact calc_asset_body.
  - exact calc_asset_not_local.
  - exact HS.
  - exact HF.
  - exact HT.
  - exact (elements_calculate_asset_word_call Hmodel).
Qed.

Theorem calculate_explicit_token_local_spec (Hmodel : memcpy_model) :
  calculation_jet_local_spec f_simplicity_calculate_explicit_token (@calculate_explicit_token_spec Alg.CoreFunSem).
Proof.
  destruct calc_token_link as [HS [HF HT]].
  eapply calculation_jet_from_helper with (jid := _simplicity_calculateToken) (p := Some 1)
    (cf := f_simplicity_calculateToken).
  - exact calculate_explicit_token_frame_header.
  - exact calc_explicit_body.
  - exact calc_token_not_local.
  - exact HS.
  - exact HF.
  - exact HT.
  - exact (elements_calculate_explicit_token_word_call Hmodel).
Qed.

Theorem calculate_confidential_token_local_spec (Hmodel : memcpy_model) :
  calculation_jet_local_spec f_simplicity_calculate_confidential_token (@calculate_confidential_token_spec Alg.CoreFunSem).
Proof.
  destruct calc_token_link as [HS [HF HT]].
  eapply calculation_jet_from_helper with (jid := _simplicity_calculateToken) (p := Some 2)
    (cf := f_simplicity_calculateToken).
  - exact calculate_confidential_token_frame_header.
  - exact calc_confidential_body.
  - exact calc_token_not_local.
  - exact HS.
  - exact HF.
  - exact HT.
  - exact (elements_calculate_confidential_token_word_call Hmodel).
Qed.
