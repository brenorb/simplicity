(** The ten jets sha_256_ctx_8_add_{1,2,4,...,512} of the SHA translation
    unit against the literal ctx8Addn programs.

    Each jet copies the source frame and calls [sha_256_ctx_8_add_n] with its
    byte count.  The contract is the partial (assertion) jet contract in the
    SHA global environment: the call returns true exactly when the option
    semantics of the program is defined, and then writes its encoding.
    The theorems are conditional on the explicit [memcpy_model] and carry the
    explicit state premise [sha_globals_ok] (dispatch pointer and constant
    [sha256_max_counter] hold their initializers). *)
From Coq Require Import ZArith List Lia PeanoNat.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jet_exec C.jet_memcpy_model C.jet_partial.
Require Import C.jet_frame_copy C.jet_frame_copy_layout C.jet_frame_layout.
Require Import C.jet_input_layout C.jet_output_layout C.jet_write_layout C.jet_encoding C.jet_bitmachine_rep.
Require Import C.jet_buffer_input C.jet_sha256_ctx8_init_spec C.jet_constant_layout.
Require Import C.jets_sha C.jet_sha_linkage C.jet_sha_compress_call C.jet_sha_block_local.
Require Import C.jet_sha_ctx8_spec C.jet_sha_uchars_exec C.jet_sha_add_n_init C.jet_sha_add_n_exec.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 600.

Definition sha_jet_partial_local_spec (f : function) (A B : Ty) (spec : A -> option B) : Prop :=
  forall env m bd dbase bs sbase bi bw edge outedge cursor read_cursor (a : A),
    sha_globals_ok m ->
    frame_base_valid sbase -> (8 | sbase) ->
    frame_fields_at m bs sbase bi edge read_cursor ->
    0 <= read_cursor -> read_cursor + Z.of_nat (bitSize A) <= Int64.max_unsigned ->
    frame_input_cells_at m bi edge read_cursor (encode a) ->
    write_frame_at m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ->
    exists mf,
      Clight2.eval_funcall sha_ge m (Internal f)
        [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); env]
        E0 mf (jet_partial_return (spec a)) /\
      (match spec a with
       | Some b => frame_output_cells_at mf bw outedge cursor (encode b) /\
           write_prefix_at m mf bw outedge cursor /\
           frame_fields_at mf bd dbase bw outedge (cursor - Z.of_nat (bitSize B))
       | None => True
       end) /\
      (forall chunk b ofs, Mem.valid_block m b ->
        (b <> bd \/ ofs + size_chunk chunk <= dbase + 8 \/ dbase + 16 <= ofs) ->
        (b <> bw \/
          ofs + size_chunk chunk <= outedge + 8 * ((cursor - Z.of_nat (bitSize B)) / 64) \/
          write_word_address outedge cursor + 8 <= ofs) ->
        Mem.load chunk mf b ofs = Mem.load chunk m b ofs).

Notation FR := (Tstruct _frameItem noattr).

Definition add_n_ty : type :=
  Tfunction (Tcons FRP (Tcons FRP (Tcons tulong Tnil))) tbool cc_default.

Definition aw_body (K : Z) : statement :=
  Ssequence (Sassign (Evar _src FR) (Etempvar _src FR))
    (Ssequence
      (Scall (Some _t'1) (Evar _sha_256_ctx_8_add_n add_n_ty)
        [Etempvar _dst FRP; Eaddrof (Evar _src FR) FRP; Econst_int (Int.repr K) tint])
      (Sreturn (Some (Etempvar _t'1 tbool)))).

Definition aw_fun (f : function) (K : Z) : Prop :=
  fn_return f = tbool /\
  fn_params f = [(_dst, FRP); (_src, FR); (_env, tptr (Tstruct _txEnv noattr))] /\
  fn_vars f = [(_src, FR)] /\ fn_temps f = [(_t'1, tbool)] /\ fn_body f = aw_body K.

Definition aw_env (bl : block) : env := PTree.set _src (bl, FR) empty_env.
Definition aw_temps (env : val) (bd : block) (dbase : Z) (bs : block) (sbase : Z) : temp_env :=
  PTree.set _env env (PTree.set _src (Vptr bs (Ptrofs.repr sbase))
    (PTree.set _dst (Vptr bd (Ptrofs.repr dbase)) (create_undef_temps [(_t'1, tbool)]))).

Lemma aw_add_n_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha_256_ctx_8_add_n = Some (sha_symbol_block _sha_256_ctx_8_add_n).
Proof. vm_compute; reflexivity. Qed.
Lemma aw_add_n_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha_256_ctx_8_add_n) Ptrofs.zero) =
    Some (Internal f_sha_256_ctx_8_add_n).
Proof. vm_compute; reflexivity. Qed.
Lemma aw_blocks bl : blocks_of_env sha_ge (aw_env bl) = [(bl, 0, 16)].
Proof. vm_compute. reflexivity. Qed.

Lemma aw_copy m mc bl bs sbase bytes le :
  frame_base_valid sbase -> (8 | sbase) -> bl <> bs ->
  le!_src = Some (Vptr bs (Ptrofs.repr sbase)) ->
  Mem.loadbytes m bs sbase 16 = Some bytes -> Mem.storebytes m bl 0 bytes = Some mc ->
  Clight2.exec_stmt sha_ge (aw_env bl) le m (Sassign (Evar _src FR) (Etempvar _src FR)) E0 le mc Out_normal.
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

Local Opaque sha_ge.

Theorem sha_add_wrapper (Hmodel : memcpy_model) (f : function) (K : Z) (k : nat) :
  aw_fun f K -> (k <= 9)%nat ->
  Int64.repr (Int.signed (Int.repr K)) = Int64.repr (Z.of_nat (Nat.pow 2 k)) ->
  sha_jet_partial_local_spec f (Ty.Prod sha256_ctx8_type (Vector (Word 3) k)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec k optalg a).
Proof.
  intros (HfR & HfP & HfV & HfT & HfB) Hk HK
    env m bd dbase bs sbase bi bw edge outedge cursor rc [c v]
    HGl HSbase HSAlign HSource H0 Hmax Hin Hout.
  rewrite ctx8_addn_option.
  assert (HbitsA : Z.of_nat (bitSize (Ty.Prod sha256_ctx8_type (Vector (Word 3) k))) =
    830 + 8 * Z.of_nat (Nat.pow 2 k)).
  { change (bitSize (Ty.Prod sha256_ctx8_type (Vector (Word 3) k))) with
      (bitSize sha256_ctx8_type + bitSize (Vector (Word 3) k))%nat.
    rewrite sha256_ctx8_type_bits, vector_byte_bitSize. lia. }
  rewrite HbitsA in Hmax.
  rewrite sha256_ctx8_type_bits in *. change (Z.of_nat 830) with 830 in *.
  change (@encode (Ty.Prod sha256_ctx8_type (Vector (Word 3) k)) (c, v)) with (encode c ++ encode v) in Hin.
  destruct HGl as [Hdisp HMaxC].
  destruct HSource as [HSE HSO].
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HB].
  pose proof (Mem.loadbytes_length _ _ _ _ _ HB) as Hbyteslen.
  assert (Vs : Mem.valid_block m bs) by (eapply load_valid_block; exact HSE).
  assert (VG : Mem.valid_block m (sha_symbol_block _simplicity_sha256_compression))
    by (eapply load_valid_block; exact Hdisp).
  assert (VM : Mem.valid_block m (sha_symbol_block _sha256_max_counter))
    by (eapply load_valid_block; exact HMaxC).
  pose proof Hout as [HDbase [[HDE HDO] _]].
  assert (Vd : Mem.valid_block m bd) by (eapply load_valid_block; exact HDE).
  destruct (write_frame_at_head m bd dbase bw outedge cursor 830 ltac:(lia) Hout)
    as [_ [_ [_ [initialword HInitialWord]]]].
  assert (Vw : Mem.valid_block m bw) by (eapply load_valid_block; exact HInitialWord).
  assert (Vi : Mem.valid_block m bi).
  { apply frame_input_cells_at_app in Hin. destruct Hin as [_ HinV].
    rewrite encode_vector_values, frame_input_byte_list in HinV.
    pose proof (vector_values_length (Word 3) k v) as HVL.
    destruct (vector_values (Word 3) k v) as [|x0 vs'] eqn:Evs.
    { exfalso. cbn in HVL. pose proof (Nat.pow_nonzero 2 k ltac:(lia)). lia. }
    pose proof (HinV 0%nat x0 eq_refl) as Hw0.
    pose proof (Hw0 O _ (@jet_read16_input_word.frame_input_word_bits_nth 3 x0 O ltac:(vm_compute; lia))) as Hhead.
    destruct Hhead as [_ [_ [w [HL _]]]]. eapply load_valid_block; exact HL. }
  destruct (Mem.alloc m 0 16) as [ma bl] eqn:AL.
  pose proof (mext_alloc _ _ _ _ _ AL) as (XV & XL & XP & XA).
  assert (Fl : forall b0, Mem.valid_block m b0 -> b0 <> bl).
  { intros b0 Hv Heq. subst b0. exact (Mem.fresh_block_alloc _ _ _ _ _ AL Hv). }
  assert (PL : Mem.range_perm ma bl 0 16 Cur Freeable).
  { intros ofs Hr. eapply Mem.perm_alloc_2; eauto. }
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; [exact HB|exact AL|exact Vs]. }
  assert (PLW : Mem.range_perm ma bl 0 (0 + Z.of_nat (length bytes)) Cur Writable).
  { rewrite Hbyteslen. change (Mem.range_perm ma bl 0 16 Cur Writable).
    intros ofs Hr. eapply Mem.perm_implies; [apply PL; exact Hr|constructor]. }
  destruct (Mem.range_perm_storebytes ma bl 0 bytes PLW) as [mcp SC].
  assert (HSEa : Mem.load Mptr ma bs sbase = Some (Vptr bi (Ptrofs.repr edge)))
    by (rewrite XL by exact Vs; exact HSE).
  assert (HSOa : Mem.load Mint64 ma bs (sbase + 8) = Some (Vlong (Int64.repr rc)))
    by (rewrite XL by exact Vs; exact HSO).
  destruct (frame_copy_fields_at ma mcp bs sbase bl bytes _ _ HBa SC HSEa HSOa) as [HLE HLO].
  assert (K0 : forall chunk b0 ofs, Mem.valid_block m b0 -> Mem.load chunk mcp b0 ofs = Mem.load chunk m b0 ofs).
  { intros chunk b0 ofs Hv. erewrite Mem.load_storebytes_other; [|exact SC|left; apply Fl; exact Hv].
    apply XL. exact Hv. }
  assert (P0 : forall b0 ofs kd p, Mem.perm m b0 ofs kd p -> Mem.perm mcp b0 ofs kd p).
  { intros b0 ofs kd p Hp. eapply Mem.perm_storebytes_1; [exact SC|apply XP; exact Hp]. }
  assert (V0 : forall b0, Mem.valid_block m b0 -> Mem.valid_block mcp b0).
  { intros b0 Hv. eapply Mem.storebytes_valid_block_1; [exact SC|apply XV; exact Hv]. }
  assert (PLC : Mem.valid_access mcp Mint64 bl (0 + 8) Writable).
  { split; [|exists 1; reflexivity]. intros ofs Hr. eapply Mem.perm_storebytes_1; [exact SC|].
    eapply Mem.perm_implies with (p1 := Freeable); [apply PL; cbn in Hr; lia|constructor]. }
  assert (HLocalBase : frame_base_valid 0).
  { split; [lia|change (16 <= 18446744073709551615); lia]. }
  destruct (eval_sha_add_n Hmodel k mcp bd dbase bl 0 bi bw edge outedge cursor rc c v Hk)
    as (m5 & HCall & HObs & HFrame & HPerm5).
  { split; [unfold sha_dispatch_ok; rewrite K0 by exact VG; exact Hdisp|rewrite K0 by exact VM; exact HMaxC]. }
  { exact HLocalBase. }
  { split; [exact HLE|exact HLO]. }
  { exact PLC. }
  { exact H0. }
  { lia. }
  { eapply buffer_input_cells_preserved; [|exact Hin]. intros ofs w HL. rewrite K0 by exact Vi. exact HL. }
  { eapply write_frame_at_preserved; [| |exact Hout].
    - intros chunk b0 ofs v0 Hb HL. rewrite K0; [exact HL|destruct Hb; subst; assumption].
    - exact P0. }
  { intro Heq. apply (Fl bi Vi). congruence. }
  { intro Heq. apply (Fl bd Vd). congruence. }
  { intro Heq. apply (Fl bw Vw). congruence. }
  { intro Heq. apply (Fl _ VM). congruence. }
  { intro Heq. apply (Fl _ VG). congruence. }
  cbv zeta in HCall, HObs. rewrite vector_values_length in HCall. rewrite <- HK in HCall.
  set (spec := ctx8_add_list c (vector_values (Word 3) k v)) in *.
  (* free the local frame copy *)
  assert (Vl : Mem.valid_block mcp bl).
  { eapply Mem.storebytes_valid_block_1; [exact SC|]. eapply Mem.valid_new_block; exact AL. }
  destruct (free_list_blocks [(bl, 0, 16)] m5) as (mf & HFL & HLf & _ & _).
  { intros b0 lo hi [Heq|[]]. injection Heq as <- <- <-. intros ofs Hr.
    apply HPerm5; [exact Vl|]. eapply Mem.perm_storebytes_1; [exact SC|apply PL; exact Hr]. }
  { repeat constructor; cbn; tauto. }
  cbn [map fst] in HLf.
  assert (HNl : forall b0, Mem.valid_block m b0 -> ~ In b0 [bl]).
  { intros b0 Hv [Heq|[]]. exact (Fl b0 Hv (eq_sym Heq)). }
  set (le0 := aw_temps env bd dbase bs sbase).
  exists mf. split; [|split].
  - eapply eval_funcall_internal with (e := aw_env bl) (le1 := le0) (m1 := ma)
      (le2 := PTree.set _t'1 (jet_partial_return spec) le0) (m2 := m5)
      (out := Out_return (Some (jet_partial_return spec, tbool))).
    + constructor; rewrite ?HfV, ?HfP, ?HfT.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * cbn. repeat constructor; cbn; intuition discriminate.
      * intros x y HX HY Hxy. cbn in HX, HY.
        repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
          first [contradiction | vm_compute in Hxy; discriminate | congruence].
      * eapply alloc_variables_cons with (m1 := ma) (b1 := bl).
        -- change (Mem.alloc m 0 16 = (ma, bl)); exact AL.
        -- constructor.
      * reflexivity.
    + rewrite HfB. unfold aw_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (le1 := le0) (m1 := mcp).
      { eapply aw_copy; [exact HSbase|exact HSAlign| |reflexivity|exact HBa|exact SC].
        intro Heq. apply (Fl bs Vs). congruence. }
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0).
      { change (PTree.set _t'1 (jet_partial_return spec) le0) with
          (set_opttemp (Some _t'1) (jet_partial_return spec) le0).
        eapply exec_Scall with (vf := Vptr (sha_symbol_block _sha_256_ctx_8_add_n) Ptrofs.zero)
          (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bl Ptrofs.zero;
                     Vlong (Int64.repr (Int.signed (Int.repr K)))])
          (f := Internal f_sha_256_ctx_8_add_n).
        - reflexivity.
        - eapply eval_Elvalue; [apply eval_Evar_global; [reflexivity|exact aw_add_n_symbol]|].
          apply deref_loc_reference; reflexivity.
        - eapply eval_Econs; [apply eval_Etempvar; reflexivity|reflexivity|].
          eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int|reflexivity|apply eval_Enil].
        - exact aw_add_n_funct.
        - reflexivity.
        - exact HCall. }
      apply exec_Sreturn_some. apply eval_Etempvar. apply PTree.gss.
    + rewrite HfR. cbn. split; [discriminate|]. destruct spec; reflexivity.
    + rewrite aw_blocks. exact HFL.
  - destruct spec as [b|]; [|exact I]. destruct HObs as (HC & HP & [HF1 HF2]). split; [|split].
    + eapply frame_output_cells_preserved; [|exact HC].
      intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
    + eapply write_prefix_at_preserved; [| |exact HP].
      * intros ofs w HL. rewrite K0 by exact Vw. exact HL.
      * intros ofs w HL. rewrite HLf by (apply HNl; exact Vw). exact HL.
    + split; rewrite HLf by (apply HNl; exact Vd); assumption.
  - intros chunk b0 ofs Hv Hd Hw. rewrite HLf by (apply HNl; exact Hv).
    rewrite HFrame; [apply K0; exact Hv|apply V0; exact Hv|exact Hd|exact Hw|left; apply Fl; exact Hv].
Qed.

(** ** The ten jets *)
Ltac add_jet H K k :=
  apply (sha_add_wrapper H _ K k); [repeat split; reflexivity|lia|reflexivity].

Theorem sha_256_ctx_8_add_1_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_1
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 0)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 0 optalg a).
Proof. intro H. add_jet H 1 0%nat. Qed.

Theorem sha_256_ctx_8_add_2_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_2
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 1)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 1 optalg a).
Proof. intro H. add_jet H 2 1%nat. Qed.

Theorem sha_256_ctx_8_add_4_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_4
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 2)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 2 optalg a).
Proof. intro H. add_jet H 4 2%nat. Qed.

Theorem sha_256_ctx_8_add_8_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_8
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 3)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 3 optalg a).
Proof. intro H. add_jet H 8 3%nat. Qed.

Theorem sha_256_ctx_8_add_16_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_16
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 4)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 4 optalg a).
Proof. intro H. add_jet H 16 4%nat. Qed.

Theorem sha_256_ctx_8_add_32_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_32
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 5)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 5 optalg a).
Proof. intro H. add_jet H 32 5%nat. Qed.

Theorem sha_256_ctx_8_add_64_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_64
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 6)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 6 optalg a).
Proof. intro H. add_jet H 64 6%nat. Qed.

Theorem sha_256_ctx_8_add_128_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_128
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 7)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 7 optalg a).
Proof. intro H. add_jet H 128 7%nat. Qed.

Theorem sha_256_ctx_8_add_256_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_256
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 8)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 8 optalg a).
Proof. intro H. add_jet H 256 8%nat. Qed.

Theorem sha_256_ctx_8_add_512_local_spec : memcpy_model ->
  sha_jet_partial_local_spec f_simplicity_sha_256_ctx_8_add_512
    (Ty.Prod sha256_ctx8_type (Vector (Word 3) 9)) sha256_ctx8_type
    (fun a => @ctx8_addn_spec 9 optalg a).
Proof. intro H. add_jet H 512 9%nat. Qed.

