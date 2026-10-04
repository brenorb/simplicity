(** Actual Bitcoin check_lock_height / check_lock_time jets against the literal
    canonical TimeLock programs
      [assert (iden &&& (unit >>> txLockHeight) >>> le word32)].
    C: [x = simplicity_read32(&src); return x <= lockHeight(env->tx);] *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_partial C.jet_partial C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_order_spec C.jet_frame_spec.
Require Import C.jet_complement_wide_layout.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_wrapper C.jet_bitcoin_bool_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_read_step.
Require Import C.jet_bitcoin_current_spec C.jet_bitcoin_distance_spec.
Require Import C.jet_bitcoin_fee_local C.jet_bitcoin_is_final_spec C.jet_bitcoin_is_final_local.
Require Import C.jet_bitcoin_lock_exec C.jet_bitcoin_lock_spec C.jet_bitcoin_lock_local.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Definition bitcoin_check_lock_program (height : bool) {alg : Primitive.Algebra} :
    alg (Word 5) Ty.Unit :=
  bitcoin_assert_spec
    (bitcoin_comp
      (bitcoin_pair (bitcoin_core (fun alg => @DC.iden (Word 5) alg))
        (bitcoin_comp (bitcoin_core (fun alg => @DC.unit (Word 5) alg))
          (lock_program height bitcoin_tx_is_final_spec bitcoin_lock_time_prim)))
      (bitcoin_core (fun alg => @le_word_spec alg 5))).

Definition bitcoin_check_lock_height_spec {alg : Primitive.Algebra} : alg (Word 5) Ty.Unit :=
  bitcoin_check_lock_program Datatypes.true.
Definition bitcoin_check_lock_time_spec {alg : Primitive.Algebra} : alg (Word 5) Ty.Unit :=
  bitcoin_check_lock_program Datatypes.false.

Lemma lock_value_range height final z :
  0 <= z < 4294967296 -> 0 <= lock_value height final z < 4294967296.
Proof.
  intro Hz. unfold lock_value.
  destruct final; [lia|]. destruct (z <? 500000000); destruct height; lia.
Qed.

Lemma bitcoin_lock_value_range height (environment : Bitcoin.env) :
  0 <= bitcoin_lock_value height environment < 4294967296.
Proof.
  apply lock_value_range. exact (Int.unsigned_range (sigTxLock (Bitcoin.envTx environment))).
Qed.

Lemma bit_match_toBool (v : Ty.tySem Bit.Bit) :
  match v with inl _ => None | inr b => Some b end =
    if Bit.toBool v then Some tt else None.
Proof. destruct v as [ [] | [] ]; reflexivity. Qed.

Lemma bitcoin_check_lock_program_value height (x : Ty.tySem (Word 5)) (environment : Bitcoin.env) :
  @bitcoin_check_lock_program height (PrimitivePrimSem option_Monad_Zero) x environment =
    if @toZ (WordToZ 5) x <=? bitcoin_lock_value height environment then Some tt else None.
Proof.
  unfold bitcoin_check_lock_program.
  rewrite bitcoin_assert_sem, bitcoin_comp_sem, bitcoin_pair_sem.
  rewrite (bitcoin_core_sem (fun alg => @DC.iden (Word 5) alg))
    by (intros alg1 alg2 R; apply Alg.iden_Parametric).
  rewrite bitcoin_comp_sem.
  rewrite (bitcoin_core_sem (fun alg => @DC.unit (Word 5) alg))
    by (intros alg1 alg2 R; apply Alg.unit_Parametric).
  assert (HL : lock_program height (@bitcoin_tx_is_final_spec (PrimitivePrimSem option_Monad_Zero))
      (@bitcoin_lock_time_prim (PrimitivePrimSem option_Monad_Zero))
      (@DC.unit (Word 5) Alg.CoreFunSem x) environment =
    Some (@fromZ (WordToZ 5) (bitcoin_lock_value height environment)))
    by exact (bitcoin_lock_program_value height environment).
  rewrite HL.
  rewrite (bitcoin_core_sem (fun alg => @le_word_spec alg 5) (le_word_spec_parametric 5)).
  pose proof (le_word_spec_numeric 5 (@DC.iden (Word 5) Alg.CoreFunSem x)
    (@fromZ (WordToZ 5) (bitcoin_lock_value height environment))) as Hle.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize in Hle.
  rewrite Z.mod_small in Hle by exact (bitcoin_lock_value_range height environment).
  change (@toZ (WordToZ 5) (@DC.iden (Word 5) Alg.CoreFunSem x)) with (@toZ (WordToZ 5) x) in Hle.
  rewrite <- Hle.
  apply bit_match_toBool.
Qed.

Definition bitcoin_check_lock_rest (fid : ident) : statement :=
  Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _simplicity_read32 (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
        [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
      (Sset _x (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence (bitcoin_env_tx_set _t'3)
        (Scall (Some _t'2) (Evar fid lock_fn_type)
          [Etempvar _t'3 (tptr (Tstruct _bitcoinTransaction noattr))]))
      (Sreturn (Some (Ebinop Ole (Etempvar _x tulong) (Etempvar _t'2 tulong) tint)))).

Lemma exec_bitcoin_check_lock_rest fid f bl le mc mr be ebase bt tbase (xr r : int64) :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) =
    Some (Internal f) ->
  type_of_fundef (Internal f) = lock_fn_type ->
  (bitcoin_version_locals bl)!fid = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_read32)
    [Vptr bl (Ptrofs.repr 0)] E0 mr (Vlong xr) ->
  Mem.load Mptr mr be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.eval_funcall bitcoin_ge mr (Internal f) [Vptr bt (Ptrofs.repr tbase)] E0 mr (Vlong r) ->
  exists le1, Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl) le mc
    (bitcoin_check_lock_rest fid) E0 le1 mr
    (Out_return (Some (Val.of_bool (negb (Int64.ltu r xr)), tint))).
Proof.
  intros Hsym Hfun Hty HEf HEnv He HE0 Hread HL HLock.
  set (l1 := PTree.set _t'1 (Vlong xr) le).
  set (l2 := PTree.set _x (Vlong xr) l1).
  set (l3 := PTree.set _t'3 (Vptr bt (Ptrofs.repr tbase)) l2).
  set (l4 := PTree.set _t'2 (Vlong r) l3).
  exists l4. unfold bitcoin_check_lock_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l2).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l1).
    + change l1 with (set_opttemp (Some _t'1) (Vlong xr) le).
      eapply exec_bitcoin_helper_call with (id := _simplicity_read32) (f := jets.f_simplicity_read32)
        (vargs := [Vptr bl Ptrofs.zero]) (vres := Vlong xr).
      * unfold bitcoin_core_helpers. simpl. tauto.
      * reflexivity.
      * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
      * reflexivity.
      * exact Hread.
    + apply exec_set. apply eval_Etempvar. unfold l1. apply PTree.gss.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l4).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l3).
      * eapply exec_bitcoin_env_tx_set; [|exact He|exact HE0|exact HL].
        unfold l2, l1. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HEnv.
      * change l4 with (set_opttemp (Some _t'2) (Vlong r) l3).
        eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block fid) Ptrofs.zero)
          (vargs := [Vptr bt (Ptrofs.repr tbase)]) (f := Internal f).
        -- reflexivity.
        -- eapply eval_Elvalue.
           ++ apply eval_Evar_global; [exact HEf|exact Hsym].
           ++ apply deref_loc_reference; reflexivity.
        -- eapply eval_Econs; [apply eval_Etempvar; unfold l3; apply PTree.gss|reflexivity|apply eval_Enil].
        -- exact Hfun.
        -- exact Hty.
        -- exact HLock.
    + apply exec_Sreturn_some.
      eapply eval_Ebinop with (v1 := Vlong xr) (v2 := Vlong r).
      * apply eval_Etempvar. unfold l4, l3. rewrite PTree.gso by discriminate.
        rewrite PTree.gso by discriminate. unfold l2. apply PTree.gss.
      * apply eval_Etempvar. unfold l4. apply PTree.gss.
      * reflexivity.
Qed.

Definition bitcoin_check_lock_env_rep (m : mem) (env : val) (environment : Bitcoin.env) : Prop :=
  exists fp, bitcoin_lock_env_rep m env environment fp.

Lemma lock_result_unsigned (height final : bool) (lt : int64) (L : Z) :
  Int64.unsigned lt = L ->
  Int64.unsigned (lock_result final (if height then Int64.ltu lt lock_threshold
                                     else negb (Int64.ltu lt lock_threshold)) lt) =
    lock_value height final L.
Proof.
  intros HL. unfold lock_result, lock_value. rewrite lock_threshold_ltu, HL.
  destruct final; [reflexivity|].
  destruct (L <? 500000000); destruct height; cbn [negb andb]; first [reflexivity|exact HL].
Qed.

Lemma load_valid_block chunk m b ofs v : Mem.load chunk m b ofs = Some v -> Mem.valid_block m b.
Proof.
  intro HL. apply Mem.load_valid_access in HL.
  eapply Mem.valid_access_valid_block. eapply Mem.valid_access_implies; [exact HL|constructor].
Qed.

Section CheckLockJet.
Variable height : bool.
Variable jet : function.
Variable fid : ident.
Variable f : function.
Hypothesis Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid).
Hypothesis Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge)
  (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) = Some (Internal f).
Hypothesis Hshape : bitcoin_wrapper_shape jet (bitcoin_check_lock_rest fid).
Hypothesis Hlocal : forall bl, (bitcoin_version_locals bl)!fid = None.
Hypothesis Hexec : forall m bt tbase (b : bool) lt,
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bt (tbase + 480) = Some (Vint (bool_int b)) ->
  Mem.load Mint64 m bt (tbase + 472) = Some (Vlong lt) ->
  Clight2.eval_funcall bitcoin_ge m (Internal f) [Vptr bt (Ptrofs.repr tbase)] E0 m
    (Vlong (lock_result b (if height then Int64.ltu lt lock_threshold
                           else negb (Int64.ltu lt lock_threshold)) lt)).
Hypothesis Hty : type_of_fundef (Internal f) = lock_fn_type.

Lemma bitcoin_check_lock_jet_spec :
  application_jet_partial_spec jet bitcoin_ge Bitcoin.env (Word 5) Ty.Unit bitcoin_check_lock_env_rep
    (fun a environment =>
      @bitcoin_check_lock_program height (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor x
    (fp & be & ebase & bt & tbase & lt & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HFin & HLt & HR & HFp)
    HB HA HRF HR0 HRmax Hin HFrame.
  subst env.
  pose proof HRF as [HSedge HSoff].
  apply frame_input_word_at_encode in Hin.
  change (Z.of_nat (bitSize (Word 5))) with 32 in HRmax.
  set (bf := forallb sequence_final (sigTxIn (Bitcoin.envTx environment))) in *.
  set (r := lock_result bf (if height then Int64.ltu lt lock_threshold
                            else negb (Int64.ltu lt lock_threshold)) lt).
  assert (HRU : Int64.unsigned r = bitcoin_lock_value height environment).
  { unfold r, bitcoin_lock_value. apply lock_result_unsigned. exact HR. }
  set (ok := @toZ (WordToZ 5) x <=? bitcoin_lock_value height environment).
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  destruct (bitcoin_bool_wrapper jet (bitcoin_check_lock_rest fid) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bytes ok Hshape HB HA HBytes) as (mf & HCall & HMem).
  { intros ma mc bl HAlloc HBa HStore.
    destruct (bitcoin_read_wide_step W32 m ma mc bl bs sbase bi edge read_cursor x bytes
      ltac:(change (wide_bits W32) with 32; lia) HRF Hin HAlloc HBa HStore)
      as (mr & xr & Hread & Hxr & _ & HMemR & HPermR & _ & HKeep).
    assert (Hok : negb (Int64.ltu r xr) = ok).
    { unfold ok, Int64.ltu. rewrite HRU, Hxr.
      change (@toZ (WordToZ (wide_log W32)) x) with (@toZ (WordToZ 5) x).
      destruct (zlt (bitcoin_lock_value height environment) (@toZ (WordToZ 5) x)); symmetry;
        [apply Z.leb_gt|apply Z.leb_le]; cbn [negb]; lia. }
    destruct (exec_bitcoin_check_lock_rest fid f bl
      (bitcoin_wrapper_temps jet (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc mr be ebase bt tbase xr r Hsym Hfun Hty (Hlocal bl)
      ltac:(unfold bitcoin_wrapper_temps; apply PTree.gss) He0 ltac:(lia) Hread
      (HKeep _ _ _ _ HLoad)
      (Hexec mr bt tbase bf lt Ht0 HtM (HKeep _ _ _ _ HFin) (HKeep _ _ _ _ HLt))) as [le1 HExec].
    rewrite Hok in HExec.
    exists le1, mr. split; [exact HExec|]. split; [exact HMemR|exact HPermR]. }
  exists mf. rewrite bitcoin_check_lock_program_value. fold ok.
  split; [destruct ok; exact HCall|]. split.
  - destruct ok; [|exact I].
    destruct HFrame as (_ & [HDE HDO] & _).
    split; [intros i c Hi; destruct i; discriminate|]. split.
    + intros old HL. exists old. split.
      * rewrite HMem by (eapply load_valid_block; exact HL). exact HL.
      * intros i _ _. reflexivity.
    + change (Z.of_nat (bitSize Ty.Unit)) with 0. rewrite Z.sub_0_r. split.
      * rewrite HMem by (eapply load_valid_block; exact HDE). exact HDE.
      * rewrite HMem by (eapply load_valid_block; exact HDO). exact HDO.
  - intros chunk b ofs HV _ _. apply HMem. exact HV.
Qed.
End CheckLockJet.

Lemma lockHeight_exec m bt tbase (b : bool) lt :
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bt (tbase + 480) = Some (Vint (bool_int b)) ->
  Mem.load Mint64 m bt (tbase + 472) = Some (Vlong lt) ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_lockHeight) [Vptr bt (Ptrofs.repr tbase)] E0 m
    (Vlong (lock_result b (Int64.ltu lt lock_threshold) lt)).
Proof.
  intros H0 HM HB HL. rewrite f_lockHeight_shape.
  apply eval_lock_fn; [exact H0|exact HM|exact HB|exact HL|].
  intros le Hle. apply lock_height_cmp_eval. exact Hle.
Qed.

Lemma lockTime_exec m bt tbase (b : bool) lt :
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bt (tbase + 480) = Some (Vint (bool_int b)) ->
  Mem.load Mint64 m bt (tbase + 472) = Some (Vlong lt) ->
  Clight2.eval_funcall bitcoin_ge m (Internal f_lockTime) [Vptr bt (Ptrofs.repr tbase)] E0 m
    (Vlong (lock_result b (negb (Int64.ltu lt lock_threshold)) lt)).
Proof.
  intros H0 HM HB HL. rewrite f_lockTime_shape.
  apply eval_lock_fn; [exact H0|exact HM|exact HB|exact HL|].
  intros le Hle. apply lock_time_cmp_eval. exact Hle.
Qed.

Lemma bitcoin_check_lock_height_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_check_lock_height (bitcoin_check_lock_rest _lockHeight).
Proof. wrapper_shape. Qed.
Lemma bitcoin_check_lock_time_shape :
  bitcoin_wrapper_shape f_simplicity_bitcoin_check_lock_time (bitcoin_check_lock_rest _lockTime).
Proof. wrapper_shape. Qed.

Theorem bitcoin_check_lock_height_local_spec :
  application_jet_partial_spec f_simplicity_bitcoin_check_lock_height bitcoin_ge Bitcoin.env
    (Word 5) Ty.Unit bitcoin_check_lock_env_rep
    (fun a environment => @bitcoin_check_lock_height_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_check_lock_jet_spec Datatypes.true) with (fid := _lockHeight) (f := f_lockHeight).
  - exact bitcoin_lockHeight_symbol.
  - exact bitcoin_lockHeight_funct.
  - exact bitcoin_check_lock_height_shape.
  - intro bl. reflexivity.
  - exact lockHeight_exec.
  - reflexivity.
Qed.

Theorem bitcoin_check_lock_time_local_spec :
  application_jet_partial_spec f_simplicity_bitcoin_check_lock_time bitcoin_ge Bitcoin.env
    (Word 5) Ty.Unit bitcoin_check_lock_env_rep
    (fun a environment => @bitcoin_check_lock_time_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_check_lock_jet_spec Datatypes.false) with (fid := _lockTime) (f := f_lockTime).
  - exact bitcoin_lockTime_symbol.
  - exact bitcoin_lockTime_funct.
  - exact bitcoin_check_lock_time_shape.
  - intro bl. reflexivity.
  - exact lockTime_exec.
  - reflexivity.
Qed.
