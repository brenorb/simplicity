(** Actual legacy Elements relative-lock assertion jets. The C false return
    corresponds to specification failure; no success/comparison is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine Simplicity.Util.Option.
Require Import C.jet_exec C.jet_application_partial C.jet_partial C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_order_spec C.jet_frame_spec C.jet_complement_wide_layout.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_elements_version_exec.
Require Import C.jet_elements_field_eval C.jet_elements_wrapper C.jet_elements_bool_wrapper.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_read_step C.jet_elements_tx_field_set.
Require Import C.jet_elements_current_spec C.jet_elements_prim_sem C.jet_bitcoin_distance_spec.
Require Import C.jet_elements_legacy_lock_spec C.jet_elements_legacy_lock_exec C.jet_elements_legacy_lock_local.
Require C.jets.
Require C.jet_elements_check_lock.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition elements_legacy_value distance (environment : Elements.env) :=
  if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
  then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0.

Lemma elements_legacy_value_range distance environment : 0 <= elements_legacy_value distance environment < 65536.
Proof.
  unfold elements_legacy_value. destruct (2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment)));
    [apply legacy_cache_value_range|lia].
Qed.

Definition elements_legacy_check_spec distance {alg : Primitive.Algebra} : alg Word16 Ty.Unit :=
  elements_assert_spec
    (elements_comp
      (elements_pair (elements_core (fun alg => @DC.iden Word16 alg))
        (elements_comp (elements_core (fun alg => @DC.unit Word16 alg)) (elements_legacy_lock_spec distance)))
      (elements_core (fun alg => @le_word_spec alg 4))).

Lemma elements_legacy_check_value distance (x : Ty.tySem Word16) environment :
  @elements_legacy_check_spec distance (PrimitivePrimSem option_Monad_Zero) x environment =
    if @toZ (WordToZ 4) x <=? elements_legacy_value distance environment then Some tt else None.
Proof.
  unfold elements_legacy_check_spec.
  rewrite elements_assert_sem, elements_comp_sem, elements_pair_sem.
  rewrite (elements_core_sem (fun alg => @DC.iden Word16 alg))
    by (intros alg1 alg2 R; apply Alg.iden_Parametric).
  rewrite elements_comp_sem.
  rewrite (elements_core_sem (fun alg => @DC.unit Word16 alg))
    by (intros alg1 alg2 R; apply Alg.unit_Parametric).
  rewrite elements_legacy_lock_spec_value.
  rewrite (elements_core_sem (fun alg => @le_word_spec alg 4) (le_word_spec_parametric 4)).
  pose proof (le_word_spec_numeric 4 x (@fromZ (WordToZ 4) (elements_legacy_value distance environment))) as Hle.
  rewrite to_fromZ, two_power_nat_equiv, word_bitSize in Hle.
  rewrite Z.mod_small in Hle by apply elements_legacy_value_range.
  fold (elements_legacy_value distance environment).
  change (@DC.iden Word16 Alg.CoreFunSem x) with x. rewrite <- Hle.
  apply jet_elements_check_lock.bit_match_toBool.
Qed.

Definition elements_checked_helper_rest width (fid : ident) : statement :=
  Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar (wide_reader_id width) (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) Tnil) tulong cc_default))
        [Eaddrof (Evar _src (Tstruct _frameItem noattr)) (tptr (Tstruct _frameItem noattr))])
      (Sset _x (Etempvar _t'1 tulong)))
    (Ssequence
      (Ssequence (elements_env_tx_set _t'3)
        (Scall (Some _t'2) (Evar fid (Tfunction
          (Tcons (tptr (Tstruct _elementsTransaction noattr)) Tnil) tulong cc_default))
          [Etempvar _t'3 (tptr (Tstruct _elementsTransaction noattr))]))
      (Sreturn (Some (Ebinop Ole (Etempvar _x tulong) (Etempvar _t'2 tulong) tint)))).

Lemma exec_elements_checked_helper_rest width fid f bl le mc mr be ebase bt base xr r :
  Genv.find_symbol (Clight.genv_genv elements_ge) fid = Some (elements_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block fid) Ptrofs.zero) = Some (Internal f) ->
  type_of_fundef (Internal f) = Tfunction (Tcons (tptr (Tstruct _elementsTransaction noattr)) Tnil) tulong cc_default ->
  (elements_version_locals bl)!fid = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> 0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  Clight2.eval_funcall elements_ge mc (Internal (wide_reader width)) [Vptr bl (Ptrofs.repr 0)] E0 mr (Vlong xr) ->
  Mem.load Mptr mr be ebase = Some (Vptr bt (Ptrofs.repr base)) ->
  Clight2.eval_funcall elements_ge mr (Internal f) [Vptr bt (Ptrofs.repr base)] E0 mr (Vlong r) ->
  exists le1, Clight2.exec_stmt elements_ge (elements_version_locals bl) le mc
    (elements_checked_helper_rest width fid) E0 le1 mr
    (Out_return (Some (Val.of_bool (negb (Int64.ltu r xr)), tint))).
Proof.
  intros Hsym Hfun Hty HEf HEnv HE HEM Hread HL HCall.
  set (l1 := PTree.set _t'1 (Vlong xr) le).
  set (l2 := PTree.set _x (Vlong xr) l1).
  set (l3 := PTree.set _t'3 (Vptr bt (Ptrofs.repr base)) l2).
  set (l4 := PTree.set _t'2 (Vlong r) l3).
  exists l4. unfold elements_checked_helper_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l2).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l1).
    + change l1 with (set_opttemp (Some _t'1) (Vlong xr) le).
      eapply exec_elements_helper_call with (id := wide_reader_id width) (f := wide_reader width)
        (vargs := [Vptr bl Ptrofs.zero]) (vres := Vlong xr).
      * destruct width; unfold elements_core_helpers, wide_reader, wide_reader_id; simpl; tauto.
      * destruct width; reflexivity.
      * eapply eval_Econs; [eapply eval_Eaddrof; apply eval_Evar_local; reflexivity|reflexivity|apply eval_Enil].
      * destruct width; reflexivity.
      * exact Hread.
    + apply exec_set. apply eval_Etempvar. unfold l1. apply PTree.gss.
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l4).
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mr) (le1 := l3).
      * eapply exec_elements_env_tx_set; [|exact HE|exact HEM|exact HL].
        unfold l2, l1. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. exact HEnv.
      * change l4 with (set_opttemp (Some _t'2) (Vlong r) l3).
        eapply exec_Scall with (vf := Vptr (elements_symbol_block fid) Ptrofs.zero)
          (vargs := [Vptr bt (Ptrofs.repr base)]) (f := Internal f).
        -- reflexivity.
        -- eapply eval_Elvalue; [apply eval_Evar_global; [exact HEf|exact Hsym]|apply deref_loc_reference; reflexivity].
        -- eapply eval_Econs; [apply eval_Etempvar; unfold l3; apply PTree.gss|reflexivity|apply eval_Enil].
        -- exact Hfun.
        -- exact Hty.
        -- exact HCall.
    + apply exec_Sreturn_some. eapply eval_Ebinop with (v1 := Vlong xr) (v2 := Vlong r).
      * apply eval_Etempvar. unfold l4, l3. rewrite PTree.gso by discriminate.
        rewrite PTree.gso by discriminate. unfold l2. apply PTree.gss.
      * apply eval_Etempvar. unfold l4. apply PTree.gss.
      * reflexivity.
Qed.

Definition legacy_check_jet (distance : bool) :=
  if distance then f_simplicity_broken_do_not_use_check_lock_distance
  else f_simplicity_broken_do_not_use_check_lock_duration.

Definition elements_legacy_check_rep distance m env environment :=
  exists fp, elements_legacy_lock_env_rep distance m env environment fp.

Lemma legacy_check_shape distance :
  elements_wrapper_shape (legacy_check_jet distance)
    (elements_checked_helper_rest W16 (legacy_lock_id distance)).
Proof.
  destruct distance; repeat split; try reflexivity;
    intros x y HX HY Hxy; cbn in HX, HY;
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
Qed.

Lemma legacy_lock_result_unsigned distance environment ver cached :
  Int64.unsigned ver = Int.unsigned (sigTxVersion (Elements.envTx environment)) ->
  Int64.unsigned cached = legacy_cache_value distance (sigTxIn (Elements.envTx environment)) ->
  Int64.unsigned (legacy_lock_result ver cached) = elements_legacy_value distance environment.
Proof.
  intros HV HC. unfold legacy_lock_result, elements_legacy_value. rewrite legacy_ltu_two, HV.
  destruct (2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))); cbn [negb];
    [exact HC|reflexivity].
Qed.

Theorem elements_legacy_check_local_spec distance :
  application_jet_partial_spec (legacy_check_jet distance) elements_ge Elements.env Word16 Ty.Unit
    (elements_legacy_check_rep distance)
    (fun a e => @elements_legacy_check_spec distance (PrimitivePrimSem option_Monad_Zero) a e).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor rc x
    (fp & be & ebase & bt & base & ver & cached & HEnv & HE & HEM & HB & HBM & HP & HV & HVnum & HC & HCnum & Hfp)
    HSB HSA HRF HR0 HRmax Hin HFrame.
  subst env. pose proof HRF as [HSE HSO].
  apply frame_input_word_at_encode in Hin.
  change (Z.of_nat (bitSize Word16)) with 16 in HRmax.
  set (r := legacy_lock_result ver cached).
  assert (HRU : Int64.unsigned r = elements_legacy_value distance environment)
    by (unfold r; apply legacy_lock_result_unsigned; assumption).
  set (ok := @toZ (WordToZ 4) x <=? elements_legacy_value distance environment).
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HBytes].
  destruct (elements_bool_wrapper (legacy_check_jet distance)
    (elements_checked_helper_rest W16 (legacy_lock_id distance)) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bytes ok (legacy_check_shape distance) HSB HSA HBytes) as (mf & HCall & HMem).
  { intros ma mc bl HA HBa HS.
    destruct (elements_read_wide_step W16 m ma mc bl bs sbase bi edge rc x bytes
      ltac:(change (wide_bits W16) with 16; lia) HRF Hin HA HBa HS)
      as (mr & xr & Hread & Hxr & _ & HMemR & HPermR & _ & HKeep).
    assert (Hok : negb (Int64.ltu r xr) = ok).
    { unfold ok, Int64.ltu. rewrite HRU, Hxr.
      change (@toZ (WordToZ (wide_log W16)) x) with (@toZ (WordToZ 4) x).
      destruct (zlt (elements_legacy_value distance environment) (@toZ (WordToZ 4) x)); symmetry;
        [apply Z.leb_gt|apply Z.leb_le]; cbn [negb]; lia. }
    assert (HLock : Clight2.eval_funcall elements_ge mr (Internal (legacy_lock_helper distance))
      [Vptr bt (Ptrofs.repr base)] E0 mr (Vlong r)).
    { unfold r. rewrite legacy_lock_helper_shape.
      eapply eval_legacy_lock_fn with (delta := legacy_lock_delta distance).
      - destruct distance; [exact legacy_distance_at|exact legacy_duration_at].
      - destruct distance; cbn; lia.
      - destruct distance; cbn; lia.
      - exact HB.
      - exact HBM.
      - exact (HKeep _ _ _ _ HV).
      - exact (HKeep _ _ _ _ HC). }
    destruct (legacy_lock_linkage distance) as [Hsym Hfun].
    destruct (exec_elements_checked_helper_rest W16 (legacy_lock_id distance) (legacy_lock_helper distance)
      bl (elements_wrapper_temps (legacy_check_jet distance) (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc mr be ebase bt base xr r Hsym Hfun
      ltac:(destruct distance; reflexivity) ltac:(destruct distance; reflexivity)
      ltac:(unfold elements_wrapper_temps; apply PTree.gss) HE ltac:(lia) Hread
      (HKeep _ _ _ _ HP) HLock) as [le1 HExec].
    rewrite Hok in HExec. exists le1, mr. split; [exact HExec|]. split; [exact HMemR|exact HPermR]. }
  exists mf. rewrite elements_legacy_check_value. fold ok.
  split; [destruct ok; exact HCall|]. split.
  - destruct ok; [|exact I]. destruct HFrame as (_ & [HDE HDO] & _).
    split; [intros i c Hi; destruct i; discriminate|]. split.
    + intros old HL. exists old. split.
      * rewrite HMem by (eapply load_valid_block; exact HL). exact HL.
      * intros i _ _. reflexivity.
    + change (Z.of_nat (bitSize Ty.Unit)) with 0. rewrite Z.sub_0_r. split.
      * rewrite HMem by (eapply load_valid_block; exact HDE). exact HDE.
      * rewrite HMem by (eapply load_valid_block; exact HDO). exact HDO.
  - intros chunk b ofs Hv _ _. apply HMem. exact Hv.
Qed.

Theorem elements_broken_check_lock_distance_local_spec :
  application_jet_partial_spec f_simplicity_broken_do_not_use_check_lock_distance elements_ge Elements.env Word16 Ty.Unit
    (elements_legacy_check_rep Datatypes.true)
    (fun a e => @elements_legacy_check_spec Datatypes.true (PrimitivePrimSem option_Monad_Zero) a e).
Proof. exact (elements_legacy_check_local_spec Datatypes.true). Qed.

Theorem elements_broken_check_lock_duration_local_spec :
  application_jet_partial_spec f_simplicity_broken_do_not_use_check_lock_duration elements_ge Elements.env Word16 Ty.Unit
    (elements_legacy_check_rep Datatypes.false)
    (fun a e => @elements_legacy_check_spec Datatypes.false (PrimitivePrimSem option_Monad_Zero) a e).
Proof. exact (elements_legacy_check_local_spec Datatypes.false). Qed.
