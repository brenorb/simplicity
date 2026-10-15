(** Whole original C legacy Elements lock getters, including entry, by-value
    frame copy, helper call, write16, return, free and memory observations.
    The relation describes the initial cached maximum in the transaction;
    establishing that cache from env.c is a separate caller obligation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Maps Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine Simplicity.Util.Option.
Require Import C.jet_exec C.jet_frame_copy_layout C.jet_frame_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_application_sep C.jet_encoding C.jet_wide C.jet_wide_spec C.jet_word_repr C.jet_bitmachine_rep.
Require Import C.jet_elements_prim C.jets_elements C.jet_elements_linkage C.jet_elements_version_exec.
Require Import C.jet_elements_wrapper C.jet_elements_effects C.jet_elements_steps.
Require Import C.jet_elements_legacy_lock_spec C.jet_elements_legacy_lock_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque elements_ge.
Set Default Timeout 10.

Definition legacy_lock_id (distance : bool) := if distance then _obsolete_lockDistance else _obsolete_lockDuration.
Definition legacy_lock_field (distance : bool) := if distance then _obsolete_lockDistance else _obsolete_lockDuration.
Definition legacy_lock_delta (distance : bool) := if distance then 736 else 744.
Definition legacy_lock_helper (distance : bool) := if distance then f_obsolete_lockDistance else f_obsolete_lockDuration.
Definition legacy_lock_jet (distance : bool) := if distance then f_simplicity_broken_do_not_use_tx_lock_distance
                                     else f_simplicity_broken_do_not_use_tx_lock_duration.

Lemma legacy_lock_helper_shape distance :
  legacy_lock_helper distance = legacy_lock_fn (legacy_lock_field distance).
Proof. destruct distance; reflexivity. Qed.

Lemma legacy_lock_linkage distance :
  Genv.find_symbol (Clight.genv_genv elements_ge) (legacy_lock_id distance) =
    Some (elements_symbol_block (legacy_lock_id distance)) /\
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block (legacy_lock_id distance)) Ptrofs.zero) =
    Some (Internal (legacy_lock_helper distance)).
Proof. destruct distance; split; vm_compute; reflexivity. Qed.

Lemma legacy_lock_wrapper_shape distance :
  elements_wrapper_shape (legacy_lock_jet distance)
    (elements_simple_rest (elements_helper_write_mid W16 (legacy_lock_id distance))).
Proof.
  destruct distance; repeat split; try reflexivity;
    intros x y HX HY Hxy; cbn in HX, HY;
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
Qed.

Definition elements_legacy_lock_env_rep distance (m : mem) (env : val) (environment : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt base ver cached,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= base /\ base + 760 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr base)) /\
    Mem.load Mint64 m bt (base + 720) = Some (Vlong ver) /\
    Int64.unsigned ver = Int.unsigned (sigTxVersion (Elements.envTx environment)) /\
    Mem.load Mint64 m bt (base + legacy_lock_delta distance) = Some (Vlong cached) /\
    Int64.unsigned cached = legacy_cache_value distance (sigTxIn (Elements.envTx environment)) /\
    fp = [(be, ebase, ebase + 8); (bt, base + 720, base + 752)].

Lemma legacy_ltu_two ver : Int64.ltu ver (Int64.repr 2) = negb (2 <=? Int64.unsigned ver).
Proof.
  unfold Int64.ltu. change (Int64.unsigned (Int64.repr 2)) with 2.
  destruct (zlt (Int64.unsigned ver) 2) as [HL|HL];
    destruct (2 <=? Int64.unsigned ver) eqn:HC; cbn;
    try reflexivity; [apply Z.leb_le in HC|apply Z.leb_gt in HC]; lia.
Qed.

Lemma legacy_lock_decode_result distance environment ver cached :
  Int64.unsigned ver = Int.unsigned (sigTxVersion (Elements.envTx environment)) ->
  Int64.unsigned cached = legacy_cache_value distance (sigTxIn (Elements.envTx environment)) ->
  decode_wide W16 (Int64.zero_ext 16 (legacy_lock_result ver cached)) =
    @fromZ (WordToZ 4) (if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
      then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0).
Proof.
  intros HV HC.
  change (@fromZ (WordToZ 4) (Int64.unsigned (Int64.zero_ext 16 (legacy_lock_result ver cached))) =
    @fromZ (WordToZ 4) (if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
      then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0)).
  rewrite Int64.zero_ext_mod by (change (0 <= 16 < 64); lia).
  change (two_p 16) with 65536. unfold legacy_lock_result. rewrite legacy_ltu_two, HV.
  destruct (2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))); cbn [negb].
  - rewrite HC, Z.mod_small by apply legacy_cache_value_range. reflexivity.
  - reflexivity.
Qed.

Theorem elements_legacy_lock_local_spec distance :
  application_jet_local_spec_sep (legacy_lock_jet distance) elements_ge Elements.env Ty.Unit Word16
    (elements_legacy_lock_env_rep distance)
    (fun a environment => @elements_legacy_lock_spec distance (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor rc [] fp
    (be & ebase & bt & base & ver & cached & HEnv & HE & HEM & HB & HBM & HP & HV & HVnum & HC & HCnum & Hfp)
    HSep HSB HSA [HSE HSO] _ _ _ HF.
  subst env fp. change (write_frame_at m bd dbase bw outedge cursor 16) in HF.
  destruct (frame_loadbytes_at m bs sbase _ _ HSE HSO) as [bytes HBytes].
  set (r := legacy_lock_result ver cached).
  set (cells := encode (decode_wide W16 (Int64.zero_ext 16 r))).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b ofs v, Mem.load chunk m b ofs = Some v -> Mem.load chunk mc b ofs = Some v) ->
    (forall b ofs kind p, Mem.perm m b ofs kind p -> Mem.perm mc b ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 16 ->
    exists le1 me,
      Clight2.exec_stmt elements_ge (elements_version_locals bl)
        (elements_wrapper_temps (legacy_lock_jet distance) (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        (elements_helper_write_mid W16 (legacy_lock_id distance)) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 16 cells).
  { intros ma mc bl HA HS HLP HPP HFC.
    destruct (elements_write_wide_step W16 mc bd dbase bw outedge cursor r HFC) as (me & HWrite & HEff).
    eexists _, me. split; [|exact HEff].
    destruct (legacy_lock_linkage distance) as [Hsym Hfun].
    eapply exec_elements_helper_write_mid with (f := legacy_lock_helper distance)
      (be := be) (ebase := ebase) (bt := bt) (tbase := base) (r := r).
    - exact Hsym.
    - exact Hfun.
    - destruct distance; reflexivity.
    - destruct distance; reflexivity.
    - reflexivity.
    - unfold elements_wrapper_temps. apply PTree.gss.
    - unfold elements_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - exact (HLP _ _ _ _ HP).
    - unfold r. rewrite legacy_lock_helper_shape.
      eapply eval_legacy_lock_fn with (delta := legacy_lock_delta distance).
      + destruct distance; [exact legacy_distance_at|exact legacy_duration_at].
      + destruct distance; cbn; lia.
      + destruct distance; cbn; lia.
      + exact HB.
      + exact HBM.
      + exact (HLP _ _ _ _ HV).
      + exact (HLP _ _ _ _ HC).
    - exact HWrite. }
  destruct (elements_wrapper_layout_simple (legacy_lock_jet distance)
    (elements_helper_write_mid W16 (legacy_lock_id distance)) cells (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bw outedge cursor 16 bytes (legacy_lock_wrapper_shape distance)
    HSB HSA HBytes ltac:(lia) HF
    (fun ma mc bl HA HS HLP HPP HFC =>
      match HMid ma mc bl HA HS HLP HPP HFC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HO (conj HPre (conj HFields (conj HLoads (conj HPerm HValid))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HO (conj HPre (conj HFields
            (conj (fun chunk b ofs _ H1 H2 => HLoads chunk b ofs H1 H2) (conj HPerm HValid)))))))
      end)) as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (@fromZ (WordToZ 4) (if 2 <=? Int.unsigned (sigTxVersion (Elements.envTx environment))
    then legacy_cache_value distance (sigTxIn (Elements.envTx environment)) else 0)).
  split; [apply elements_legacy_lock_spec_value|]. split; [exact HCall|].
  split.
  - unfold cells, r in HCells. rewrite (legacy_lock_decode_result distance environment ver cached HVnum HCnum) in HCells.
    exact HCells.
  - split; [exact HPrefix|]. split; [exact HFields|exact HMem].
Qed.

Theorem elements_broken_tx_lock_distance_local_spec :
  application_jet_local_spec_sep f_simplicity_broken_do_not_use_tx_lock_distance elements_ge Elements.env Ty.Unit Word16
    (elements_legacy_lock_env_rep Datatypes.true)
    (fun a e => @elements_legacy_lock_spec Datatypes.true (PrimitivePrimSem option_Monad_Zero) a e).
Proof. exact (elements_legacy_lock_local_spec Datatypes.true). Qed.

Theorem elements_broken_tx_lock_duration_local_spec :
  application_jet_local_spec_sep f_simplicity_broken_do_not_use_tx_lock_duration elements_ge Elements.env Ty.Unit Word16
    (elements_legacy_lock_env_rep Datatypes.false)
    (fun a e => @elements_legacy_lock_spec Datatypes.false (PrimitivePrimSem option_Monad_Zero) a e).
Proof. exact (elements_legacy_lock_local_spec Datatypes.false). Qed.
