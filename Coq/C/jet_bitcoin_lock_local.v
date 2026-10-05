(** Actual Bitcoin tx_lock_height / tx_lock_time jets against the literal
    canonical TimeLock programs.
    C: [simplicity_write32(dst, lockHeight(env->tx))] (resp. [lockTime]). *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option Simplicity.Primitive.Bitcoin.
Require Import C.jet_exec C.jet_application_sep C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_spec C.jet_encoding.
Require Import C.jet_wide C.jet_wide_spec C.jet_word_repr.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_fee_local C.jet_bitcoin_is_final_spec C.jet_bitcoin_is_final_local.
Require Import C.jet_bitcoin_lock_exec C.jet_bitcoin_lock_spec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Opaque bitcoin_ge.
Local Transparent Archi.ptr64.
Set Default Timeout 60.

Definition lock_threshold : int64 := Int64.repr 500000000.

Lemma lock_height_cmp_eval m lt le :
  le!_t'5 = Some (Vlong lt) ->
  eval_expr bitcoin_ge empty_env le m (Ecast lock_height_cmp tbool)
    (Vint (bool_int (Int64.ltu lt lock_threshold))).
Proof.
  intro HT. unfold lock_height_cmp.
  eapply eval_Ecast with (v1 := Val.of_bool (Int64.ltu lt lock_threshold)).
  - eapply eval_Ebinop; [apply eval_Etempvar; exact HT|apply eval_Econst_int|reflexivity].
  - destruct (Int64.ltu lt lock_threshold); reflexivity.
Qed.

Lemma lock_time_cmp_eval m lt le :
  le!_t'5 = Some (Vlong lt) ->
  eval_expr bitcoin_ge empty_env le m (Ecast lock_time_cmp tbool)
    (Vint (bool_int (negb (Int64.ltu lt lock_threshold)))).
Proof.
  intro HT. unfold lock_time_cmp.
  eapply eval_Ecast with (v1 := Val.of_bool (negb (Int64.ltu lt lock_threshold))).
  - eapply eval_Ebinop; [apply eval_Econst_int|apply eval_Etempvar; exact HT|reflexivity].
  - destruct (Int64.ltu lt lock_threshold); reflexivity.
Qed.

Lemma bitcoin_lockHeight_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _lockHeight = Some (bitcoin_symbol_block _lockHeight).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_lockHeight_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _lockHeight) Ptrofs.zero) = Some (Internal f_lockHeight).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_lockTime_symbol :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) _lockTime = Some (bitcoin_symbol_block _lockTime).
Proof. vm_compute; reflexivity. Qed.
Lemma bitcoin_lockTime_funct :
  Genv.find_funct (Clight.genv_genv bitcoin_ge)
    (Vptr (bitcoin_symbol_block _lockTime) Ptrofs.zero) = Some (Internal f_lockTime).
Proof. vm_compute; reflexivity. Qed.

Definition lock_fn_type : type :=
  Tfunction (Tcons (tptr (Tstruct _bitcoinTransaction noattr)) Tnil) tulong cc_default.

Definition bitcoin_lock_mid (fid : ident) : statement :=
  Ssequence
    (Ssequence (bitcoin_env_tx_set _t'2)
      (Scall (Some _t'1) (Evar fid lock_fn_type)
        [Etempvar _t'2 (tptr (Tstruct _bitcoinTransaction noattr))]))
    (Scall None
      (Evar _simplicity_write32 (Tfunction
        (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
      [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Etempvar _t'1 tulong]).

Lemma exec_bitcoin_lock_mid fid f e le mc me bd dbase be ebase bt tbase (r : int64) :
  Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid) ->
  Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) =
    Some (Internal f) ->
  type_of_fundef (Internal f) = lock_fn_type ->
  e!fid = None -> e!_simplicity_write32 = None ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  0 <= ebase -> ebase + 8 <= Ptrofs.max_unsigned ->
  Mem.load Mptr mc be ebase = Some (Vptr bt (Ptrofs.repr tbase)) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal f) [Vptr bt (Ptrofs.repr tbase)] E0 mc (Vlong r) ->
  Clight2.eval_funcall bitcoin_ge mc (Internal jets.f_simplicity_write32)
    [Vptr bd (Ptrofs.repr dbase); Vlong r] E0 me Vundef ->
  Clight2.exec_stmt bitcoin_ge e le mc (bitcoin_lock_mid fid) E0
    (PTree.set _t'1 (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le)) me Out_normal.
Proof.
  intros Hsym Hfun Hty HEf HW HEnv HDst He HE0 HL HLock HCall.
  unfold bitcoin_lock_mid.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc)
    (le1 := PTree.set _t'1 (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le)).
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc).
    + eapply exec_bitcoin_env_tx_set; [exact HEnv|exact He|exact HE0|exact HL].
    + change (PTree.set _t'1 (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le))
        with (set_opttemp (Some _t'1) (Vlong r) (PTree.set _t'2 (Vptr bt (Ptrofs.repr tbase)) le)).
      eapply exec_Scall with (vf := Vptr (bitcoin_symbol_block fid) Ptrofs.zero)
        (vargs := [Vptr bt (Ptrofs.repr tbase)]) (f := Internal f).
      * reflexivity.
      * eapply eval_Elvalue.
        -- apply eval_Evar_global; [exact HEf|exact Hsym].
        -- apply deref_loc_reference; reflexivity.
      * eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
      * exact Hfun.
      * exact Hty.
      * exact HLock.
  - refine (exec_bitcoin_helper_call _ _ _ None _simplicity_write32 jets.f_simplicity_write32
      _ _ _ _ _ Vundef _ _ _ _ _ _).
    + unfold bitcoin_core_helpers. simpl. tauto.
    + exact HW.
    + eapply eval_Econs.
      * apply eval_Etempvar. repeat rewrite PTree.gso by discriminate. exact HDst.
      * reflexivity.
      * eapply eval_Econs; [apply eval_Etempvar; apply PTree.gss|reflexivity|apply eval_Enil].
    + reflexivity.
    + exact HCall.
Qed.

Definition bitcoin_lock_env_rep (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt tbase lt,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= tbase /\ tbase + 488 <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be ebase = Some (Vptr bt (Ptrofs.repr tbase)) /\
    Mem.load Mint8unsigned m bt (tbase + 480) =
      Some (Vint (bool_int (forallb sequence_final (sigTxIn (Bitcoin.envTx environment))))) /\
    Mem.load Mint64 m bt (tbase + 472) = Some (Vlong lt) /\
    Int64.unsigned lt = Int.unsigned (sigTxLock (Bitcoin.envTx environment)) /\
    fp = [(be, ebase, ebase + 8); (bt, tbase + 472, tbase + 481)].

Lemma lock_threshold_ltu lt :
  Int64.ltu lt lock_threshold = (Int64.unsigned lt <? 500000000).
Proof.
  unfold Int64.ltu, lock_threshold.
  rewrite Int64.unsigned_repr by (change Int64.max_unsigned with 18446744073709551615; lia).
  destruct (zlt (Int64.unsigned lt) 500000000); symmetry;
    [apply Z.ltb_lt|apply Z.ltb_ge]; lia.
Qed.

Lemma lock_result_value (height final : bool) (lt : int64) (L : Z) :
  Int64.unsigned lt = L -> 0 <= L < 4294967296 ->
  decode_wide W32 (Int64.zero_ext 32
    (lock_result final (if height then Int64.ltu lt lock_threshold
                        else negb (Int64.ltu lt lock_threshold)) lt)) =
    @fromZ (WordToZ 5) (lock_value height final L).
Proof.
  intros HL HR.
  change (@fromZ (WordToZ 5) (Int64.unsigned (Int64.zero_ext 32
    (lock_result final (if height then Int64.ltu lt lock_threshold
                        else negb (Int64.ltu lt lock_threshold)) lt))) =
    @fromZ (WordToZ 5) (lock_value height final L)).
  rewrite Int64.zero_ext_mod by (change (0 <= 32 < 64); lia).
  change (two_p 32) with 4294967296.
  f_equal. unfold lock_result, lock_value. rewrite lock_threshold_ltu, HL.
  destruct final; [reflexivity|].
  destruct (L <? 500000000); destruct height; cbn [negb andb];
    first [reflexivity|rewrite HL; apply Z.mod_small; exact HR].
Qed.

Section LockJet.
Variable height : bool.
Variable jet : function.
Variable fid : ident.
Variable f : function.
Hypothesis Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) fid = Some (bitcoin_symbol_block fid).
Hypothesis Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge)
  (Vptr (bitcoin_symbol_block fid) Ptrofs.zero) = Some (Internal f).
Hypothesis Hshape : bitcoin_wrapper_shape jet (bitcoin_simple_rest (bitcoin_lock_mid fid)).
Hypothesis Hlocal : forall bl, (bitcoin_version_locals bl)!fid = None.
Hypothesis Hexec : forall m bt tbase (b : bool) lt,
  0 <= tbase -> tbase + 488 <= Ptrofs.max_unsigned ->
  Mem.load Mint8unsigned m bt (tbase + 480) = Some (Vint (bool_int b)) ->
  Mem.load Mint64 m bt (tbase + 472) = Some (Vlong lt) ->
  Clight2.eval_funcall bitcoin_ge m (Internal f) [Vptr bt (Ptrofs.repr tbase)] E0 m
    (Vlong (lock_result b (if height then Int64.ltu lt lock_threshold
                           else negb (Int64.ltu lt lock_threshold)) lt)).
Hypothesis Hty : type_of_fundef (Internal f) = lock_fn_type.

Lemma bitcoin_lock_jet_local_spec
    (spec : tySem Ty.Unit -> Bitcoin.env -> option (tySem Word32)) :
  (forall environment, spec tt environment =
    Some (@fromZ (WordToZ 5) (bitcoin_lock_value height environment))) ->
  application_jet_local_spec_sep jet bitcoin_ge Bitcoin.env Ty.Unit Word32 bitcoin_lock_env_rep spec.
Proof.
  intros HSpec environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & tbase & lt & HEnvVal & He0 & HeM & Ht0 & HtM & HLoad & HFin & HLt & HR & HFp)
    HSep HB HA [HSedge HSoff] _ _ _ HFrame.
  subst env fp.
  set (b := forallb sequence_final (sigTxIn (Bitcoin.envTx environment))) in *.
  set (r := lock_result b (if height then Int64.ltu lt lock_threshold
                           else negb (Int64.ltu lt lock_threshold)) lt).
  assert (HC : Z.of_nat (bitSize Word32) = 32) by reflexivity.
  rewrite HC in HFrame.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (cells := encode (decode_wide W32 (Int64.zero_ext 32 r))).
  assert (HMid : forall ma mc bl,
    Mem.alloc m 0 16 = (ma, bl) -> Mem.storebytes ma bl 0 bytes = Some mc ->
    (forall chunk b' ofs v', Mem.load chunk m b' ofs = Some v' -> Mem.load chunk mc b' ofs = Some v') ->
    (forall b' ofs kind p, Mem.perm m b' ofs kind p -> Mem.perm mc b' ofs kind p) ->
    write_frame_at mc bd dbase bw outedge cursor 32 ->
    exists le1 me,
      Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
        (bitcoin_wrapper_temps jet (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase) mc
        (bitcoin_lock_mid fid) E0 le1 me Out_normal /\
      write_effect mc me bd dbase bw outedge cursor 32 cells).
  { intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    destruct (bitcoin_write_wide_step W32 mc bd dbase bw outedge cursor r HFrameC)
      as (me & HCall & HEff).
    eexists _, me. split; [|exact HEff].
    eapply exec_bitcoin_lock_mid with (be := be) (ebase := ebase) (bt := bt) (tbase := tbase)
      (r := r) (f := f).
    - exact Hsym.
    - exact Hfun.
    - exact Hty.
    - apply Hlocal.
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss.
    - lia.
    - lia.
    - exact (HLP _ _ _ _ HLoad).
    - apply Hexec; [lia|lia|exact (HLP _ _ _ _ HFin)|exact (HLP _ _ _ _ HLt)].
    - exact HCall. }
  destruct (bitcoin_wrapper_layout_simple jet
    (bitcoin_lock_mid fid) cells (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor 32 bytes
    Hshape HB HA HBytes ltac:(lia) HFrame
    (fun ma mc bl HAlloc HStore HLP HPP HFrameC =>
      match HMid ma mc bl HAlloc HStore HLP HPP HFrameC with
      | ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF (conj HL (conj HPm HV))))))) =>
          ex_intro _ le1 (ex_intro _ me (conj HEx (conj HC' (conj HP (conj HF
            (conj (fun chunk b' ofs _ H1 H2 => HL chunk b' ofs H1 H2) (conj HPm HV)))))))
      end))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (@fromZ (WordToZ 5) (bitcoin_lock_value height environment)).
  split; [apply HSpec|]. split; [exact HCall|].
  split.
  { unfold cells, r in HCells.
    rewrite (lock_result_value height b lt _ HR
      (Int.unsigned_range (sigTxLock (Bitcoin.envTx environment)))) in HCells.
    exact HCells. }
  split; [exact HPrefix|]. split; [exact HFields|]. exact HMem.
Qed.
End LockJet.

Ltac wrapper_shape :=
  repeat split; try reflexivity;
  intros x y HX HY Hxy; cbn in HX, HY;
  repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
    first [contradiction | vm_compute in Hxy; discriminate | congruence].

Lemma bitcoin_tx_lock_height_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tx_lock_height
    (bitcoin_simple_rest (bitcoin_lock_mid _lockHeight)).
Proof. wrapper_shape. Qed.
Lemma bitcoin_tx_lock_time_body :
  bitcoin_wrapper_shape f_simplicity_bitcoin_tx_lock_time
    (bitcoin_simple_rest (bitcoin_lock_mid _lockTime)).
Proof. wrapper_shape. Qed.

Theorem bitcoin_tx_lock_height_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tx_lock_height bitcoin_ge Bitcoin.env
    Ty.Unit Word32 bitcoin_lock_env_rep
    (fun a environment => @bitcoin_tx_lock_height_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_lock_jet_local_spec Datatypes.true) with (fid := _lockHeight) (f := f_lockHeight).
  - exact bitcoin_lockHeight_symbol.
  - exact bitcoin_lockHeight_funct.
  - exact bitcoin_tx_lock_height_body.
  - intro bl. reflexivity.
  - intros m bt tbase b lt H0 HM HB HL. rewrite f_lockHeight_shape.
    apply eval_lock_fn; [exact H0|exact HM|exact HB|exact HL|].
    intros le Hle. apply lock_height_cmp_eval. exact Hle.
  - reflexivity.
  - intro environment. exact (bitcoin_lock_program_value Datatypes.true environment).
Qed.

Theorem bitcoin_tx_lock_time_local_spec :
  application_jet_local_spec_sep f_simplicity_bitcoin_tx_lock_time bitcoin_ge Bitcoin.env
    Ty.Unit Word32 bitcoin_lock_env_rep
    (fun a environment => @bitcoin_tx_lock_time_spec (PrimitivePrimSem option_Monad_Zero) a environment).
Proof.
  eapply (bitcoin_lock_jet_local_spec Datatypes.false) with (fid := _lockTime) (f := f_lockTime).
  - exact bitcoin_lockTime_symbol.
  - exact bitcoin_lockTime_funct.
  - exact bitcoin_tx_lock_time_body.
  - intro bl. reflexivity.
  - intros m bt tbase b lt H0 HM HB HL. rewrite f_lockTime_shape.
    apply eval_lock_fn; [exact H0|exact HM|exact HB|exact HL|].
    intros le Hle. apply lock_time_cmp_eval. exact Hle.
  - reflexivity.
  - intro environment. exact (bitcoin_lock_program_value Datatypes.false environment).
Qed.
