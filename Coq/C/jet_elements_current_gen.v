(** Generic proof of the Elements "current input" jets over an arbitrary tail:
      [if (numInputs <= ix) return false; TAIL]   (TAIL ends in [return true])
    with the statement forms the bodies are built from (reload of
    [env->tx], the array pointer and [env->ix]; a pointer-taking helper
    call).  Adapted from the single-helper theorem of
    [jet_elements_current_ptr_jets]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Digest Simplicity.Translate Simplicity.BitMachine.
Require Import Simplicity.Util.Option C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_wide C.jet_wide_spec.
Require Import C.jet_encoding C.jet_input_layout C.jet_uint32_array_init C.jets_elements C.jet_elements_linkage C.jet_exec.
Require C.jets.
Require Import C.jet_elements_version_exec C.jet_elements_field_eval C.jet_elements_wrapper C.jet_elements_effects.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_index_eval C.jet_elements_indexed_exec.
Require Import C.jet_elements_current_exec C.jet_elements_current_spec C.jet_elements_current_ptr.
Require Import C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr C.jet_elements_hash_write C.jet_elements_hash_helpers.
Require Import C.jet_elements_script_cmr_local C.jet_elements_indexed_scalar_jets C.jet_elements_indexed_ptr_jets.
Require Import C.jet_elements_current_ptr_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.


Definition elements_current_guard (ta tb tc countfield : ident) : statement :=
  Ssequence (Sset ta elements_env_tx_expr)
    (Ssequence
      (Sset tb (Efield (Ederef (Etempvar ta (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) countfield tulong))
      (Ssequence (Sset tc elements_env_ix_expr)
        (Sifthenelse (Ebinop Ole (Etempvar tb tulong) (Etempvar tc tulong) tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint))) Sskip))).

Definition elements_current_gen_rest (ta tb tc countfield : ident) (tail : statement) : statement :=
  Ssequence (elements_current_guard ta tb tc countfield) tail.

Definition elements_return_one : statement := Sreturn (Some (Econst_int (Int.repr 1) tint)).

Lemma exec_elements_return_one e le m :
  Clight2.exec_stmt elements_ge e le m elements_return_one E0 le m elements_returned_one.
Proof. apply exec_Sreturn_some, eval_Econst_int. Qed.

(** [t1 = env->tx; t2 = t1->ARRAY; t3 = env->ix; S] *)
Definition elements_current_load3 (t1 t2 t3 arrfield sid : ident) (s : statement) : statement :=
  Ssequence (Sset t1 elements_env_tx_expr)
    (Ssequence
      (Sset t2 (Efield (Ederef (Etempvar t1 (tptr (Tstruct _elementsTransaction noattr)))
        (Tstruct _elementsTransaction noattr)) arrfield (tptr (Tstruct sid noattr))))
      (Ssequence (Sset t3 elements_env_ix_expr) s)).

Definition elements_ptr_call (cid : ident) (pt : type) (pexpr : expr) : statement :=
  Scall None
    (Evar cid (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); pexpr].

Lemma exec_elements_current_guard e le0 ta tb tc countfield cdelta mc be ebase bt txbase nI ixv :
  ta <> _env -> tb <> _env -> tc <> tb ->
  le0!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= cdelta -> txbase + cdelta + 8 <= Ptrofs.max_unsigned ->
  elements_field_at _elementsTransaction countfield cdelta ->
  Mem.load Mptr mc be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mint64 mc bt (txbase + cdelta) = Some (Vlong nI) ->
  Mem.load Mint64 mc be (ebase + 80) = Some (Vlong ixv) ->
  Int64.ltu ixv nI = true ->
  Clight2.exec_stmt elements_ge e le0 mc (elements_current_guard ta tb tc countfield) E0
    (PTree.set tc (Vlong ixv) (PTree.set tb (Vlong nI) (PTree.set ta (Vptr bt (Ptrofs.repr txbase)) le0)))
    mc Out_normal.
Proof.
  intros Ha Hb Hcb HEnv He0 He1 Ht0 Hc0 HcM HFc Hl_tx Hl_cnt Hl_ix Hlt.
  set (la_a := PTree.set ta (Vptr bt (Ptrofs.repr txbase)) le0).
  set (la_b := PTree.set tb (Vlong nI) la_a).
  set (la_c := PTree.set tc (Vlong ixv) la_b).
  assert (HEa : la_a!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la_a; gsoc2; exact HEnv).
  assert (HEb : la_b!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold la_b; gsoc2; exact HEa).
  unfold elements_current_guard.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_a).
  - apply exec_set. eapply eval_elements_env_tx_expr; [exact HEnv|exact He0|lia|exact Hl_tx].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_b).
    + apply exec_set.
      eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := cdelta) (chunk := Mint64).
      * reflexivity.
      * exact HFc.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold la_a. apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hl_cnt].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := la_c).
      * apply exec_set. eapply eval_elements_env_ix; [exact HEb|exact He0|exact He1|exact Hl_ix].
      * eapply exec_Sifthenelse with (v1 := Vint Int.zero) (b := false).
        -- eapply eval_Ebinop with (v1 := Vlong nI) (v2 := Vlong ixv).
           ++ apply eval_Etempvar. unfold la_c. gsoc2. apply PTree.gss.
           ++ apply eval_Etempvar. unfold la_c. apply PTree.gss.
           ++ change (Some (Val.of_bool (negb (Int64.ltu ixv nI))) = Some (Vint Int.zero)).
              rewrite Hlt. reflexivity.
        -- reflexivity.
        -- apply exec_Sskip.
Qed.

Lemma exec_elements_current_load3 e le t1 t2 t3 arrfield adelta sid s m le' m' out
    be ebase bt txbase bin inbase ixv :
  t1 <> _env -> t2 <> _env ->
  le!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
  0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
  0 <= txbase -> 0 <= adelta -> txbase + adelta + 8 <= Ptrofs.max_unsigned ->
  elements_field_at _elementsTransaction arrfield adelta ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m be (ebase + 80) = Some (Vlong ixv) ->
  Clight2.exec_stmt elements_ge e
    (PTree.set t3 (Vlong ixv) (PTree.set t2 (Vptr bin (Ptrofs.repr inbase))
      (PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) le))) m s E0 le' m' out ->
  Clight2.exec_stmt elements_ge e le m (elements_current_load3 t1 t2 t3 arrfield sid s) E0 le' m' out.
Proof.
  intros H1 H2 HEnv He0 He1 Ht0 Ha0 HaM HFa Hl_tx Hl_arr Hl_ix HS.
  set (lb1 := PTree.set t1 (Vptr bt (Ptrofs.repr txbase)) le) in *.
  set (lb2 := PTree.set t2 (Vptr bin (Ptrofs.repr inbase)) lb1) in *.
  assert (HE1 : lb1!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold lb1; gsoc2; exact HEnv).
  assert (HE2 : lb2!_env = Some (Vptr be (Ptrofs.repr ebase))) by (unfold lb2; gsoc2; exact HE1).
  unfold elements_current_load3.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := lb1).
  - apply exec_set. eapply eval_elements_env_tx_expr; [exact HEnv|exact He0|lia|exact Hl_tx].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := lb2).
    + apply exec_set.
      eapply eval_elements_field_value with (sid := _elementsTransaction) (delta := adelta) (chunk := Mptr).
      * reflexivity.
      * exact HFa.
      * reflexivity.
      * apply eval_elements_deref_struct. unfold lb1. apply PTree.gss.
      * rewrite elements_ptr_add_repr by lia. apply elements_loadv_repr; [lia|exact Hl_arr].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := m) (le1 := PTree.set t3 (Vlong ixv) lb2).
      * apply exec_set. eapply eval_elements_env_ix; [exact HE2|exact He0|exact He1|exact Hl_ix].
      * exact HS.
Qed.

Lemma exec_elements_ptr_call e le m cid pt cf pexpr pofs bd dbase bin me :
  typeof pexpr = tptr pt -> e!cid = None ->
  Genv.find_symbol (Clight.genv_genv elements_ge) cid = Some (elements_symbol_block cid) ->
  Genv.find_funct (Clight.genv_genv elements_ge) (Vptr (elements_symbol_block cid) Ptrofs.zero) = Some (Internal cf) ->
  type_of_fundef (Internal cf) =
    Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default ->
  le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  eval_expr elements_ge e le m pexpr (Vptr bin (Ptrofs.repr pofs)) ->
  Clight2.eval_funcall elements_ge m (Internal cf)
    [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)] E0 me Vundef ->
  Clight2.exec_stmt elements_ge e le m (elements_ptr_call cid pt pexpr) E0 le me Out_normal.
Proof.
  intros Hpty He Hsym Hfun Hty HDst Hptr Hcall. unfold elements_ptr_call.
  change le with (set_opttemp None Vundef le) at 2.
  eapply exec_Scall with (vf := Vptr (elements_symbol_block cid) Ptrofs.zero) (f := Internal cf)
    (vargs := [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr pofs)]) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue; [apply eval_Evar_global; [exact He|exact Hsym]|apply deref_loc_reference; reflexivity].
  - eapply eval_Econs; [apply eval_Etempvar; exact HDst|reflexivity|].
    eapply eval_Econs; [exact Hptr|rewrite Hpty; reflexivity|apply eval_Enil].
  - exact Hfun.
  - exact Hty.
  - exact Hcall.
Qed.

(** The environment words re-read between output writes belong to the
    footprint, with the whole array of elements. *)
Definition current_gen_rep {A} (elems_of : Elements.env -> list A)
    (elemrep : mem -> block -> Z -> A -> Prop)
    (sz adelta cdelta : Z) (m : mem) (env : val) (environment : Elements.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI ixv,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 88 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 760 <= Ptrofs.max_unsigned /\
    0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
    Mem.load Mint64 m be (ebase + 80) = Some (Vlong ixv) /\
    Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
    Int64.unsigned ixv = Z.of_nat (Elements.envIx environment) /\
    (forall j x, nth_error (elems_of environment) j = Some x ->
      elemrep m bin (inbase + sz * Z.of_nat j) x) /\
    fp = [(be, ebase, ebase + 8); (be, ebase + 80, ebase + 88);
          (bt, txbase + adelta, txbase + adelta + 8);
          (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))].

Theorem elements_current_gen_local {A} (elems_of : Elements.env -> list A) (nbits : Z)
    (pcells : A -> list Cell) (elemrep : mem -> block -> Z -> A -> Prop) (Bpay : Ty)
    (ta tb tc countfield : ident) (cdelta adelta sz : Z) (body : statement) (f : function)
    (Ha : ta <> _env) (Hb : tb <> _env) (Hc : tc <> _env)
    (Had : ta <> _dst) (Hbd : tb <> _dst) (Hcd : tc <> _dst) (Hcb : tc <> tb)
    (Hnb : 1 <= nbits <= 1000)
    (Hcf : elements_field_at _elementsTransaction countfield cdelta)
    (Hcb' : 0 <= cdelta /\ cdelta + 8 <= 760) (Hab : 0 <= adelta /\ adelta + 8 <= 760)
    (Hsz : 0 < sz <= 1000)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + sz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    (Hbody : forall bd dbase bw outedge bl le mc x be ebase bt txbase bin inbase ixv cur,
      le!_env = Some (Vptr be (Ptrofs.repr ebase)) -> le!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
      0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
      0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
      0 <= inbase -> inbase + sz * Int64.unsigned ixv + sz <= Ptrofs.max_unsigned ->
      Mem.load Mptr mc be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
      Mem.load Mptr mc bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
      Mem.load Mint64 mc be (ebase + 80) = Some (Vlong ixv) ->
      elemrep mc bin (inbase + sz * Int64.unsigned ixv) x ->
      out_sep bd dbase bw outedge cur nbits be ebase (ebase + 8) ->
      out_sep bd dbase bw outedge cur nbits be (ebase + 80) (ebase + 88) ->
      out_sep bd dbase bw outedge cur nbits bt (txbase + adelta) (txbase + adelta + 8) ->
      out_sep bd dbase bw outedge cur nbits bin (inbase + sz * Int64.unsigned ixv)
        (inbase + sz * Int64.unsigned ixv + sz) ->
      write_frame_at mc bd dbase bw outedge cur nbits ->
      exists le' me,
        Clight2.exec_stmt elements_ge (elements_version_locals bl) le mc body E0 le' me elements_returned_one /\
        write_effect mc me bd dbase bw outedge cur nbits (pcells x))
    (Hshape : elements_wrapper_shape f (elements_current_gen_rest ta tb tc countfield body))
    (HB : Z.of_nat (bitSize Bpay) = nbits)
    (spec : Ty.tySem Ty.Unit -> Elements.env -> option (Ty.tySem Bpay))
    (Hsem : forall environment, exists x V,
      nth_error (elems_of environment) (Elements.envIx environment) = Some x /\
      spec tt environment = Some V /\ encode V = pcells x) :
  application_jet_local_spec_sep f elements_ge Elements.env Ty.Unit Bpay
    (current_gen_rep elems_of elemrep sz adelta cdelta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor [] fp
    (be & ebase & bt & txbase & bin & inbase & nI & ixv & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLarr & HLcnt & HLix & HnI & Hixv & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  pose proof Hnb as Hwb.
  rewrite HB in HSep, HFrame.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor nbits be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; tauto)).
  assert (S2 : out_sep bd dbase bw outedge cursor nbits be (ebase + 80) (ebase + 88))
    by exact (HSep (be, ebase + 80, ebase + 88) ltac:(simpl; tauto)).
  assert (S4 : out_sep bd dbase bw outedge cursor nbits bt (txbase + adelta) (txbase + adelta + 8))
    by exact (HSep (bt, txbase + adelta, txbase + adelta + 8) ltac:(simpl; tauto)).
  assert (S5 : out_sep bd dbase bw outedge cursor nbits bin inbase
    (inbase + sz * Z.of_nat (length (elems_of environment))))
    by exact (HSep (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment))) ltac:(simpl; tauto)).
  destruct (Hsem environment) as (x & V & Hnth & HVs & HVenc).
  assert (Hix_lt : (Elements.envIx environment < length (elems_of environment))%nat)
    by (apply nth_error_Some; rewrite Hnth; discriminate).
  assert (Hlt : Int64.ltu ixv nI = true).
  { unfold Int64.ltu. rewrite zlt_true; [reflexivity|]. rewrite Hixv, HnI. lia. }
  set (nn := Z.of_nat (length (elems_of environment))) in *.
  set (szn := sz * nn) in *.
  assert (Hm : sz * Int64.unsigned ixv + sz <= szn).
  { subst szn. rewrite Hixv. assert (sz * (Z.of_nat (Elements.envIx environment) + 1) <= sz * nn)
      by (apply Z.mul_le_mono_nonneg_l; subst nn; lia). lia. }
  assert (Hs0 : 0 <= sz * Int64.unsigned ixv) by (apply Z.mul_nonneg_nonneg; [lia|apply Int64.unsigned_range]).
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  set (ofs := inbase + sz * Int64.unsigned ixv).
  assert (Hrep : elemrep m bin ofs x).
  { pose proof (HLelem _ x Hnth) as H. rewrite <- Hixv in H. exact H. }
  assert (HMid : elements_wrapper_mid f (elements_current_gen_rest ta tb tc countfield body)
    (pcells x) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor nbits bytes).
  { unfold elements_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    assert (Hrepc : elemrep mc bin ofs x).
    { eapply Hpres; [exact Hrep|]. intros chunk o v Hlo Hhi Hl. exact (HLP _ _ _ _ Hl). }
    assert (HSp : out_sep bd dbase bw outedge cursor nbits bin ofs (ofs + sz)).
    { eapply out_sep_range with (lo := inbase) (hi := inbase + szn); [exact S5|slia|slia]. }
    set (le0 := elements_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase).
    assert (HEnv0 : le0!_env = Some (Vptr be (Ptrofs.repr ebase)))
      by (unfold le0, elements_wrapper_temps; apply PTree.gss).
    assert (HDst0 : le0!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold le0, elements_wrapper_temps. rewrite PTree.gso by discriminate.
      rewrite PTree.gso by discriminate. apply PTree.gss. }
    pose proof (exec_elements_current_guard (elements_version_locals bl) le0 ta tb tc countfield cdelta mc
      be ebase bt txbase nI ixv Ha Hb Hcb HEnv0 He0 He1 Ht0 (proj1 Hcb') ltac:(slia) Hcf
      (HLP _ _ _ _ HLtx) (HLP _ _ _ _ HLcnt) (HLP _ _ _ _ HLix) Hlt) as HG.
    set (leg := PTree.set tc (Vlong ixv) (PTree.set tb (Vlong nI)
      (PTree.set ta (Vptr bt (Ptrofs.repr txbase)) le0))) in *.
    assert (HEg : leg!_env = Some (Vptr be (Ptrofs.repr ebase))).
    { unfold leg. gsoc2. gsoc2. gsoc2. exact HEnv0. }
    assert (HDg : leg!_dst = Some (Vptr bd (Ptrofs.repr dbase))).
    { unfold leg. gsoc2. gsoc2. gsoc2. exact HDst0. }
    destruct (Hbody bd dbase bw outedge bl leg mc x be ebase bt txbase bin inbase ixv cursor
      HEg HDg He0 He1 Ht0 Ht1 Hi0 ltac:(slia)
      (HLP _ _ _ _ HLtx) (HLP _ _ _ _ HLarr) (HLP _ _ _ _ HLix) Hrepc S1 S2 S4 HSp HFrameC)
      as (le1 & me & HEx & E).
    destruct E as (c & p & fl & l & pm & vv).
    exists le1, me.
    refine (conj _ (conj c (conj p (conj fl (conj _ (conj pm vv)))))).
    - unfold elements_current_gen_rest.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := leg); [exact HG|exact HEx].
    - intros chunk b ofs' _ H1' H2'. exact (l chunk b ofs' H1' H2'). }
  destruct (elements_wrapper_layout f (elements_current_gen_rest ta tb tc countfield body)
    (pcells x) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs sbase bw outedge cursor nbits bytes
    Hshape HBf HA HBytes ltac:(slia) HFrame HMid)
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, V. split; [exact HVs|].
  split; [exact HCall|]. split; [rewrite HVenc; exact HCells|]. split; [exact HPrefix|].
  rewrite HB. split; [exact HFields|]. exact HMem.
Qed.
