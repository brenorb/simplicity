(** Full original-C public contract of [simplicity_fe_multiply] against the
    literal canonical [fe_multiply] ([mul256 >>> fe_normalize512]): actual
    entry, three local allocations, source copy, two readers, in-place
    multiplication ([r = a]), wide writer, return and freeing. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Values Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_exec C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout.
Require Import C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp.
Require Import C.jet_sx_exec C.jet_secp_fns C.jet_secp_wrapper_run.
Require Import C.jet_secp_public_copy C.jet_secp_public_body C.jet_secp_normalize_local.
Require Import C.jet_secp_add_body C.jet_secp_add_entry C.jet_secp_add_prepare.
Require Import C.jet_secp_canonical_negate C.jet_secp_negate_literal_contract C.jet_parallel_fe_mul_calls.
Import Clightdefs ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 20.
Local Opaque literal_fe_multiply encode.

(** ** Statement shape *)
Definition secp_public_mul_stmt : statement :=
  Scall None
    (Evar jets_secp._secp256k1_fe_mul (Tfunction
      (Tcons (tptr secp_field_type) (Tcons (tptr secp_field_type)
        (Tcons (tptr secp_field_type) Tnil))) tvoid cc_default))
    [Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._a secp_field_type) (tptr secp_field_type);
     Eaddrof (Evar jets_secp._b secp_field_type) (tptr secp_field_type)].
Definition secp_fe_mul_rest : statement :=
  Ssequence (secp_read_field_stmt jets_secp._a)
    (Ssequence (secp_read_field_stmt jets_secp._b)
      (Ssequence secp_public_mul_stmt
        (Ssequence secp_public_write_stmt
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))))).
Lemma secp_fe_mul_body :
  fn_body f_simplicity_fe_multiply =
    Ssequence (Sassign (Evar jets_secp._src secp_frame_type)
      (Etempvar jets_secp._src secp_frame_type)) secp_fe_mul_rest.
Proof. reflexivity. Qed.
Lemma secp_mul_helper_symbols :
  Genv.find_symbol secp_ge jets_secp._secp256k1_fe_mul =
    Some (secp_symbol_block jets_secp._secp256k1_fe_mul) /\
  Genv.find_funct secp_ge
    (Vptr (secp_symbol_block jets_secp._secp256k1_fe_mul) Ptrofs.zero) =
    Some (Internal f_secp256k1_fe_mul).
Proof. vm_compute; split; reflexivity. Qed.

Lemma exec_secp_mul_fields le m mf bl ba bb :
  Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_mul)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_add_env bl ba bb) le m
    secp_public_mul_stmt E0 le mf Out_normal.
Proof.
  intro HCall; destruct secp_mul_helper_symbols as [HS HF].
  eapply ClightBigstep.exec_Scall with
    (vf := Vptr (secp_symbol_block jets_secp._secp256k1_fe_mul) Ptrofs.zero)
    (vargs := [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero])
    (f := Internal f_secp256k1_fe_mul) (vres := Vundef).
  - reflexivity.
  - eapply eval_Elvalue.
    + eapply eval_Evar_global; [reflexivity|exact HS].
    + apply deref_loc_reference; reflexivity.
  - eapply eval_Econs.
    + apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
    + reflexivity.
    + eapply eval_Econs.
      * apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
      * reflexivity.
      * eapply eval_Econs.
        -- apply eval_Eaddrof; apply eval_Evar_local; reflexivity.
        -- reflexivity.
        -- apply eval_Enil.
  - exact HF.
  - reflexivity.
  - exact HCall.
Qed.

Lemma exec_secp_mul_rest_calls le m ma mb mn mf bl ba bb bd dbase :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  Clight2.eval_funcall secp_ge m (Internal f_read_fe)
    [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef ->
  Clight2.eval_funcall secp_ge ma (Internal f_read_fe)
    [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mb Vundef ->
  Clight2.eval_funcall secp_ge mb (Internal f_secp256k1_fe_mul)
    [Vptr ba Ptrofs.zero; Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mn Vundef ->
  Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
    [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef ->
  Clight2.exec_stmt secp_ge (secp_public_add_env bl ba bb) le m secp_fe_mul_rest E0 le mf
    (Out_return (Some (Vint Int.one, tint))).
Proof.
  intros HDst HA HB HMul HWrite. unfold secp_fe_mul_rest.
  eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ma) (le1 := le).
  - eapply exec_secp_read_field; [reflexivity|reflexivity|reflexivity|exact HA].
  - eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mb) (le1 := le).
    + eapply exec_secp_read_field; [reflexivity|reflexivity|reflexivity|exact HB].
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mn) (le1 := le).
      * apply exec_secp_mul_fields; exact HMul.
      * eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mf) (le1 := le).
        -- eapply exec_secp_write_field; [reflexivity|reflexivity|exact HDst|exact HWrite].
        -- apply exec_Sreturn_some; constructor.
Qed.

(** ** Entry *)
Definition secp_mul_temps (v_env : val) bd dbase bs sbase : temp_env :=
  PTree.set jets_secp._env v_env
    (PTree.set jets_secp._src (Vptr bs (Ptrofs.repr sbase))
      (PTree.set jets_secp._dst (Vptr bd (Ptrofs.repr dbase))
        (create_undef_temps (fn_temps f_simplicity_fe_multiply)))).
Lemma secp_fe_mul_entry v_env m ml ma mb bl ba bb bd dbase bs sbase :
  Mem.alloc m 0 16 = (ml, bl) -> Mem.alloc ml 0 40 = (ma, ba) ->
  Mem.alloc ma 0 40 = (mb, bb) ->
  function_entry2 secp_ge f_simplicity_fe_multiply
    [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] m
    (secp_public_add_env bl ba bb) (secp_mul_temps v_env bd dbase bs sbase) mb.
Proof.
  intros HL HA HB; constructor.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - cbn; repeat constructor; cbn; intuition discriminate.
  - intros x y HX HY Hxy; cbn in HX, HY.
    repeat match goal with H : _ \/ _ |- _ => destruct H end; subst;
      first [contradiction|vm_compute in Hxy; discriminate|congruence].
  - eapply alloc_variables_cons with (m1 := ml) (b1 := bl).
    + change (Mem.alloc m 0 16 = (ml, bl)); exact HL.
    + eapply alloc_variables_cons with (m1 := ma) (b1 := ba).
      * change (Mem.alloc ml 0 40 = (ma, ba)); exact HA.
      * eapply alloc_variables_cons with (m1 := mb) (b1 := bb).
        -- change (Mem.alloc ma 0 40 = (mb, bb)); exact HB.
        -- constructor.
  - reflexivity.
Qed.

(** ** Statement suffix and whole call *)
Theorem exec_secp_fe_mul_rest_literal le m0 bd dbase bw outedge cursor N bi edge rc
    (a b : Ty.tySem (Word 8)) m ba bb bl :
  le!jets_secp._dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
  write_frame_at m0 bd dbase bw outedge cursor N ->
  frame_input_cells_at m0 bi edge rc (@encode (Ty.Prod (Word 8) (Word 8)) (a,b)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  Mem.range_perm m ba 0 40 Cur Freeable -> Mem.range_perm m bb 0 40 Cur Freeable ->
  Mem.range_perm m bl 0 16 Cur Freeable -> frame_fields_at m bl 0 bi edge rc ->
  ba <> bb -> ba <> bl -> bb <> bl ->
  xsep (extA m0 bd bw bi) [(ba,0);(bl,0)] ->
  xsep (extA m0 bd bw bi) [(bb,0);(bl,0)] ->
  invA m0 bd dbase bw outedge cursor N bi rc false [] 256
    (read_fe_rho (frame_input_word_bits a) rc) [] m ->
  exists mf,
    Clight2.exec_stmt secp_ge (secp_public_add_env bl ba bb) le m secp_fe_mul_rest E0 le mf
      (Out_return (Some (Vint Int.one, tint))) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@literal_fe_multiply Alg.CoreFunSem (a,b))) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\
    Mem.range_perm mf bb 0 40 Cur Freeable /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (fun bx _ => bx <> ba /\ bx <> bb /\ bx <> bl /\
      ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HDst HO HI Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv.
  destruct (eval_fe_mul_four_calls m0 bd dbase bw outedge cursor N bi edge rc
    a b m ba bb bl HO HI Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv)
    as (ma & mb & mn & mf & HReadA & HReadB & HMul & HWrite & HFinal &
      HFinalA & HFinalB & HFinalL & HFrame).
  exists mf. split.
  - eapply exec_secp_mul_rest_calls; eassumption.
  - split; [exact HFinal|]. split; [exact HFinalA|].
    split; [exact HFinalB|]. split; assumption.
Qed.

Theorem eval_secp_fe_mul_literal v_env m0 bd dbase bs sbase bw outedge cursor N bi edge rc
    (a b : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw outedge cursor N -> 256 <= N ->
  frame_base_valid sbase -> (8 | sbase) -> frame_fields_at m0 bs sbase bi edge rc ->
  frame_input_cells_at m0 bi edge rc (@encode (Ty.Prod (Word 8) (Word 8)) (a,b)) ->
  0 <= rc -> rc+512 <= Int64.max_unsigned ->
  exists mf,
    Clight2.eval_funcall secp_ge m0 (Internal f_simplicity_fe_multiply)
      [Vptr bd (Ptrofs.repr dbase); Vptr bs (Ptrofs.repr sbase); v_env] E0 mf (Vint Int.one) /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@literal_fe_multiply Alg.CoreFunSem (a,b))) /\
    lframe (fun bx _ => ~ extA m0 bd bw bi bx) m0 mf.
Proof.
  intros HO HN HBase HAlign HFields HI Hrc HM.
  destruct (Mem.alloc m0 0 16) as [ml bl] eqn:HL.
  destruct (Mem.alloc ml 0 40) as [ma ba] eqn:HA.
  destruct (Mem.alloc ma 0 40) as [mb bb] eqn:HB.
  set (le := secp_mul_temps v_env bd dbase bs sbase).
  destruct (secp_prepare_add_locals le m0 ml ma mb bl ba bb bd dbase bs sbase
    bw outedge cursor N bi edge rc a HL HA HB HO HN HBase HAlign HFields eq_refl)
    as (mc & HCopy & HFA & HFB & HFL & HSource & HAB & HAL & HBL &
      HXSA & HXSB & HInv & HPrep & HFreshA & HFreshB & HFreshL).
  destruct (exec_secp_fe_mul_rest_literal le m0 bd dbase bw outedge cursor N bi edge rc
    a b mc ba bb bl eq_refl HO HI Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv)
    as (mw & HRest & HFinal & HFinalA & HFinalB & HFinalL & HRestFrame).
  destruct (secp_free_add_locals mw bl ba bb HAL HBL HAB HFinalL HFinalA HFinalB)
    as (mf & HFree & HFreeFrame).
  assert (HFreeExt : eqext m0 bd bw bi mw mf).
  { eapply lframe_implies; [exact HFreeFrame|].
    intros bx pos [_ HValid] _; repeat split; intro HE; subst bx; contradiction. }
  exists mf. split.
  - eapply eval_funcall_internal with (e := secp_public_add_env bl ba bb)
      (le1 := le) (le2 := le) (m1 := mb) (m2 := mw)
      (out := Out_return (Some (Vint Int.one, tint))).
    + eapply secp_fe_mul_entry; eassumption.
    + rewrite secp_fe_mul_body.
      eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mc) (le1 := le); eassumption.
    + cbn; split; [discriminate|reflexivity].
    + exact HFree.
  - split.
    + eapply finv_stable; [exact HO|exact HFinal|exact HFreeExt].
    + assert (HOutside : lframe (fun bx _ => Mem.valid_block m0 bx /\ ~ extA m0 bd bw bi bx) m0 mf).
      { eapply lframe_trans.
        - eapply lframe_implies; [exact HPrep|].
          intros bx pos [HValid _] _; repeat split; intro HE; subst bx; contradiction.
        - eapply lframe_trans.
          + eapply lframe_implies; [exact HRestFrame|].
            intros bx pos [HValid HExt] _; split; [intro HE; subst bx; contradiction|].
            split; [intro HE; subst bx; contradiction|].
            split; [intro HE; subst bx; contradiction|exact HExt].
          + eapply lframe_implies; [exact HFreeFrame|].
            intros bx pos [HValid _] _; repeat split; intro HE; subst bx; contradiction. }
      eapply lframe_implies; [exact HOutside|]. intros bx pos HExt HValid; split; assumption.
Qed.

(** ** The standard public contract *)
Theorem fe_multiply_literal_local_spec :
  secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8)
    (@literal_fe_multiply Alg.CoreFunSem).
Proof.
  intros env m bd dbase bs sbase bi bw edge outedge cursor rc [a b]
    HBase HAlign HSource HCursor HMax HInput HOutput.
  change (rc+512 <= Int64.max_unsigned) in HMax.
  change (write_frame_at m bd dbase bw outedge cursor 256) in HOutput.
  destruct (eval_secp_fe_mul_literal env m bd dbase bs sbase bw outedge cursor 256 bi edge rc a b
    HOutput ltac:(lia) HBase HAlign HSource HInput HCursor HMax)
    as (mf & HCall & HFinal & HFrame).
  destruct HFinal as (HV & HF & HN & (HCells & HPrefix & HFields & HLoads & HPerms) & Hw).
  rewrite encode_length in HFields, HLoads.
  exists mf. split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
  split; [exact HFields|].
  intros chunk bx ofs HValid HFrameOther HOutputOther.
  destruct (Pos.eq_dec bx bd) as [HD|HD];
    [apply HLoads; [split; [left; exact HD|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec bx bw) as [HW|HW];
    [apply HLoads; [split; [right; left; exact HW|exact HValid]|assumption|assumption]|].
  destruct (Pos.eq_dec bx bi) as [HI|HI];
    [apply HLoads; [split; [right; right; exact HI|exact HValid]|assumption|assumption]|].
  apply (proj1 HFrame); [exact HValid|]. intros pos HPos.
  unfold extA, fext; intros [[H|[H|H]] _]; contradiction.
Qed.

(** The same contract stated against the canonical (non-literal) program. *)
Theorem fe_multiply_local_spec :
  secp_jet_local_spec f_simplicity_fe_multiply (Ty.Prod (Word 8) (Word 8)) (Word 8)
    (@canonical_fe_multiply Alg.CoreFunSem).
Proof. rewrite <- literal_fe_multiply_matches. exact fe_multiply_literal_local_spec. Qed.

Print Assumptions secp_fe_mul_entry.
Print Assumptions eval_secp_fe_mul_literal.
Print Assumptions fe_multiply_literal_local_spec.
Print Assumptions fe_multiply_local_spec.
