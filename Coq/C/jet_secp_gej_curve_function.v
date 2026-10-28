(** Entire original projective validity helper: exact body, three allocations,
    all nine derived arithmetic calls, bool return conversion, and frees. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_square_columns
  C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_gej_curve_statements C.jet_secp_gej_curve_calls C.jet_secp_gej_curve_prefix.
Import Ctypes Values ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition gej_curve_result (x y z : nat -> int64) :=
  if Z.eqb ((radix_value y*radix_value y) mod feP)
    ((radix_value x*radix_value x*radix_value x+
      7*(radix_value z*radix_value z*radix_value z*radix_value z*radix_value z*radix_value z)) mod feP)
    then Int.one else Int.zero.

Theorem exec_gej_curve_body_owned_readback le x y z m ba b_y bx bz :
  le!_a=Some (Vptr ba Ptrofs.zero) ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>b_y -> ba<>bx -> ba<>bz -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m b_y 0 40 Cur Freeable ->
  Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge (gej_curve_helper_env b_y bx bz) le m (fn_body f_simplicity_gej_is_valid_var) E0
    (PTree.set _t'1 (Vint (gej_curve_result x y z)) le) mf
    (Out_return (Some (Vint (gej_curve_result x y z),tint))) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf b_y 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  lframe (gej_curve_frame ba b_y bx bz) m mf /\ gej_curve_input_readback m mf ba x y z.
Proof.
  intros HA BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ.
  destruct (gej_curve_arithmetic_calls_readback x y z m ba b_y bx bz BX BY BZ HAY HAX HAZ HYX HYZ HXZ
    HX HY HZ HFA HFY HFX HFZ)
    as (m1 & m2 & m3 & m4 & m5 & m6 & m7 & m8 & mf & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 &
      AF & YF & XF & ZF & HF & Readback).
  exists mf;split.
  - rewrite gej_curve_helper_source.
    exact (exec_gej_curve_from_calls le m m1 m2 m3 m4 m5 m6 m7 m8 mf ba b_y bx bz
      (gej_curve_result x y z) HA C1 C2 C3 C4 C5 C6 C7 C8 C9).
  - split;[exact AF|]. split;[exact YF|]. split;[exact XF|].
    split;[exact ZF|]. split;[exact HF|exact Readback].
Qed.

Theorem exec_gej_curve_body_owned le x y z m ba b_y bx bz :
  le!_a=Some (Vptr ba Ptrofs.zero) ->
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  ba<>b_y -> ba<>bx -> ba<>bz -> b_y<>bx -> b_y<>bz -> bx<>bz ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable -> Mem.range_perm m b_y 0 40 Cur Freeable ->
  Mem.range_perm m bx 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable ->
  exists mf,
  Clight2.exec_stmt secp_ge (gej_curve_helper_env b_y bx bz) le m (fn_body f_simplicity_gej_is_valid_var) E0
    (PTree.set _t'1 (Vint (gej_curve_result x y z)) le) mf
    (Out_return (Some (Vint (gej_curve_result x y z),tint))) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ Mem.range_perm mf b_y 0 40 Cur Freeable /\
  Mem.range_perm mf bx 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
  lframe (gej_curve_frame ba b_y bx bz) m mf.
Proof.
 intros HA BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ.
 destruct (exec_gej_curve_body_owned_readback le x y z m ba b_y bx bz HA BX BY BZ HAY HAX HAZ HYX HYZ HXZ HX HY HZ HFA HFY HFX HFZ) as (mf & Rest).
 exists mf;tauto.
Qed.

Definition gej_curve_entry_temps ba :=
  PTree.set _a (Vptr ba Ptrofs.zero) (create_undef_temps (fn_temps f_simplicity_gej_is_valid_var)).
Lemma gej_curve_function_ok : fn_okb f_simplicity_gej_is_valid_var=true.
Proof. reflexivity. Qed.
Lemma gej_curve_function_entry m mx my mi ba b_y bx bz :
  Mem.alloc m 0 40=(mx,bx) -> Mem.alloc mx 0 40=(my,b_y) -> Mem.alloc my 0 40=(mi,bz) ->
  function_entry2 secp_ge f_simplicity_gej_is_valid_var [Vptr ba Ptrofs.zero] m
    (gej_curve_helper_env b_y bx bz) (gej_curve_entry_temps ba) mi.
Proof.
  intros AX AY AZ;destruct (fn_okb_true _ gej_curve_function_ok) as (HN1 & HN2 & HD).
  constructor;[exact HN1|exact HN2|exact HD| |reflexivity].
  eapply alloc_variables_cons with (m1:=mx) (b1:=bx);[exact AX|].
  eapply alloc_variables_cons with (m1:=my) (b1:=b_y);[exact AY|].
  eapply alloc_variables_cons with (m1:=mi) (b1:=bz);[exact AZ|constructor].
Qed.
Lemma gej_curve_function_blocks b_y bx bz : blocks_of_env secp_ge (gej_curve_helper_env b_y bx bz)=
  [(b_y,0,40);(bx,0,40);(bz,0,40)].
Proof. reflexivity. Qed.

Theorem eval_gej_curve_function_readback x y z m ba :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf (Vint (gej_curve_result x y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf /\
  gej_curve_input_readback m mf ba x y z.
Proof.
  intros BX BY BZ HX HY HZ HFA.
  destruct (Mem.alloc m 0 40) as [mx bx] eqn:AX.
  destruct (Mem.alloc mx 0 40) as [my b_y] eqn:AY.
  destruct (Mem.alloc my 0 40) as [mi bz] eqn:AZ.
  assert (HOld : forall b, Mem.valid_block m b -> b<>b_y /\ b<>bx /\ b<>bz).
  { intros b HV;repeat split;intro HE;subst b.
    - apply (Mem.fresh_block_alloc _ _ _ _ _ AY);eapply Mem.valid_block_alloc;[exact AX|exact HV].
    - exact (Mem.fresh_block_alloc _ _ _ _ _ AX HV).
    - apply (Mem.fresh_block_alloc _ _ _ _ _ AZ).
      eapply Mem.valid_block_alloc;[exact AY|]. eapply Mem.valid_block_alloc;[exact AX|exact HV]. }
  assert (HV : Mem.valid_block m ba) by (eapply Mem.perm_valid_block;apply (HFA 0);lia).
  destruct (HOld ba HV) as (HAY & HAX & HAZ).
  assert (HYX : b_y<>bx).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AY);rewrite HE;eapply Mem.valid_new_block;exact AX. }
  assert (HYZ : b_y<>bz).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AZ);rewrite <- HE;eapply Mem.valid_new_block;exact AY. }
  assert (HXZ : bx<>bz).
  { intro HE;apply (Mem.fresh_block_alloc _ _ _ _ _ AZ);rewrite <- HE.
    eapply Mem.valid_block_alloc;[exact AY|eapply Mem.valid_new_block;exact AX]. }
  assert (FAlloc : lframe (fun _ _ => True) m mi).
  { eapply lframe_trans.
    - apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact AX.
    - eapply lframe_trans;apply lframe_unchanged;eapply Mem.alloc_unchanged_on;eassumption. }
  pose proof (field_at_lframe m mi ba 0 _ _ HX FAlloc ltac:(intros;exact I)) as HXi.
  pose proof (field_at_lframe m mi ba 40 _ _ HY FAlloc ltac:(intros;exact I)) as HYi.
  pose proof (field_at_lframe m mi ba 80 _ _ HZ FAlloc ltac:(intros;exact I)) as HZi.
  pose proof (curve_keep_free _ m mi ba 128 ltac:(lia) HFA FAlloc ltac:(intros;exact I)) as HFAi.
  assert (HFXi : Mem.range_perm mi bx 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AZ|]. eapply Mem.perm_alloc_1;[exact AY|].
    eapply Mem.perm_alloc_2;[exact AX|exact HP]. }
  assert (HFYi : Mem.range_perm mi b_y 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_1;[exact AZ|]. eapply Mem.perm_alloc_2;[exact AY|exact HP]. }
  assert (HFZi : Mem.range_perm mi bz 0 40 Cur Freeable).
  { intros pos HP;eapply Mem.perm_alloc_2;[exact AZ|exact HP]. }
  destruct (exec_gej_curve_body_owned_readback (gej_curve_entry_temps ba) x y z mi ba b_y bx bz
    ltac:(apply PTree.gss) BX BY BZ HAY HAX HAZ HYX HYZ HXZ HXi HYi HZi HFAi HFYi HFXi HFZi)
    as (mo & HBody & HFAo & HFYo & HFXo & HFZo & FBody & Readback).
  destruct (free_list_exists [(b_y,0,40);(bx,0,40);(bz,0,40)] mo) as (mf & HFree & HUnchanged).
  - cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi [H|[H|[H|H]]];
      [inversion H;subst;exact HFYo|inversion H;subst;exact HFXo|inversion H;subst;exact HFZo|contradiction].
  - assert (FFree : lframe (fun b _ => b<>b_y /\ b<>bx /\ b<>bz) mo mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact HUnchanged|].
      intros b pos (NY & NX & NZ) HV';cbn;intuition congruence. }
    pose proof (curve_keep_free _ mo mf ba 128 ltac:(lia) HFAo FFree
      ltac:(intro pos;repeat split;assumption)) as HFAf.
    exists mf;split.
    + eapply eval_funcall_internal with (e:=gej_curve_helper_env b_y bx bz) (le1:=gej_curve_entry_temps ba)
        (le2:=PTree.set _t'1 (Vint (gej_curve_result x y z)) (gej_curve_entry_temps ba))
        (m1:=mi) (m2:=mo) (out:=Out_return (Some (Vint (gej_curve_result x y z),tint))).
      * exact (gej_curve_function_entry m mx my mi ba b_y bx bz AX AY AZ).
      * exact HBody.
      * split;[discriminate|]. unfold gej_curve_result;destruct (Z.eqb _ _);reflexivity.
      * rewrite gej_curve_function_blocks;exact HFree.
    + split;[exact HFAf|].
      assert (HFrame : lframe (fun b _ => Mem.valid_block m b /\ b<>ba) m mf).
      { eapply lframe_trans.
        - eapply lframe_implies;[exact FAlloc|];intros;exact I.
        - eapply lframe_trans.
          + eapply lframe_implies;[exact FBody|]. intros b pos [HV0 HNotA] HV1.
            split;[exact HNotA|exact (HOld b HV0)].
          + eapply lframe_implies;[exact FFree|]. intros b pos [HV0 HNotA] HV1;exact (HOld b HV0). }

      split;[eapply lframe_implies;[exact HFrame|intros b pos HOther HV0;split;assumption]|].
      destruct Readback as (AXo & AYo & AZo & Flago).
      unfold gej_curve_input_readback;split.
      * eapply field_at_lframe;[exact AXo|exact FFree|intros;repeat split;assumption].
      * split.
        -- eapply field_at_lframe;[exact AYo|exact FFree|intros;repeat split;assumption].
        -- split.
           ++ eapply field_at_lframe;[exact AZo|exact FFree|intros;repeat split;assumption].
           ++ rewrite (proj1 FFree Mint32 ba 120).
              ** rewrite Flago;apply (proj1 FAlloc);[exact HV|intros;exact I].
              ** eapply Mem.perm_valid_block;apply (HFAo 0);lia.
              ** intros;repeat split;assumption.

Qed.

Theorem eval_gej_curve_function x y z m ba :
  square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
  fe_at m ba 0 (words5 x) -> fe_at m ba 40 (words5 y) -> fe_at m ba 80 (words5 z) ->
  Mem.range_perm m ba 0 128 Cur Freeable ->
  exists mf,
  Clight2.eval_funcall secp_ge m (Internal f_simplicity_gej_is_valid_var)
    [Vptr ba Ptrofs.zero] E0 mf (Vint (gej_curve_result x y z)) /\
  Mem.range_perm mf ba 0 128 Cur Freeable /\ lframe (fun b _ => b<>ba) m mf.
Proof.
 intros BX BY BZ HX HY HZ HFA.
 destruct (eval_gej_curve_function_readback x y z m ba BX BY BZ HX HY HZ HFA) as (mf & Rest).
 exists mf;tauto.
Qed.
