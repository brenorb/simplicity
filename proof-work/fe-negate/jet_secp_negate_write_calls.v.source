(** Original negation followed by the whole original writer, from initial facts. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word.
Require Simplicity.Alg Simplicity.Translate.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_exec C.jet_sx_mem.
Require Import C.jet_secp_frame C.jet_secp_fe_math C.jet_secp_local_regions C.jet_secp_linkage C.jets_secp.
Require Import C.jet_output_layout C.jet_frame_inv.
Require Import C.jet_secp_field_negate_storage C.jet_secp_field_negate_values C.jet_secp_field_negate_calls.
Require Import C.jet_secp_negate_writer_bridge C.jet_secp_write_fe_wide_values C.jet_secp_write_fe_wide_exec.
Require Import C.jet_secp_canonical_negate.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Theorem eval_negate_write_calls m0 bd dbase bw edge cursor N bi rc w0 outs0 m b rho
    (x : Ty.tySem (Word 8)) :
  write_frame_at m0 bd dbase bw edge cursor N ->
  rep rho [(b,0)] local_write_initial_regs m ->
  xsep (extA m0 bd bw bi) [(b,0)] ->
  invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 rho [] m ->
  fe_limbs_ok (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) ->
  fe_val (Int64.unsigned (rho 1%nat)) (Int64.unsigned (rho 2%nat))
    (Int64.unsigned (rho 3%nat)) (Int64.unsigned (rho 4%nat)) (Int64.unsigned (rho 5%nat)) =
      @toZ (WordToZ 8) x ->
  @toZ (WordToZ 8) x < feP ->
  exists mn mf,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_fe_negate)
      [Vptr b Ptrofs.zero; Vptr b Ptrofs.zero; Vint Int.one] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr b Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw edge cursor N bi mf true
      (outs0 ++ Simplicity.Translate.encode (@canonical_fe_negate Alg.CoreFunSem x)) /\
    Mem.range_perm mf b 0 40 Cur Freeable /\
    lframe (frame (extA m0 bd bw bi) [(b,0)] local_write_initial_regs m) m mf.
Proof.
  intros HO HR HS HI Hok HV Hlt.
  destruct (eval_field_negate_to_field m b rho HR) as (mn & HNeg & HField & HFree & HFrame).
  assert (HExt : lframe (fun b' _ => extA m0 bd bw bi b') m mn).
  { eapply lframe_implies; [exact HFrame|].
    intros b' pos HE HValid (r & s & d & ch & HN & HCell & HBlock & HRange).
    destruct r as [|r]; [|destruct r; discriminate].
    change (b' = b) in HBlock. subst b'.
    exact (HS 0%nat ltac:(cbn; lia) HE). }
  pose proof (invA_stable m0 bd dbase bw edge cursor N bi rc w0 outs0 256 HO
    rho [] m mn HI HExt) as HIN.
  set (wrho := wide_fe_rho (negate_value rho 0) (negate_value rho 1)
    (negate_value rho 2) (negate_value rho 3) (negate_value rho 4) rc).
  assert (HWI : invA m0 bd dbase bw edge cursor N bi rc w0 outs0 256 wrho [] mn).
  { unfold invA in *. destruct HIN as [_ HRest]. split; [reflexivity|exact HRest]. }
  pose proof (wide_field_initial_rep _ _ _ _ _ rc mn b HField HFree) as HWR.
  pose proof (negate_normalizer_bounds rho Hok) as HB.
  destruct (eval_local_wide_write_fe m0 bd dbase bw edge cursor N bi rc
    (negate_value rho 0) (negate_value rho 1) (negate_value rho 2)
    (negate_value rho 3) (negate_value rho 4) w0 outs0 mn [(b,0)] HO
    (HB 0%nat ltac:(lia)) (HB 1%nat ltac:(lia)) (HB 2%nat ltac:(lia))
    (HB 3%nat ltac:(lia)) (HB 4%nat ltac:(lia)) HWR HS HWI)
    as (mf & HWrite & HFinal & HRepFinal & HWriteFrame).
  rewrite (wide_negate_output rho x Hok HV Hlt) in HFinal.
  pose proof (wide_local_final_freeable _ b mf bd (Ptrofs.repr dbase) HRepFinal) as HFreeFinal.
  assert (HNegOutside : lframe
    (frame (extA m0 bd bw bi) [(b,0)] local_write_initial_regs m) m mn).
  { eapply lframe_implies; [exact HFrame|].
    intros b' pos [_ [HOutside _]] _. exact HOutside. }
  assert (HWriteOutside : lframe
    (frame (extA m0 bd bw bi) [(b,0)] local_write_initial_regs m) mn mf).
  { eapply lframe_implies; [exact HWriteFrame|].
    intros b' pos [HValid [HOutside HNotExt]] _.
    split; [exact (proj2 (proj2 HFrame) b' HValid)|]. split; assumption. }
  exists mn, mf. split; [exact HNeg|]. split; [exact HWrite|].
  split; [exact HFinal|]. split; [exact HFreeFinal|].
  eapply lframe_trans; eassumption.
Qed.
Print Assumptions eval_negate_write_calls.
