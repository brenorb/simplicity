(** Four original calls from pair input and owned locals; public allocation,
    source copy, entry, return and freeing are still separate obligations. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Ctypes Clight ClightBigstep Integers Values Memory Events.
Require Import Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_sx_state C.jet_sx_mem C.jet_sx_exec.
Require Import C.jet_encoding C.jet_secp_frame C.jet_frame_inv C.jet_output_layout C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_local_regions C.jet_secp_public_body C.jet_secp_local_call.
Require Import C.jet_secp_wrapper_run C.jet_secp_field_add C.jet_secp_literal_add_program.
Require Import C.jet_secp_add_pair_input C.jet_secp_add_two_reads C.jet_secp_add_write_calls.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_add encode.

Lemma no_field_add_foot ba bb bx pos : bx <> ba -> bx <> bb ->
  ~ foot [(ba,0);(bb,0)] (map rshape field_add_initial_regs) bx pos.
Proof.
  intros HA HB (r & s & d & ch & HGet & HCell & HBlock & HRange).
  destruct r as [|[|r]].
  - change (bx = ba) in HBlock. contradiction.
  - change (bx = bb) in HBlock. contradiction.
  - cbn [field_add_initial_regs map nth_error] in HGet. destruct r; discriminate.
Qed.

Theorem eval_field_add_four_calls m0 bd dbase bw outedge cursor N bi edge rc
    (a b : Ty.tySem (Word 8)) m ba bb bl :
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
  exists ma mb mn mf,
    Clight2.eval_funcall secp_ge m (Internal f_read_fe)
      [Vptr ba Ptrofs.zero; Vptr bl Ptrofs.zero] E0 ma Vundef /\
    Clight2.eval_funcall secp_ge ma (Internal f_read_fe)
      [Vptr bb Ptrofs.zero; Vptr bl Ptrofs.zero] E0 mb Vundef /\
    Clight2.eval_funcall secp_ge mb (Internal f_secp256k1_fe_add)
      [Vptr ba Ptrofs.zero; Vptr bb Ptrofs.zero] E0 mn Vundef /\
    Clight2.eval_funcall secp_ge mn (Internal f_write_fe)
      [Vptr bd (Ptrofs.repr dbase); Vptr ba Ptrofs.zero] E0 mf Vundef /\
    finv m0 bd dbase bw outedge cursor N bi mf true
      (encode (@literal_fe_add Alg.CoreFunSem (a,b))) /\
    Mem.range_perm mf ba 0 40 Cur Freeable /\
    Mem.range_perm mf bb 0 40 Cur Freeable /\
    Mem.range_perm mf bl 0 16 Cur Freeable /\
    lframe (fun bx _ => bx <> ba /\ bx <> bb /\ bx <> bl /\
      ~ extA m0 bd bw bi bx) m mf.
Proof.
  intros HO HInput Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv.
  destruct (field_pair_input_slices m0 bi edge rc a b HInput) as [HA HB].
  destruct (eval_add_two_readers m0 bd dbase bw outedge cursor N 256 bi edge rc
    a b m ba bb bl HO HA HB Hrc HM HFA HFB HFL HSource HAB HAL HBL HXSA HXSB HInv)
    as (ma & mb & HReadA & HReadB & HFieldA & HFieldB & HCursor &
      HFreeA & HFreeB & HFreeL & HReadInv & HFrameA & HFrameB).
  change (Int64.repr (rc+256) = Int64.repr (rc+256) /\
    finv m0 bd dbase bw outedge cursor N bi mb false [] /\
    0+256 <= N /\ 0 <= 256) in HReadInv.
  destruct HReadInv as (_ & HFIN & HN & _).
  assert (HS : xsep (extA m0 bd bw bi) [(ba,0);(bb,0)]).
  { intros r Hr. destruct r as [|[|r]].
    - exact (HXSA 0%nat ltac:(cbn; lia)).
    - exact (HXSB 0%nat ltac:(cbn; lia)).
    - cbn in Hr. lia. }
  destruct (eval_add_write_calls m0 bd dbase bw outedge cursor N bi rc mb ba bb
    a b HO HN HAB HFieldA HFieldB HFreeA HFreeB HS HFIN)
    as (mn & mf & HAdd & HWrite & HFinal & HFinalA & HFinalB & HAddFrame & HWriteFrame).
  assert (HV : Mem.valid_block mb bl).
  { eapply Mem.perm_valid_block. apply (HFreeL 0). lia. }
  assert (HFreeLN : Mem.range_perm mn bl 0 16 Cur Freeable).
  { intros pos HP. apply (proj1 (proj2 HAddFrame)); [exact HV| |apply HFreeL; exact HP].
    apply no_field_add_foot; congruence. }
  assert (HVN : Mem.valid_block mn bl).
  { exact (proj2 (proj2 HAddFrame) bl HV). }
  assert (HFinalL : Mem.range_perm mf bl 0 16 Cur Freeable).
  { intros pos HP. apply (proj1 (proj2 HWriteFrame)); [exact HVN| |apply HFreeLN; exact HP].
    split; [exact HVN|]. split.
    - apply no_local_write_foot. congruence.
    - exact (HXSA 1%nat ltac:(cbn; lia)). }
  set (P := fun bx (_ : Z) => bx <> ba /\ bx <> bb /\ bx <> bl /\ ~ extA m0 bd bw bi bx).
  assert (HPA : lframe P m ma).
  { eapply lframe_implies; [exact HFrameA|].
    intros bx pos (HXA & HXB & HXL & HXE) HValid.
    split; [exact HValid|]. split; [apply no_local_read_foot; assumption|exact HXE]. }
  assert (HPB : lframe P ma mb).
  { eapply lframe_implies; [exact HFrameB|].
    intros bx pos (HXA & HXB & HXL & HXE) HValid.
    split; [exact HValid|]. split; [apply no_local_read_foot; assumption|exact HXE]. }
  assert (HPN : lframe P mb mn).
  { eapply lframe_implies; [exact HAddFrame|].
    intros bx pos (HXA & HXB & HXL & HXE) HValid.
    apply no_field_add_foot; assumption. }
  assert (HPF : lframe P mn mf).
  { eapply lframe_implies; [exact HWriteFrame|].
    intros bx pos (HXA & HXB & HXL & HXE) HValid.
    split; [exact HValid|]. split; [apply no_local_write_foot; exact HXA|exact HXE]. }
  exists ma, mb, mn, mf.
  split; [exact HReadA|]. split; [exact HReadB|]. split; [exact HAdd|].
  split; [exact HWrite|]. split; [exact HFinal|]. split; [exact HFinalA|].
  split; [exact HFinalB|]. split; [exact HFinalL|].
  eapply lframe_trans; [exact HPA|]. eapply lframe_trans; [exact HPB|].
  eapply lframe_trans; eassumption.
Qed.
Print Assumptions no_field_add_foot.
Print Assumptions eval_field_add_four_calls.
