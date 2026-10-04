(** Generic proofs of the core padding jets
      left:  [src_local = src; for (i<c) writeN(dst, pad); copyBits(dst, &src_local, N); return 1]
      right: [src_local = src; copyBits(dst, &src_local, N); for (i<c) writeN(dst, pad); return 1]
    without an external-library premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight Maps Errors.
From compcert Require Import ClightBigstep Memory Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine.
Require Import C.jets C.jet_exec C.jet_frame_layout C.jet_frame_copy C.jet_frame_copy_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_output_layout_step C.jet_input_layout C.jet_encoding.
Require Import C.jet_context_separated C.jet_bitmachine_rep C.jet_copyBits_separation.
Require Import C.jet_bitcoin_effects C.jet_core_wrapper C.jet_core_copy_exec C.jet_core_loop.
Require Import C.jet_core_pad_spec C.jet_core_pad C.jet_core_copy_jets.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque ge0.
Set Default Timeout 60.

Lemma core_sep_cursor_mono bd bi bw edge outedge cursor cursor' rc N :
  jet_copy_buffers_separated bd bi bw edge outedge cursor rc N -> 0 <= cursor' <= cursor ->
  jet_copy_buffers_separated bd bi bw edge outedge cursor' rc N.
Proof.
  intros [HD [HB|HR]] Hc. split; [exact HD|]. left; exact HB.
  split; [exact HD|]. right. unfold disjoint_ranges in *.
  pose proof (copy_frame_words_mono cursor' cursor ltac:(lia)). lia.
Qed.

Definition pad_count_expr (M N : Z) : expr :=
  Ebinop Osub (Ebinop Odiv (Econst_int (Int.repr M) tint) (Econst_int (Int.repr N) tint) tint)
    (Econst_int (Int.repr 1) tint) tint.
Definition pad_count_expr1 (M : Z) : expr :=
  Ebinop Osub (Econst_int (Int.repr M) tint) (Econst_int (Int.repr 1) tint) tint.

Lemma int_eq_small_false x y : 0 <= x <= 64 -> x <> y mod Int.modulus ->
  Int.eq (Int.repr x) (Int.repr y) = false.
Proof.
  intros Hx Hne. apply Int.eq_false. intro HE. apply (f_equal Int.unsigned) in HE.
  rewrite (Int.unsigned_repr x) in HE by (change Int.max_unsigned with 4294967295; lia).
  rewrite Int.unsigned_repr_eq in HE. lia.
Qed.

Lemma eval_pad_count_expr e le m M N :
  0 < N <= M -> M <= 64 ->
  eval_expr ge0 e le m (pad_count_expr M N) (Vint (Int.repr (M / N - 1))).
Proof.
  intros HN HM.
  assert (HD : Int.divs (Int.repr M) (Int.repr N) = Int.repr (M / N)).
  { unfold Int.divs. rewrite !Int.signed_repr by (change Int.min_signed with (-2147483648); change Int.max_signed with 2147483647; lia).
    rewrite Z.quot_div_nonneg by lia. reflexivity. }
  assert (Hq : 0 <= M / N <= 64) by (split; [apply Z.div_pos; lia|apply Z.div_le_upper_bound; lia]).
  eapply eval_Ebinop with (v1 := Vint (Int.repr (M / N))) (v2 := Vint (Int.repr 1)).
  - eapply eval_Ebinop with (v1 := Vint (Int.repr M)) (v2 := Vint (Int.repr N));
      [apply eval_Econst_int|apply eval_Econst_int|].
    simpl. unfold sem_div, sem_binarith, sem_cast. simpl.
    rewrite HD.
    assert (Hz : Int.eq (Int.repr N) Int.zero = false).
    { change Int.zero with (Int.repr 0). apply int_eq_small_false; [lia|]. change (0 mod Int.modulus) with 0. lia. }
    assert (Hm : Int.eq (Int.repr M) (Int.repr Int.min_signed) = false).
    { apply int_eq_small_false; [lia|]. change (Int.min_signed mod Int.modulus) with 2147483648. lia. }
    rewrite Hz, Hm. simpl. reflexivity.
  - apply eval_Econst_int.
  - simpl. unfold sem_sub, sem_binarith, sem_cast. simpl.
    f_equal. f_equal. unfold Int.sub. rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    reflexivity.
Qed.

Lemma eval_pad_count_expr1 e le m M :
  1 <= M <= 64 ->
  eval_expr ge0 e le m (pad_count_expr1 M) (Vint (Int.repr (M - 1))).
Proof.
  intros HM.
  eapply eval_Ebinop with (v1 := Vint (Int.repr M)) (v2 := Vint (Int.repr 1));
    [apply eval_Econst_int|apply eval_Econst_int|].
  simpl. unfold sem_sub, sem_binarith, sem_cast. simpl.
  f_equal. f_equal. unfold Int.sub. rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
  reflexivity.
Qed.

Lemma core_pad_frame_after m m1 bd dbase bw outedge cursor n count cells :
  Z.of_nat (length cells) = n -> 0 <= count ->
  write_frame_at m bd dbase bw outedge cursor (n + count) ->
  write_effect m m1 bd dbase bw outedge cursor n cells ->
  write_frame_at m1 bd dbase bw outedge (cursor - n) count.
Proof. intros; eapply write_frame_at_after_effect; eassumption. Qed.

Theorem core_left_pad_jet f (A B : Ty) (spec : tySem A -> tySem B)
    (c w Nn : Z) (cnt : expr) (stmt : statement) (pcells : list Cell) :
  core_wrapper_shape f (Ssequence (core_for_loop cnt stmt) (core_simple_rest (core_copy_call Nn))) ->
  Nn = Z.of_nat (bitSize A) -> Z.of_nat (bitSize B) = c * w + Nn -> 0 < Nn <= 64 -> 0 < w ->
  0 <= c <= 1000 -> Z.of_nat (length pcells) = w -> typeof cnt = tint ->
  (forall e le m', eval_expr ge0 e le m' cnt (Vint (Int.repr c))) ->
  (forall bl le' m cur bd dbase bw edge, le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
    write_frame_at m bd dbase bw edge cur w ->
    exists m', Clight2.exec_stmt ge0 (core_src_locals bl) le' m stmt E0 le' m' Out_normal /\
      write_effect m m' bd dbase bw edge cur w pcells) ->
  (forall a, encode (spec a) = rep_cells pcells (Z.to_nat c) ++ encode a) ->
  jet_separated_local_spec f A B spec.
Proof.
  intros Hshape HN HM HNn Hw Hc Hpl Hty Hcnt Hwr Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign [HSedge HSoff] H0 Hmax Hin Hout Hsep.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge)) (Vlong (Int64.repr rc))
    HSedge HSoff) as [bytes HBytes].
  assert (Hrep : Z.of_nat (length (rep_cells pcells (Z.to_nat c))) = c * w).
  { rewrite rep_cells_length, Nat2Z.inj_mul, Z2Nat.id by lia. rewrite Hpl. reflexivity. }
  assert (Hlenenc : Z.of_nat (length (encode a)) = Nn) by (rewrite encode_length, HN; reflexivity).
  assert (Hlenspec : Z.of_nat (length (encode (spec a))) = Z.of_nat (bitSize B))
    by (rewrite encode_length; reflexivity).
  destruct (core_wrapper_layout f (Ssequence (core_for_loop cnt stmt) (core_simple_rest (core_copy_call Nn)))
    (encode (spec a)) env m bd dbase bs sbase bw outedge cursor (Z.of_nat (bitSize B)) bytes Hshape
    HBase HAlign HBytes ltac:(lia) Hout) as (mf & Hcall & HC & HP & HFl & HL).
  - unfold core_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    pose proof (core_local_frame_fields m ma mc bl bs sbase bytes bi edge rc HAlloc HBytes HStore
      HSedge HSoff) as HLoc.
    assert (HInC : frame_input_cells_at mc bi edge rc (encode a)).
    { eapply core_input_cells_load_preserved; [|exact Hin]. intros ofs w' HL. apply HLP. exact HL. }
    pose proof (fresh_frame_not_loaded m ma bl bd Mptr dbase _ HAlloc (proj1 (proj1 (proj2 Hout)))) as Hbd.
    destruct (write_frame_at_head m bd dbase bw outedge cursor (Z.of_nat (bitSize B)) ltac:(lia) Hout)
      as [_ [_ [_ [w0 Hw0]]]].
    pose proof (fresh_frame_not_loaded m ma bl bw Mint64 _ _ HAlloc Hw0) as Hbw.
    assert (Hdst : (core_wrapper_temps f env bd dbase bs sbase)!_dst = Some (Vptr bd (Ptrofs.repr dbase)))
      by (unfold core_wrapper_temps; rewrite !PTree.gso by discriminate; apply PTree.gss).
    set (le0 := core_wrapper_temps f env bd dbase bs sbase) in *.
    pose proof HFrameC as HFrameC0.
    destruct (core_pad_loop_phase (core_src_locals bl) le0 c w cnt stmt pcells mc bd dbase bw outedge cursor
      (Z.of_nat (bitSize B)) Hty (fun m' k _ => Hcnt _ _ _) Hc Hpl Hw HFrameC ltac:(nia) ltac:(nia) Hdst
      (fun le' m cur Hd HF => Hwr bl le' m cur bd dbase bw outedge Hd HF)) as (ml & Hloop & Heff1).
    assert (HFcopy : write_frame_at ml bd dbase bw outedge (cursor - c * w) Nn).
    { eapply write_frame_at_after_effect with (m := mc) (cells := rep_cells pcells (Z.to_nat c));
        [exact Hrep|lia| |exact Heff1].
      replace (c * w + Nn) with (Z.of_nat (bitSize B)) by lia. exact HFrameC. }
    pose proof HFrameC as [_ [_ [_ [Hcnt0 _]]]].
    pose proof Heff1 as Heff1c.
    destruct Heff1 as (O1 & P1 & F1 & L1 & Pm1 & V1).
    assert (HInL : frame_input_cells_at ml bi edge rc (encode a)).
    { assert (A1 : jet_copy_buffers_separated bd bi bw edge outedge cursor rc Nn) by (rewrite HN; exact Hsep).
      assert (A2 : 1 <= cursor) by nia.
      assert (A3 : outedge <= outedge + 8 * ((cursor - c * w) / 64)).
      { pose proof (Z.div_pos (cursor - c * w) 64 ltac:(nia) ltac:(lia)). lia. }
      assert (A4 : write_word_address outedge cursor + 8 <= outedge + 8 * frame_words cursor).
      { pose proof (copy_write_word_region outedge cursor 0 ltac:(nia)) as Hww.
        rewrite Z.sub_0_r in Hww. exact (proj2 Hww). }
      exact (core_input_after_effect mc ml bd dbase bi bw edge outedge cursor rc Nn (encode a)
        (outedge + 8 * ((cursor - c * w) / 64)) A1 H0 (ltac:(lia)) A2 A3 A4 L1 HInC). }
    assert (HSepL : jet_copy_buffers_separated bd bi bw edge outedge (cursor - c * w) rc Nn).
    { eapply core_sep_cursor_mono; [rewrite HN; exact Hsep|nia]. }
    assert (HLocL : frame_fields_at ml bl 0 bi edge rc).
    { destruct HLoc as [HE HO]. split.
      - rewrite (L1 Mptr bl 0 (or_introl Hbd) (or_introl Hbw)). exact HE.
      - rewrite (L1 Mint64 bl (0 + 8) (or_introl Hbd) (or_introl Hbw)). exact HO. }
    assert (Hdst2 : (le_at le0 c)!_dst = Some (Vptr bd (Ptrofs.repr dbase)))
      by (unfold le_at; rewrite PTree.gso by discriminate; exact Hdst).
    destruct (core_copy_phase ml bl bd dbase bw outedge (cursor - c * w) bi edge rc Nn (encode a)
      (le_at le0 c) HLocL HFcopy ltac:(lia) HNn HSepL HInL Hdst2) as (mf & Hexec2 & Heff2).
    assert (Heff : write_effect mc mf bd dbase bw outedge cursor (c * w + Nn)
      (rep_cells pcells (Z.to_nat c) ++ encode a)).
    { eapply write_effect_seq with (m1 := ml) (n1 := c * w) (n2 := Nn); [exact Hrep|lia| | exact Heff1c|exact Heff2].
      replace (c * w + Nn) with (Z.of_nat (bitSize B)) by lia. exact HFrameC. }
    exists (le_at le0 c), mf. split.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := ml) (le1 := le_at le0 c); [exact Hloop|].
      apply exec_core_simple_rest. exact Hexec2.
    + rewrite <- Hspec in Heff. replace (c * w + Nn) with (Z.of_nat (bitSize B)) in Heff by lia.
      destruct Heff as (O & P & F & L & Pm & V).
      split; [exact O|]. split; [exact P|]. split; [exact F|]. split.
      * intros chunk b ofs _ H1 H2. apply L; assumption.
      * split; assumption.
  - exists mf. split; [exact Hcall|]. split; [exact HC|]. split; [exact HP|]. split; [exact HFl|exact HL].
Qed.

Theorem core_right_pad_jet f (A B : Ty) (spec : tySem A -> tySem B)
    (c w Nn : Z) (cnt : expr) (stmt : statement) (pcells : list Cell) :
  core_wrapper_shape f (Ssequence (core_copy_call Nn) (core_simple_rest (core_for_loop cnt stmt))) ->
  Nn = Z.of_nat (bitSize A) -> Z.of_nat (bitSize B) = Nn + c * w -> 0 < Nn <= 64 -> 0 < w ->
  1 <= c <= 1000 -> Z.of_nat (length pcells) = w -> typeof cnt = tint ->
  (forall e le m', eval_expr ge0 e le m' cnt (Vint (Int.repr c))) ->
  (forall bl le' m cur bd dbase bw edge, le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
    write_frame_at m bd dbase bw edge cur w ->
    exists m', Clight2.exec_stmt ge0 (core_src_locals bl) le' m stmt E0 le' m' Out_normal /\
      write_effect m m' bd dbase bw edge cur w pcells) ->
  (forall a, encode (spec a) = encode a ++ rep_cells pcells (Z.to_nat c)) ->
  jet_separated_local_spec f A B spec.
Proof.
  intros Hshape HN HM HNn Hw Hc Hpl Hty Hcnt Hwr Hspec env m bd dbase bs sbase bi bw edge outedge cursor rc a
    HBase HAlign [HSedge HSoff] H0 Hmax Hin Hout Hsep.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge)) (Vlong (Int64.repr rc))
    HSedge HSoff) as [bytes HBytes].
  assert (Hrep : Z.of_nat (length (rep_cells pcells (Z.to_nat c))) = c * w).
  { rewrite rep_cells_length, Nat2Z.inj_mul, Z2Nat.id by lia. rewrite Hpl. reflexivity. }
  assert (Hlenenc : Z.of_nat (length (encode a)) = Nn) by (rewrite encode_length, HN; reflexivity).
  destruct (core_wrapper_layout f (Ssequence (core_copy_call Nn) (core_simple_rest (core_for_loop cnt stmt)))
    (encode (spec a)) env m bd dbase bs sbase bw outedge cursor (Z.of_nat (bitSize B)) bytes Hshape
    HBase HAlign HBytes ltac:(nia) Hout) as (mf & Hcall & HC & HP & HFl & HL).
  - unfold core_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
    pose proof (core_local_frame_fields m ma mc bl bs sbase bytes bi edge rc HAlloc HBytes HStore
      HSedge HSoff) as HLoc.
    assert (HInC : frame_input_cells_at mc bi edge rc (encode a)).
    { eapply core_input_cells_load_preserved; [|exact Hin]. intros ofs w' HL. apply HLP. exact HL. }
    assert (Hdst : (core_wrapper_temps f env bd dbase bs sbase)!_dst = Some (Vptr bd (Ptrofs.repr dbase)))
      by (unfold core_wrapper_temps; rewrite !PTree.gso by discriminate; apply PTree.gss).
    set (le0 := core_wrapper_temps f env bd dbase bs sbase) in *.
    assert (HFc : write_frame_at mc bd dbase bw outedge cursor Nn).
    { eapply write_frame_at_shorter; [|exact HFrameC]. nia. }
    assert (HSepC : jet_copy_buffers_separated bd bi bw edge outedge cursor rc Nn)
      by (rewrite HN; exact Hsep).
    destruct (core_copy_phase mc bl bd dbase bw outedge cursor bi edge rc Nn (encode a) le0
      HLoc HFc ltac:(lia) HNn HSepC HInC Hdst) as (mk & Hexec1 & Heff1).
    assert (HFloop : write_frame_at mk bd dbase bw outedge (cursor - Nn) (c * w)).
    { eapply write_frame_at_after_effect with (m := mc) (cells := encode a);
        [exact Hlenenc|nia| |exact Heff1].
      replace (Nn + c * w) with (Z.of_nat (bitSize B)) by lia. exact HFrameC. }
    destruct (core_pad_loop_phase (core_src_locals bl) le0 c w cnt stmt pcells mk bd dbase bw outedge
      (cursor - Nn) (c * w) Hty (fun m' k _ => Hcnt _ _ _) ltac:(lia) Hpl Hw HFloop ltac:(nia) ltac:(lia) Hdst
      (fun le' m cur Hd HF => Hwr bl le' m cur bd dbase bw outedge Hd HF)) as (ml & Hloop & Heff2).
    assert (Heff : write_effect mc ml bd dbase bw outedge cursor (Nn + c * w)
      (encode a ++ rep_cells pcells (Z.to_nat c))).
    { eapply write_effect_seq with (m1 := mk) (n1 := Nn) (n2 := c * w); [exact Hlenenc|nia| | exact Heff1|exact Heff2].
      replace (Nn + c * w) with (Z.of_nat (bitSize B)) by lia. exact HFrameC. }
    exists (le_at le0 c), ml. split.
    + eapply exec_Sseq_1 with (t1 := E0) (t2 := E0) (m1 := mk) (le1 := le0); [exact Hexec1|].
      apply exec_core_simple_rest. exact Hloop.
    + rewrite <- Hspec in Heff. replace (Nn + c * w) with (Z.of_nat (bitSize B)) in Heff by lia.
      destruct Heff as (O & P & F & L & Pm & V).
      split; [exact O|]. split; [exact P|]. split; [exact F|]. split.
      * intros chunk b ofs _ H1 H2. apply L; assumption.
      * split; assumption.
  - exists mf. split; [exact Hcall|]. split; [exact HC|]. split; [exact HP|]. split; [exact HFl|exact HL].
Qed.
