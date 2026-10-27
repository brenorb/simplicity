(** Compose all four original quotient stores. The destination may start
    uninitialized; the complete product array is retained for the round bit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_statement_prefix
 C.jet_secp_scalar_shift384_control C.jet_secp_scalar_shift384_copy C.jet_secp_scalar_get_b32_storage
 C.jet_sx_mem C.jet_clight_internal_permissions.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition shift384_fixed le br := le!_r=Some (Vptr br Ptrofs.zero) /\
 le!_shift=Some (Vint (Int.repr 384)) /\ le!_shiftlow=Some (Vint Int.zero) /\
 le!_shiftlimbs=Some (Vint (Int.repr 6)).
Definition shift384_words (w:nat->int64) := [w 6%nat;w 7%nat;Int64.zero;Int64.zero].
Definition shift384_prefix w br count m := forall j,(j<count)%nat ->
 Mem.load Mint64 m br (8*Z.of_nat j)=Some (Vlong (shift384_copy_value j (w (6+j)%nat))).
Definition shift384_product w bl m := forall j,(j<8)%nat ->
 Mem.load Mint64 m bl (8*Z.of_nat j)=Some (Vlong (w j)).
Definition shift384_copy_range start count := statement_sequence
 (map shift384_copy_statement (seq start count)) Sskip.

Lemma shift384_copy_fixed i le word br : (i<4)%nat -> shift384_fixed le br ->
 shift384_fixed (shift384_copy_temps i le word) br.
Proof.
 intros Index (R & Shift & Low & Limbs);unfold shift384_fixed;repeat split;
 (rewrite shift384_copy_other;
 [assumption|destruct i as [|[|[|i]]];cbn [shift384_copy_ids In];intuition discriminate]).
Qed.

Lemma shift384_store_exists m br i word : (i<4)%nat -> Mem.range_perm m br 0 32 Cur Freeable ->
 exists mf,Mem.store Mint64 m br (8*Z.of_nat i) (Vlong word)=Some mf /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ keeps_permissions m mf /\ lframe (fun b _=>b<>br) m mf.
Proof.
 intros Index Free.
 destruct (Mem.valid_access_store m Mint64 br (8*Z.of_nat i) (Vlong word)) as (mf & Store).
 { split.
   - intros pos Range;change (8*Z.of_nat i<=pos<8*Z.of_nat i+8) in Range.
     eapply Mem.perm_implies;[apply Free;lia|constructor].
   - change (8|8*Z.of_nat i);exists (Z.of_nat i);ring. }
 exists mf;split;[exact Store|];split.
 - intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Free;exact Range].
 - split.
   + intros b pos k p Perm;eapply Mem.perm_store_1;[exact Store|exact Perm].
   + apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|];intros;congruence.
Qed.

Theorem exec_shift384_copy_range count : forall start w e le m br bl,
 (start+count=4)%nat -> br<>bl -> e!_l=Some (bl,tarray tulong 8) -> shift384_fixed le br ->
 shift384_prefix w br start m -> shift384_product w bl m -> Mem.range_perm m br 0 32 Cur Freeable ->
 exists le' mf,Clight2.exec_stmt secp_ge e le m (shift384_copy_range start count) E0 le' mf Out_normal /\
 shift384_fixed le' br /\ shift384_prefix w br 4 mf /\ shift384_product w bl mf /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ keeps_permissions m mf /\ lframe (fun b _=>b<>br) m mf.
Proof.
 induction count as [|count IH];intros start w e le m br bl Sum Separate Local Fixed Prefix Product Free.
 - assert (Start:start=4%nat) by lia;subst start;exists le,m;split;[constructor|].
   split;[exact Fixed|];split;[exact Prefix|];split;[exact Product|];split;[exact Free|];split;
   [intros b pos k p Perm;exact Perm|apply lframe_refl].
 - assert (Index:(start<4)%nat) by lia.
   destruct (shift384_store_exists m br start (shift384_copy_value start (w (6+start)%nat)) Index Free)
    as (m1 & Store & Free1 & Keep1 & Frame1).
   assert (Prefix1:shift384_prefix w br (S start) m1).
   { intros j J;destruct (Nat.eq_dec j start) as [->|Different].
     - rewrite (Mem.load_store_same _ _ _ _ _ _ Store);reflexivity.
     - rewrite (Mem.load_store_other _ _ _ _ _ _ Store) by
        (right;left;change (8*Z.of_nat j+8<=8*Z.of_nat start);lia).
       apply Prefix;lia. }
   assert (Product1:shift384_product w bl m1).
   { intros j J;rewrite (Mem.load_store_other _ _ _ _ _ _ Store) by (left;congruence);apply Product;exact J. }
   pose proof (shift384_copy_fixed start le (w (6+start)%nat) br Index Fixed) as Fixed1.
   destruct (IH (S start) w e (shift384_copy_temps start le (w (6+start)%nat)) m1 br bl
    ltac:(lia) Separate Local Fixed1 Prefix1 Product1 Free1)
    as (le' & mf & Rest & Fixed' & Prefix' & Product' & Free' & Keep2 & Frame2).
   exists le',mf;split.
   + change (Clight2.exec_stmt secp_ge e le m
      (Ssequence (shift384_copy_statement start) (shift384_copy_range (S start) count)) E0 le' mf Out_normal).
     eapply exec_Sseq_1 with (t1:=E0) (t2:=E0).
     * destruct Fixed as (R & Shift & Low & Limbs);eapply exec_shift384_copy;
       [exact Index|exact Local|exact R|exact Shift|exact Low|exact Limbs| |exact Store].
       intro J;replace (8*(6+Z.of_nat start)) with (8*Z.of_nat (6+start)%nat) by (rewrite Nat2Z.inj_add;reflexivity).
       apply Product;lia.
     * exact Rest.
   + split;[exact Fixed'|];split;[exact Prefix'|];split;[exact Product'|];split;[exact Free'|];split.
     * intros b pos k p Perm;apply Keep2,Keep1;exact Perm.
     * eapply lframe_trans;[exact Frame1|exact Frame2].
Qed.

Lemma shift384_prefix_storage w br m : shift384_prefix w br 4 m -> Mem.range_perm m br 0 32 Cur Freeable ->
 scalar_at m br 0 (shift384_words w).
Proof.
 intros Prefix Free;unfold scalar_at;split;[reflexivity|];split;[lia|];split;[exists 0;lia|];split;
 [change (32<=18446744073709551615);lia|];split.
 - intros pos Range;eapply Mem.perm_implies;[apply Free;lia|constructor].
 - intros i word Nth;destruct i as [|[|[|[|i]]]];try (destruct i;discriminate);
   injection Nth as <-;apply Prefix;lia.
Qed.

Corollary exec_shift384_copies w e le m br bl :
 br<>bl -> e!_l=Some (bl,tarray tulong 8) -> shift384_fixed le br ->
 shift384_product w bl m -> Mem.range_perm m br 0 32 Cur Freeable ->
 exists le' mf,Clight2.exec_stmt secp_ge e le m (shift384_copy_range 0 4) E0 le' mf Out_normal /\
 shift384_fixed le' br /\ scalar_at mf br 0 (shift384_words w) /\ shift384_product w bl mf /\
 Mem.range_perm mf br 0 32 Cur Freeable /\ keeps_permissions m mf /\ lframe (fun b _=>b<>br) m mf.
Proof.
 intros Separate Local Fixed Product Free.
 destruct (exec_shift384_copy_range 4 0 w e le m br bl eq_refl Separate Local Fixed
  ltac:(intros i I;lia) Product Free) as (le' & mf & Run & Fixed' & Prefix & Product' & Rest).
 exists le',mf;split;[exact Run|];split;[exact Fixed'|];split;
 [apply shift384_prefix_storage;[exact Prefix|exact (proj1 Rest)]|split;assumption].
Qed.
