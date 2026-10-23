From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_elements_null_overlap_exec C.jet_env_constructible C.jet_elements_env_constructible.
Require Import C.jet_elements_prim C.jet_elements_null_data_opcode Simplicity.Digest.
Import ListNotations.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 10.

(** Only the null-data projection is represented here. The opcode cache uses
    otherwise unread bytes of the same allocation; no real-builder layout
    or whole-transaction representation is asserted. *)
Definition overlap_output_fields (m : mem) b o (_ : unit) : Prop :=
  Mem.load Mptr m b (o + 224) = Some (Vptr b (Ptrofs.repr o)) /\
  Mem.load Mint64 m b (o + 232) = Some (Vlong Int64.one) /\
  Mem.load Mint8unsigned m b (o + 240) = Some (Vint Int.one) /\
  Mem.load Mint32 m b (o + 32) = Some (Vint (elements_datum_code (@OP1 hash256))).

Lemma overlap_output_fields_local : elem_local overlap_output_fields 248.
Proof.
  intros m1 m2 b o [] (L1 & L2 & L3 & L4) HM.
  unfold overlap_output_fields. repeat split; eapply HM;
    first [eassumption | change (size_chunk Mptr) with 8; lia |
      change (size_chunk Mint64) with 8; lia |
      change (size_chunk Mint8unsigned) with 1; lia |
      change (size_chunk Mint32) with 4; lia | lia].
Qed.

Lemma overlap_output_fields_buildable : elem_buildable 8 overlap_output_fields 248.
Proof.
  intros [] m b o P A.
  destruct (built_store_ptr m b (o + 224) b (Ptrofs.repr o) (o + 224) (o + 232) eq_refl)
    as (m1 & B1 & L1).
  - intros k K. apply P; lia.
  - apply Z.divide_add_r; [exact A|exists 28;reflexivity].
  - lia.
  - lia.
  - destruct (built_store_int64 m1 b (o + 232) Int64.one (o + 232) (o + 240))
      as (m2 & B2 & L2).
    + eapply built_range_perm; [exact B1|]. intros k K. apply P; lia.
    + apply Z.divide_add_r; [exact A|exists 29;reflexivity].
    + lia.
    + lia.
    + destruct (built_store_bool m2 b (o + 240) true (o + 240) (o + 241))
        as (m3 & B3 & L3).
      * eapply built_range_perm; [exact B2|]. eapply built_range_perm; [exact B1|].
        intros k K. apply P; lia.
      * lia.
      * lia.
      * destruct (built_store_int32 m3 b (o + 32) (elements_datum_code (@OP1 hash256))
          (o + 32) (o + 36)) as (m4 & B4 & L4).
        -- eapply built_range_perm; [exact B3|]. eapply built_range_perm; [exact B2|].
           eapply built_range_perm; [exact B1|]. intros k K. apply P; lia.
        -- apply Z.divide_add_r; [eapply Z.divide_trans; [exists 2;reflexivity|exact A]|exists 8;reflexivity].
        -- lia.
        -- lia.
        -- exists m4. split.
           ++ eapply built_trans with (m1 := m1); [eapply built_weaken; [| |exact B1]; lia|].
              eapply built_trans with (m1 := m2); [eapply built_weaken; [| |exact B2]; lia|].
              eapply built_trans with (m1 := m3); [eapply built_weaken; [| |exact B3]; lia|].
              eapply built_weaken; [| |exact B4]; lia.
           ++ destruct B2 as (H2 & _). destruct B3 as (H3 & _). destruct B4 as (H4 & _).
              unfold overlap_output_fields. split.
              ** rewrite H4 by (right;right;lia). rewrite H3 by (right;left;change(size_chunk Mptr)with 8;lia).
                 rewrite H2 by (right;left;change(size_chunk Mptr)with 8;lia). exact L1.
              ** split.
                 --- rewrite H4 by (right;right;lia). rewrite H3 by (right;left;change(size_chunk Mint64)with 8;lia). exact L2.
                 --- split; [rewrite H4 by(right;right;lia);exact L3|exact L4].
Qed.


Require Import C.jet_elements_null_data_output_guard C.jet_elements_null_data_index.

Theorem overlap_environment_constructible :
  exists m be bt bout,
    Mem.valid_block m be /\ Mem.valid_block m bt /\ Mem.valid_block m bout /\
    elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true /\
    elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one /\
    overlap_output_fields m bout 0 tt.
Proof.
  destruct (elements_env_built [tt] overlap_output_fields 248 8 704 Int64.zero Mem.empty
    ltac:(lia) ltac:(exists 31;reflexivity) overlap_output_fields_local overlap_output_fields_buildable
    ltac:(lia) ltac:(lia) ltac:(exists 1;reflexivity)
    ltac:(lia) ltac:(lia) ltac:(exists 88;reflexivity) ltac:(left;lia))
    as (m & be & bt & bout & VE & VT & VO & EP & IX & TP & TC & Output).
  specialize (Output 0%nat tt eq_refl).
  change (overlap_output_fields m bout 0 tt) in Output.
  pose proof Output as (OP & OC & OF & Code).
  exists m,be,bt,bout. do 3 (split; [assumption|]). split.
  - unfold elements_null_data_output_rep.
    do 4 (split; [vm_compute; discriminate|]).
    split; [exact EP|]. split; [exact TC|]. intro Test.
    split; [lia|]. split; [change (241 <= 18446744073709551615);lia|].
    split; [exact TP|exact OF].
  - split; [|exact Output]. unfold elements_null_data_count_path.
    do 6 (split; [vm_compute; discriminate|]).
    split; [exact EP|]. split; [exact TP|exact OC].
Qed.


From compcert Require Import Ctypes Clight ClightBigstep Events.
Require Import C.jet_elements_linkage C.jets_elements C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_output_layout C.jet_encoding C.jet_application_sep C.jet_bitmachine_rep.
Require Import C.jet_elements_null_data_guard_compose.
Require Import Simplicity.Word.

(** A completed public C execution on a constructible projected environment
    and overlapping, individually represented frames. This is not a claim
    about reachability from the evaluator or from the actual env.c builders. *)
Theorem overlap_public_execution_witness :
  exists m mf bd bs bw be bt bout,
    frame_fields_at m bs 0 bw 40 0 /\
    frame_input_word_at m bw 40 0 (@fromZ (WordToZ 5) 0) /\
    frame_input_word_at m bw 40 32 (@fromZ (WordToZ 5) 0) /\
    write_frame_at m bd 0 bw 0 261 261 /\
    elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true /\
    elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one /\
    overlap_output_fields m bout 0 tt /\
    (be <> bd /\ be <> bw /\ bt <> bd /\ bt <> bw /\ bout <> bd /\ bout <> bw) /\
    Clight2.eval_funcall elements_ge m (Internal f_simplicity_output_null_datum)
      [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; Vptr be Ptrofs.zero] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 261 ([Some true; Some false] ++ repeat None 259) /\
    frame_fields_at mf bd 0 bw 0 0.
Proof.
  destruct overlap_environment_constructible
    as (m0 & be & bt & bout & VE & VT & VO & Rep & Count & Output).
  destruct (overlap_frames_constructible m0)
    as (m & bd & bs & bw & DB & Source & Input & Frame & Word & Old).
  assert (Keep : forall c b o v, Mem.load c m0 b o = Some v -> Mem.load c m b o = Some v).
  { intros c b o v L. destruct (Old b (load_valid_block _ _ _ _ _ L)) as (_ & _ & Loads).
    rewrite Loads. exact L. }
  assert (RepM : elements_null_data_output_rep m be 0 bt 0 bout 0 Int64.zero Int64.one true).
  { eapply C.jet_elements_null_data_layout.elements_null_data_output_rep_mono; eassumption. }
  assert (CountM : elements_null_data_count_path m be 0 bt 0 bout 0 Int64.zero Int64.one).
  { eapply C.jet_elements_null_data_layout.elements_null_data_count_path_mono; eassumption. }
  destruct (Old be VE) as (ED & EW & EL).
  destruct (Old bt VT) as (TD & TW & TL).
  destruct (Old bout VO) as (OD & OW & OL).
  assert (Sep : Forall (fun '(b,lo,hi) => out_sep bd 0 bw 0 261 261 b lo hi)
    (elements_null_data_count_footprint be 0 bt 0 bout 0 Int64.zero)).
  { unfold elements_null_data_count_footprint. constructor.
    - split; left; assumption.
    - constructor; [split;left;assumption|]. constructor; [split;left;assumption|constructor]. }
  destruct (overlap_public_runs_absent m bd bs bw be bt bout DB Source Input RepM CountM Sep Frame Word)
    as (mf & Call & Cells & Prefix & Fields & Outside).
  exists m,mf,bd,bs,bw,be,bt,bout.
  split; [exact Source|]. split; [exact Input|]. split.
  - apply input32_zero_in_shared_word; [lia|exact Word].
  - split; [exact Frame|]. split; [exact RepM|]. split; [exact CountM|]. split.
    + destruct Output as (P & C & F & Code). unfold overlap_output_fields.
      repeat split; apply Keep; assumption.
    + split; [repeat split; assumption|exact (conj Call (conj Cells Fields))].
Qed.
