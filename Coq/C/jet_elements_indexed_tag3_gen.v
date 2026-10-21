(** Proof-support instance of the existing indexed skeleton with the outer
    bounds bit in temporary t'3. This does not replace any C implementation.
    Its consumer must prove the unchanged generated function has this shape. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine C.jet_elements_prim.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jets_elements C.jet_elements_linkage C.jet_elements_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_elements_field_eval C.jet_elements_effects C.jet_elements_wrapper.
Require Import C.jet_elements_transport C.jet_elements_call C.jet_elements_read_step C.jet_elements_steps.
Require Import C.jet_elements_index_eval C.jet_elements_indexed_exec C.jet_elements_indexed_ptr_then.
Require Import C.jet_elements_env_load C.jet_elements_indexed_scalar C.jet_elements_indexed_ptr.
Require Import C.jet_elements_indexed_tag3_exec.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque elements_ge ge0.
Set Default Timeout 60.

Lemma elements_indexed_gen_mid_tag3 {A} (elems : list A) (nbits : Z) (pcells : A -> list Cell)
    (elemrep : mem -> block -> Z -> A -> Prop)
    (tp cp countfield : ident) (cdelta adelta sz : Z) (then_s : statement) (f : function)
    (Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> _t'3 /\ tp <> cp)
    (Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> _t'3)
    (Hnb : 1 <= nbits <= 1000) (Hlen : forall x, Z.of_nat (length (pcells x)) = nbits)
    (Hcf : elements_field_at _elementsTransaction countfield cdelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 760) (Hab : 0 <= adelta /\ adelta + 8 <= 760)
    (Hsz : 0 < sz <= 1000)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + sz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    bd dbase bw outedge
    (Hthen : forall bl le' mb x be ebase bt txbase bin inbase r cur,
      le'!_i = Some (Vlong r) -> le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
      le'!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
      0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
      0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
      Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
      elemrep mb bin (inbase + sz * Int64.unsigned r) x ->
      out_sep bd dbase bw outedge cur nbits be ebase (ebase + 8) ->
      out_sep bd dbase bw outedge cur nbits bt (txbase + adelta) (txbase + adelta + 8) ->
      out_sep bd dbase bw outedge cur nbits bin (inbase + sz * Int64.unsigned r)
        (inbase + sz * Int64.unsigned r + sz) ->
      write_frame_at mb bd dbase bw outedge cur nbits ->
      exists le'' me,
        Clight2.exec_stmt elements_ge (elements_version_locals bl) le' mb then_s E0 le'' me Out_normal /\
        write_effect mb me bd dbase bw outedge cur nbits (pcells x))
    m bs sbase bi edge cursor read_cursor
    (a : Ty.tySem Word32) be ebase bt txbase bin inbase nI bytes :
  0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
  0 <= inbase -> inbase + sz * Z.of_nat (length elems) <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) ->
  Int64.unsigned nI = Z.of_nat (length elems) ->
  (forall j x, nth_error elems j = Some x -> elemrep m bin (inbase + sz * Z.of_nat j) x) ->
  out_sep bd dbase bw outedge cursor (1 + nbits) be ebase (ebase + 8) ->
  out_sep bd dbase bw outedge cursor (1 + nbits) bt (txbase + adelta) (txbase + adelta + 8) ->
  out_sep bd dbase bw outedge cursor (1 + nbits) bin inbase (inbase + sz * Z.of_nat (length elems)) ->
  frame_fields_at m bs sbase bi edge read_cursor ->
  0 <= read_cursor <= Int64.max_unsigned - 32 ->
  frame_input_word_at m bi edge read_cursor a ->
  write_frame_at m bd dbase bw outedge cursor (1 + nbits) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  elements_wrapper_mid f
    (elements_indexed_rest_tag3 tp cp countfield
      then_s (elements_skip_stmt nbits))
    (indexed_ptr_cells elems nbits pcells a) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bw outedge cursor (1 + nbits) bytes.
Proof.
  intros He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HLn HnI HLelem S1 S4 S5 HRF HRC HIn HFrame HBytes.
  pose proof Hnb as Hwb.
  unfold elements_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
  set (nn := Z.of_nat (length elems)) in *.
  set (szn := sz * nn) in *.
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HBytes sbase); slia. }
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  destruct (elements_read_wide_step W32 m ma mc bl bs sbase bi edge read_cursor a bytes HRC HRF HIn
    HAlloc HBa HStore) as (mr & r & Hread & Hr & HRFields & HRMem & HRPerm & HRValid & HRLoads).
  assert (Hidx : Int64.unsigned r = toZ32 a) by exact Hr.
  clear Hr.
  pose proof HFrame as [HDB [[HDE HDO] [HEd [HN [HMx [PD HWords]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (1 + nbits) ltac:(slia) HFrame)
    as [_ [_ [_ [w0 Hw0]]]].
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor (1 + nbits)).
  { eapply write_frame_at_preserved with (m := mc).
    - intros chunk b ofs v Hb HL. rewrite HRMem; [exact HL|].
      destruct Hb; subst; auto.
    - exact HRPerm.
    - exact HFrameC. }
  assert (HE0 : Mem.load Mptr mr be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))) by (apply HRLoads; exact HLtx).
  assert (HE1 : Mem.load Mptr mr bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase))) by (apply HRLoads; exact HLin).
  assert (HE2 : Mem.load Mint64 mr bt (txbase + cdelta) = Some (Vlong nI)) by (apply HRLoads; exact HLn).
  assert (HF1 : write_frame_at mr bd dbase bw outedge cursor 1).
  { eapply write_frame_at_shorter; [|exact HFrameR]. slia. }
  destruct (elements_writeBit_step mr bd dbase bw outedge cursor (Int64.ltu r nI) HF1)
    as (mb & Hwb1 & E1).
  assert (HF65 : write_frame_at mr bd dbase bw outedge cursor (1 + nbits)) by exact HFrameR.
  assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) nbits).
  { eapply write_frame_at_after_effect with (cells := [Some (Int64.ltu r nI)]);
      [reflexivity|slia|exact HF65|exact E1]. }
  assert (HLoadB : forall chunk b lo hi ofs, out_sep bd dbase bw outedge cursor (1 + nbits) b lo hi ->
    lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b ofs = Mem.load chunk mr b ofs).
  { intros chunk b lo hi ofs Hs Hlo Hhi.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 1 + nbits) (n := 1)
      (cells := [Some (Int64.ltu r nI)]) (lo := lo) (hi := hi);
      [slia|slia|slia|slia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  set (V := indexed_ptr_cells elems nbits pcells a).
  assert (HTotal : exists le1 me,
    Clight2.exec_stmt elements_ge (elements_version_locals bl)
      (elements_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc (elements_indexed_rest_tag3 tp cp countfield
        then_s (elements_skip_stmt nbits))
      E0 le1 me elements_returned_one /\
    write_effect mr me bd dbase bw outedge cursor (1 + nbits) V).
  { refine (exec_elements_indexed_rest_tag3 tp cp Htp Hcp (elements_version_locals bl)
      (elements_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      countfield cdelta then_s
      (elements_skip_stmt nbits) mc mr mb be ebase bt txbase bl bd dbase r nI
      (fun me => write_effect mr me bd dbase bw outedge cursor (1 + nbits) V)
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold elements_wrapper_temps. apply PTree.gss.
    - unfold elements_wrapper_temps. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. apply PTree.gss.
    - exact Hread.
    - exact He0.
    - clear - He1; slia.
    - exact Ht0.
    - exact (proj1 Hcb).
    - clear - Ht1 Hcb; slia.
    - exact Hcf.
    - exact HE0.
    - exact HE2.
    - exact Hwb1.
    - (* success branch *)
      intros le' Hi Hd He Hb.
      assert (Hlt : Int64.unsigned r < nn).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [|discriminate].
        rewrite HnI in Hl. exact Hl. }
      destruct (nth_error elems (Z.to_nat (Int64.unsigned r))) as [x|] eqn:Hnth;
        [|apply nth_error_None in Hnth; subst nn; slia].
      assert (Hm : sz * Int64.unsigned r + sz <= szn).
      { subst szn. assert (sz * (Int64.unsigned r + 1) <= sz * nn) by (apply Z.mul_le_mono_nonneg_l; slia). slia. }
      assert (Hs0 : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; slia).
      set (ofs := inbase + sz * Int64.unsigned r).
      assert (Hrep : elemrep m bin ofs x).
      { pose proof (HLelem _ _ Hnth) as H. rewrite Z2Nat.id in H by slia. exact H. }
      assert (Hrepb : elemrep mb bin ofs x).
      { eapply Hpres; [exact Hrep|].
        intros chunk o v Hlo Hhi Hl.
        rewrite (HLoadB chunk bin inbase (inbase + sz * nn) o S5 ltac:(slia) ltac:(slia)).
        apply HRLoads. exact Hl. }
      assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
      { rewrite (HLoadB Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(slia) ltac:(change (size_chunk Mptr) with 8; slia)).
        exact HE0. }
      assert (Hmb1 : Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase))).
      { rewrite (HLoadB Mptr bt (txbase + adelta) (txbase + adelta + 8) (txbase + adelta) S4 ltac:(slia)
          ltac:(change (size_chunk Mptr) with 8; slia)).
        exact HE1. }
      assert (HSp : out_sep bd dbase bw outedge (cursor - 1) nbits bin ofs (ofs + sz)).
      { eapply out_sep_range with (lo := inbase) (hi := inbase + sz * nn); [|slia|slia].
        eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S5]. }
      assert (HS1' : out_sep bd dbase bw outedge (cursor - 1) nbits be ebase (ebase + 8)).
      { eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S1]. }
      assert (HS4' : out_sep bd dbase bw outedge (cursor - 1) nbits bt (txbase + adelta) (txbase + adelta + 8)).
      { eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S4]. }
      destruct (Hthen bl le' mb x be ebase bt txbase bin inbase r (cursor - 1) Hi Hd He
        He0 He1 Ht0 Ht1 Hi0 ltac:(slia) Hmb0 Hmb1 Hrepb HS1' HS4' HSp HFb) as (le'' & me & HExec & E2).
      exists le'', me. split; [exact HExec|].
      pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 nbits [Some (Int64.ltu r nI)]
        (pcells x) eq_refl ltac:(slia) HF65 E1 E2) as Eseq.
      assert (Hcells : [Some (Int64.ltu r nI)] ++ pcells x = V).
      { unfold V, indexed_ptr_cells. rewrite <- Hidx. rewrite Hnth. rewrite Hb. reflexivity. }
      exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor (1 + nbits) c) Eseq _ Hcells).
    - (* failure branch *)
      intros le' Hi Hd He Hb.
      assert (Hge : nn <= Int64.unsigned r).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [discriminate|].
        rewrite HnI in Hnl. slia. }
      assert (Hnth : nth_error elems (Z.to_nat (Int64.unsigned r)) = None).
      { apply nth_error_None. subst nn. slia. }
      assert (HFb' : write_frame_at mb bd dbase bw outedge (cursor - 1) (Z.of_nat (Z.to_nat nbits))).
      { rewrite Z2Nat.id by slia. exact HFb. }
      destruct (elements_skipBits_step mb bd dbase bw outedge (cursor - 1) (Z.to_nat nbits) HFb')
        as (me & HCallS & E2).
      exists le', me. split.
      + unfold elements_skip_stmt.
        assert (Hargs : eval_exprlist elements_ge (elements_version_locals bl) le' mb
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr nbits) tint]
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
          [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat (Z.to_nat nbits)))]).
        { eapply eval_Econs; [apply eval_Etempvar; exact Hd|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
          rewrite Z2Nat.id by slia. apply elements_cast_const'; slia. }
        exact (exec_elements_helper_call (elements_version_locals bl) le' mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me ltac:(helper_in_tag3) ltac:(reflexivity) Hargs ltac:(reflexivity) HCallS).
      + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 nbits [Some (Int64.ltu r nI)]
          (repeat None (Z.to_nat nbits)) eq_refl ltac:(slia) HF65 E1) as Eseq.
        assert (E2' : write_effect mb me bd dbase bw outedge (cursor - 1) nbits
          (repeat None (Z.to_nat nbits))).
        { rewrite <- (Z2Nat.id nbits) at 1 by slia. exact E2. }
        specialize (Eseq E2').
        assert (Hcells : [Some (Int64.ltu r nI)] ++ repeat None (Z.to_nat nbits) = V).
        { unfold V, indexed_ptr_cells. rewrite <- Hidx. rewrite Hnth. rewrite Hb. reflexivity. }
        exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor (1 + nbits) c) Eseq _ Hcells). }
  destruct HTotal as (le1 & me & HEx & HEff).
  destruct (write_effect_lift mc mr me bl bd dbase bw outedge cursor (1 + nbits) V HLd HLw
    HRMem HRPerm HRValid HEff) as (c & p & fl & l & pm & vv).
  exists le1, me. refine (conj HEx (conj c (conj p (conj fl (conj l (conj pm vv)))))).
Qed.

Theorem elements_indexed_gen_local_tag3 {E : Set} {A} (elems_of : E -> list A) (nbits : Z) (pcells : A -> list Cell)
    (elemrep : mem -> block -> Z -> A -> Prop) (Bpay : Ty)
    (tp cp countfield : ident) (cdelta adelta sz : Z) (then_s : statement) (f : function)
    (Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> _t'3 /\ tp <> cp)
    (Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> _t'3)
    (Hnb : 1 <= nbits <= 1000) (Hlen : forall x, Z.of_nat (length (pcells x)) = nbits)
    (Hcf : elements_field_at _elementsTransaction countfield cdelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 760) (Hab : 0 <= adelta /\ adelta + 8 <= 760)
    (Hsz : 0 < sz <= 1000)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + sz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    (Hthen : forall bd dbase bw outedge, forall bl le' mb x be ebase bt txbase bin inbase r cur,
      le'!_i = Some (Vlong r) -> le'!_dst = Some (Vptr bd (Ptrofs.repr dbase)) ->
      le'!_env = Some (Vptr be (Ptrofs.repr ebase)) ->
      0 <= ebase -> ebase + 88 <= Ptrofs.max_unsigned ->
      0 <= txbase -> txbase + 760 <= Ptrofs.max_unsigned ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + sz <= Ptrofs.max_unsigned ->
      Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
      Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
      elemrep mb bin (inbase + sz * Int64.unsigned r) x ->
      out_sep bd dbase bw outedge cur nbits be ebase (ebase + 8) ->
      out_sep bd dbase bw outedge cur nbits bt (txbase + adelta) (txbase + adelta + 8) ->
      out_sep bd dbase bw outedge cur nbits bin (inbase + sz * Int64.unsigned r)
        (inbase + sz * Int64.unsigned r + sz) ->
      write_frame_at mb bd dbase bw outedge cur nbits ->
      exists le'' me,
        Clight2.exec_stmt elements_ge (elements_version_locals bl) le' mb then_s E0 le'' me Out_normal /\
        write_effect mb me bd dbase bw outedge cur nbits (pcells x))
    (Hshape : elements_wrapper_shape f
      (elements_indexed_rest_tag3 tp cp countfield
        then_s (elements_skip_stmt nbits)))
    (HB : Z.of_nat (bitSize (Ty.Sum Ty.Unit Bpay)) = 1 + nbits)
    (spec : Ty.tySem Word32 -> E -> option (Ty.tySem (Ty.Sum Ty.Unit Bpay)))
    (Hsem : forall a environment, exists V, spec a environment = Some V /\
      encode V = indexed_ptr_cells (elems_of environment) nbits pcells a) :
  application_jet_local_spec_sep f elements_ge E Word32 (Ty.Sum Ty.Unit Bpay)
    (indexed_ptr_rep elems_of elemrep sz 0 adelta cdelta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    (be & ebase & bt & txbase & bin & inbase & nI & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HnI & HLelem & HFp)
    HSep HBf HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  pose proof Hnb as Hwb.
  rewrite HB in HSep, HFrame.
  assert (HCA : Z.of_nat (bitSize Word32) = 32) by reflexivity.
  rewrite HCA in HRmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor (1 + nbits) be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor (1 + nbits) bt (txbase + adelta) (txbase + adelta + 8))
    by exact (HSep (bt, txbase + adelta, txbase + adelta + 8) ltac:(simpl; auto)).
  assert (S5 : out_sep bd dbase bw outedge cursor (1 + nbits) bin inbase
    (inbase + sz * Z.of_nat (length (elems_of environment))))
    by exact (HSep (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment))) ltac:(simpl; auto)).
  apply frame_input_word_at_encode in Hin.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  destruct (Hsem a environment) as (V & HVs & HVenc).
  destruct (elements_wrapper_layout f
    (elements_indexed_rest_tag3 tp cp countfield
      then_s (elements_skip_stmt nbits))
    (indexed_ptr_cells (elems_of environment) nbits pcells a) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs
    sbase bw outedge cursor (1 + nbits) bytes Hshape HBf HA HBytes ltac:(slia) HFrame
    (elements_indexed_gen_mid_tag3 (elems_of environment) nbits pcells elemrep tp cp countfield
      cdelta adelta sz then_s f Htp Hcp Hnb Hlen
      Hcf Hcb Hab Hsz Hpres bd dbase bw outedge (Hthen bd dbase bw outedge)
      m bs sbase bi edge cursor read_cursor a be ebase bt txbase bin inbase nI bytes He0 He1 Ht0 Ht1 Hi0 Hi1
      HLtx HLin HLn HnI (fun j x Hj => eq_rect _ (fun o => elemrep m bin o x) (HLelem j x Hj) _ (Z.add_0_r _)) S1 S4 S5 (conj HSedge HSoff) ltac:(slia) Hin HFrame HBytes))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, V. split; [exact HVs|].
  split; [exact HCall|]. split; [rewrite HVenc; exact HCells|]. split; [exact HPrefix|].
  rewrite HB. split; [exact HFields|]. exact HMem.
Qed.
