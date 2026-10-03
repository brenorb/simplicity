(** Generic proof of the indexed scalar Bitcoin getters (input_value,
    input_sequence, output_value): [i = read32(src)], a bounds bit, then the
    element's scalar field through a 32- or 64-bit writer, or padding.  The
    consumer instantiates the element type, its size, the field offset, the
    abstract value and the generated statements. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_read_step C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_then.
Require Import C.jet_bitcoin_env_load.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Definition bitcoin_skip_stmt (nbits : Z) : statement :=
  Scall None
    (Evar _skipBits (Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default))
    [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr nbits) tint].

Definition indexed_scalar_result {A} (s : wide_size) (elems : list A)
    (specv : A -> Ty.tySem (Word (wide_log s))) (a : Ty.tySem Word32) :
    Ty.tySem (Ty.Sum Ty.Unit (Word (wide_log s))) :=
  match nth_error elems (Z.to_nat (toZ a)) with
  | Some x => inr (specv x)
  | None => inl tt
  end.

Lemma encode_indexed_inr s (w : Ty.tySem (Word (wide_log s))) :
  @encode (Ty.Sum Ty.Unit (Word (wide_log s))) (inr w) = Some true :: @encode (Word (wide_log s)) w.
Proof. reflexivity. Qed.

Lemma encode_indexed_inl s :
  @encode (Ty.Sum Ty.Unit (Word (wide_log s))) (inl tt) = Some false :: repeat None (Z.to_nat (wide_bits s)).
Proof. destruct s; vm_compute; reflexivity. Qed.

Lemma wide_bits_succ_frame s : 1 + wide_bits s = Z.of_nat (bitSize (Ty.Sum Ty.Unit (Word (wide_log s)))).
Proof. destruct s; reflexivity. Qed.

(** Linear arithmetic over a context reduced to its arithmetic facts: the full
    contexts of these proofs contain large semantic hypotheses that make lia
    exhaust the stack. *)
Ltac slia :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with
      | Prop =>
          lazymatch T with
          | @eq Z _ _ => fail
          | @eq nat _ _ => fail
          | le _ _ => fail
          | not (Z.lt _ _) => fail
          | not (Z.le _ _) => fail
          | lt _ _ => fail
          | Z.le _ _ => fail
          | Z.lt _ _ => fail
          | Z.ge _ _ => fail
          | Z.gt _ _ => fail
          | and (Z.le _ _) (Z.le _ _) => fail
          | and (Z.lt _ _) (Z.le _ _) => fail
          | and (Z.le _ _) (Z.lt _ _) => fail
          | _ => clear H
          end
      | _ => fail
      end
  end; lia.

Definition toZ32 (a : Ty.tySem Word32) : Z := toZ a.
Lemma toZ32_eq a : toZ32 a = toZ a. Proof. reflexivity. Qed.
Local Opaque toZ32.


Lemma bitcoin_cast_const nb m : 0 <= nb <= 64 ->
  sem_cast (Vint (Int.repr nb)) tint tulong m = Some (Vlong (Int64.repr nb)).
Proof.
  intros H. unfold sem_cast. simpl. unfold cast_int_long. rewrite Int.signed_repr; [reflexivity|].
  change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia.
Qed.

Lemma bitcoin_indexed_scalar_mid {A} (s : wide_size) (elems : list A) (valz : A -> Z)
    (specv : A -> Ty.tySem (Word (wide_log s)))
    (tp cp t3 t4 t5 countfield arrfield sid wid : ident) (cdelta adelta sz voff : Z) (ve : expr)
    (wf f : function)
    (Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> _t'2 /\ tp <> cp)
    (Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> _t'2)
    (Ht3i : t3 <> _i) (Ht3d : t3 <> _dst) (Ht4i : t4 <> _i) (Ht4d : t4 <> _dst) (Ht5d : t5 <> _dst)
    (Hwin : In (wid, wf) bitcoin_core_helpers) (Hwty : type_of_fundef (Internal wf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default)
    (Hwnone : forall bl, (bitcoin_version_locals bl)!wid = None) (Hwf : wf = wide_writer s)
    (Hcf : bitcoin_field_at _bitcoinTransaction countfield cdelta)
    (Haf : bitcoin_field_at _bitcoinTransaction arrfield adelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 488) (Hab : 0 <= adelta /\ adelta + 8 <= 488)
    (Hsz : 0 < sz <= 1000) (Hvoff : 0 <= voff /\ voff + 8 <= sz)
    (Hspec : forall x, decode_wide s (Int64.zero_ext (wide_bits s) (Int64.repr (valz x))) = specv x)
    (Hval : forall e le' m' bin inbase r v,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + voff + 8 <= Ptrofs.max_unsigned ->
      Mem.load Mint64 m' bin (inbase + sz * Int64.unsigned r + voff) = Some (Vlong v) ->
      eval_expr bitcoin_ge e le' m' ve (Vlong v))
    m bd dbase bs sbase bi bw edge outedge cursor read_cursor
    (a : Ty.tySem Word32) be ebase bt txbase bin inbase nI bytes :
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 488 <= Ptrofs.max_unsigned ->
  0 <= inbase -> inbase + sz * Z.of_nat (length elems) <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) ->
  Int64.unsigned nI = Z.of_nat (length elems) ->
  (forall j x, nth_error elems j = Some x ->
    Mem.load Mint64 m bin (inbase + sz * Z.of_nat j + voff) = Some (Vlong (Int64.repr (valz x)))) ->
  out_sep bd dbase bw outedge cursor (1 + wide_bits s) be ebase (ebase + 8) ->
  out_sep bd dbase bw outedge cursor (1 + wide_bits s) bt (txbase + adelta) (txbase + adelta + 8) ->
  out_sep bd dbase bw outedge cursor (1 + wide_bits s) bin inbase (inbase + sz * Z.of_nat (length elems)) ->
  frame_fields_at m bs sbase bi edge read_cursor ->
  0 <= read_cursor <= Int64.max_unsigned - 32 ->
  frame_input_word_at m bi edge read_cursor a ->
  write_frame_at m bd dbase bw outedge cursor (1 + wide_bits s) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  bitcoin_wrapper_mid f
    (bitcoin_indexed_rest tp cp countfield
      (bitcoin_indexed_then t3 t4 t5 arrfield sid ve wid) (bitcoin_skip_stmt (wide_bits s)))
    (encode (indexed_scalar_result s elems specv a)) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bw outedge cursor (1 + wide_bits s) bytes.
Proof.
  intros He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HLn HnI HLelem S1 S4 S5 HRF HRC HIn HFrame HBytes.
  pose proof (wide_bits_bounds s) as Hwb.
  unfold bitcoin_wrapper_mid. intros ma mc bl HAlloc HStore HLP HPP HFrameC.
  set (nn := Z.of_nat (length elems)) in *.
  set (szn := sz * nn) in *.
  assert (HVs : Mem.valid_block m bs).
  { eapply Mem.perm_valid_block. eapply (Mem.loadbytes_range_perm _ _ _ _ _ HBytes sbase); slia. }
  assert (HBa : Mem.loadbytes ma bs sbase 16 = Some bytes).
  { erewrite Mem.loadbytes_alloc_unchanged; eauto. }
  destruct (bitcoin_read_wide_step W32 m ma mc bl bs sbase bi edge read_cursor a bytes HRC HRF HIn
    HAlloc HBa HStore) as (mr & r & Hread & Hr & HRFields & HRMem & HRPerm & HRValid & HRLoads).
  assert (Hidx : Int64.unsigned r = toZ32 a) by exact Hr.
  clear Hr.
  pose proof HFrame as [HDB [[HDE HDO] [HEd [HN [HMx [HDW [PD HWords]]]]]]].
  destruct (write_frame_at_head m bd dbase bw outedge cursor (1 + wide_bits s) ltac:(slia) HFrame)
    as [_ [_ [_ [w0 Hw0]]]].
  assert (HLd : bl <> bd) by (eapply fresh_frame_not_loaded; eauto).
  assert (HLw : bl <> bw) by (eapply fresh_frame_not_loaded; eauto).
  assert (HFrameR : write_frame_at mr bd dbase bw outedge cursor (1 + wide_bits s)).
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
  destruct (bitcoin_writeBit_step mr bd dbase bw outedge cursor (Int64.ltu r nI) HF1)
    as (mb & Hwb1 & E1).
  assert (HF65 : write_frame_at mr bd dbase bw outedge cursor (1 + wide_bits s)) by exact HFrameR.
  assert (HFb : write_frame_at mb bd dbase bw outedge (cursor - 1) (wide_bits s)).
  { eapply write_frame_at_after_effect with (cells := [Some (Int64.ltu r nI)]);
      [reflexivity|slia|exact HF65|exact E1]. }
  assert (HLoadB : forall chunk b lo hi ofs, out_sep bd dbase bw outedge cursor (1 + wide_bits s) b lo hi ->
    lo <= ofs -> ofs + size_chunk chunk <= hi -> Mem.load chunk mb b ofs = Mem.load chunk mr b ofs).
  { intros chunk b lo hi ofs Hs Hlo Hhi.
    eapply write_effect_env_load with (bf := bd) (base := dbase) (bw := bw) (edge := outedge)
      (cursor := cursor) (cursor0 := cursor) (count0 := 1 + wide_bits s) (n := 1)
      (cells := [Some (Int64.ltu r nI)]) (lo := lo) (hi := hi);
      [slia|slia|slia|slia|exact E1|exact Hs|exact Hlo|exact Hhi]. }
  assert (Hr0 : 0 <= Int64.unsigned r) by apply Int64.unsigned_range.
  set (V := indexed_scalar_result s elems specv a).
  assert (HTotal : exists le1 me,
    Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc (bitcoin_indexed_rest tp cp countfield
        (bitcoin_indexed_then t3 t4 t5 arrfield sid ve wid) (bitcoin_skip_stmt (wide_bits s)))
      E0 le1 me bitcoin_returned_one /\
    write_effect mr me bd dbase bw outedge cursor (1 + wide_bits s) (encode V)).
  { refine (exec_bitcoin_indexed_rest tp cp Htp Hcp (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      countfield cdelta (bitcoin_indexed_then t3 t4 t5 arrfield sid ve wid)
      (bitcoin_skip_stmt (wide_bits s)) mc mr mb be ebase bt txbase bl bd dbase r nI
      (fun me => write_effect mr me bd dbase bw outedge cursor (1 + wide_bits s) (encode V))
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - unfold bitcoin_wrapper_temps. apply PTree.gss.
    - unfold bitcoin_wrapper_temps. rewrite PTree.gso by discriminate. rewrite PTree.gso by discriminate. apply PTree.gss.
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
      set (v := Int64.repr (valz x)).
      assert (Hm : sz * Int64.unsigned r + sz <= szn).
      { subst szn. assert (sz * (Int64.unsigned r + 1) <= sz * nn) by (apply Z.mul_le_mono_nonneg_l; slia). slia. }
      assert (HLv : Mem.load Mint64 mb bin (inbase + sz * Int64.unsigned r + voff) = Some (Vlong v)).
      { rewrite (HLoadB Mint64 bin inbase (inbase + sz * nn) (inbase + sz * Int64.unsigned r + voff)
          S5 ltac:(slia) ltac:(change (size_chunk Mint64) with 8; slia)).
        apply HRLoads. pose proof (HLelem _ _ Hnth) as H.
        rewrite Z2Nat.id in H by slia. exact H. }
      assert (Hmb0 : Mem.load Mptr mb be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase))).
      { rewrite (HLoadB Mptr be ebase (ebase + 8) (ebase + 0) S1 ltac:(slia) ltac:(change (size_chunk Mptr) with 8; slia)).
        exact HE0. }
      assert (Hmb1 : Mem.load Mptr mb bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase))).
      { rewrite (HLoadB Mptr bt (txbase + adelta) (txbase + adelta + 8) (txbase + adelta) S4 ltac:(slia)
          ltac:(change (size_chunk Mptr) with 8; slia)).
        exact HE1. }
      destruct (bitcoin_write_wide_step s mb bd dbase bw outedge (cursor - 1) v HFb)
        as (me & HCallW & E2).
      subst wf.
      destruct (exec_bitcoin_indexed_then (bitcoin_version_locals bl) le' t3 t4 t5 arrfield adelta sid
        ve wid (wide_writer s) mb me be ebase bt txbase bin inbase bd dbase r v
        Ht3i Ht3d Ht4i Ht4d Ht5d Hwin Hwty (Hwnone bl) He Hd Hi
        He0 ltac:(slia) Ht0 (proj1 Hab) ltac:(slia) Haf Hmb0 Hmb1
        (fun le'' H4 HI' => Hval _ le'' mb bin inbase r v H4 HI' Hi0 ltac:(slia) HLv) HCallW)
        as [le'' HExec].
      exists le'', me. split; [exact HExec|].
      pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 (wide_bits s) [Some (Int64.ltu r nI)]
        (encode (decode_wide s (Int64.zero_ext (wide_bits s) v))) eq_refl ltac:(slia) HF65 E1 E2) as Eseq.
      assert (Hcells : [Some (Int64.ltu r nI)] ++ encode (decode_wide s (Int64.zero_ext (wide_bits s) v)) =
        encode V).
      { unfold V, indexed_scalar_result. rewrite toZ32_eq in Hidx. rewrite <- Hidx. rewrite Hnth. rewrite Hb.
        rewrite encode_indexed_inr. subst v. rewrite (Hspec x). reflexivity. }
      exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor (1 + wide_bits s) c) Eseq _ Hcells).
    - (* failure branch *)
      intros le' Hi Hd He Hb.
      assert (Hge : nn <= Int64.unsigned r).
      { unfold Int64.ltu in Hb.
        destruct (zlt (Int64.unsigned r) (Int64.unsigned nI)) as [Hl|Hnl]; [discriminate|].
        rewrite HnI in Hnl. slia. }
      assert (Hnth : nth_error elems (Z.to_nat (Int64.unsigned r)) = None).
      { apply nth_error_None. subst nn. slia. }
      assert (HFb' : write_frame_at mb bd dbase bw outedge (cursor - 1) (Z.of_nat (Z.to_nat (wide_bits s)))).
      { rewrite Z2Nat.id by slia. exact HFb. }
      destruct (bitcoin_skipBits_step mb bd dbase bw outedge (cursor - 1) (Z.to_nat (wide_bits s)) HFb')
        as (me & HCallS & E2).
      exists le', me. split.
      + unfold bitcoin_skip_stmt.
        assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) le' mb
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr (wide_bits s)) tint]
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
          [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat (Z.to_nat (wide_bits s))))]).
        { eapply eval_Econs; [apply eval_Etempvar; exact Hd|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
          rewrite Z2Nat.id by slia. apply bitcoin_cast_const; slia. }
        exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) le' mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me ltac:(helper_in) ltac:(reflexivity) Hargs ltac:(reflexivity) HCallS).
      + pose proof (write_effect_seq mr mb me bd dbase bw outedge cursor 1 (wide_bits s) [Some (Int64.ltu r nI)]
          (repeat None (Z.to_nat (wide_bits s))) eq_refl ltac:(slia) HF65 E1) as Eseq.
        assert (E2' : write_effect mb me bd dbase bw outedge (cursor - 1) (wide_bits s)
          (repeat None (Z.to_nat (wide_bits s)))).
        { rewrite <- (Z2Nat.id (wide_bits s)) at 1 by slia. exact E2. }
        specialize (Eseq E2').
        assert (Hcells : [Some (Int64.ltu r nI)] ++ repeat None (Z.to_nat (wide_bits s)) = encode V).
        { unfold V, indexed_scalar_result. rewrite toZ32_eq in Hidx. rewrite <- Hidx. rewrite Hnth. rewrite Hb.
          rewrite encode_indexed_inl. reflexivity. }
        exact (eq_rect _ (fun c => write_effect mr me bd dbase bw outedge cursor (1 + wide_bits s) c) Eseq _ Hcells). }
  destruct HTotal as (le1 & me & HEx & HEff).
  destruct (write_effect_lift mc mr me bl bd dbase bw outedge cursor (1 + wide_bits s) (encode V) HLd HLw
    HRMem HRPerm HRValid HEff) as (c & p & fl & l & pm & vv).
  exists le1, me. refine (conj HEx (conj c (conj p (conj fl (conj l (conj pm vv)))))).
Qed.

Definition indexed_scalar_rep {A} (elems_of : Bitcoin.env -> list A) (valz : A -> Z)
    (sz voff adelta cdelta : Z) (m : mem) (env : val) (environment : Bitcoin.env)
    (fp : list (block * Z * Z)) : Prop :=
  exists be ebase bt txbase bin inbase nI,
    env = Vptr be (Ptrofs.repr ebase) /\
    0 <= ebase /\ ebase + 56 <= Ptrofs.max_unsigned /\
    0 <= txbase /\ txbase + 488 <= Ptrofs.max_unsigned /\
    0 <= inbase /\ inbase + sz * Z.of_nat (length (elems_of environment)) <= Ptrofs.max_unsigned /\
    Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) /\
    Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) /\
    Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) /\
    Int64.unsigned nI = Z.of_nat (length (elems_of environment)) /\
    (forall j x, nth_error (elems_of environment) j = Some x ->
      Mem.load Mint64 m bin (inbase + sz * Z.of_nat j + voff) = Some (Vlong (Int64.repr (valz x)))) /\
    fp = [(be, ebase, ebase + 8); (bt, txbase + adelta, txbase + adelta + 8);
          (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))].

Theorem bitcoin_indexed_scalar_local {A} (s : wide_size) (elems_of : Bitcoin.env -> list A) (valz : A -> Z)
    (specv : A -> Ty.tySem (Word (wide_log s)))
    (tp cp t3 t4 t5 countfield arrfield sid wid : ident) (cdelta adelta sz voff : Z) (ve : expr)
    (wf f : function)
    (Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> _t'2 /\ tp <> cp)
    (Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> _t'2)
    (Ht3i : t3 <> _i) (Ht3d : t3 <> _dst) (Ht4i : t4 <> _i) (Ht4d : t4 <> _dst) (Ht5d : t5 <> _dst)
    (Hwin : In (wid, wf) bitcoin_core_helpers) (Hwty : type_of_fundef (Internal wf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil)) tvoid cc_default)
    (Hwnone : forall bl, (bitcoin_version_locals bl)!wid = None) (Hwf : wf = wide_writer s)
    (Hcf : bitcoin_field_at _bitcoinTransaction countfield cdelta)
    (Haf : bitcoin_field_at _bitcoinTransaction arrfield adelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 488) (Hab : 0 <= adelta /\ adelta + 8 <= 488)
    (Hsz : 0 < sz <= 1000) (Hvoff : 0 <= voff /\ voff + 8 <= sz)
    (Hspec : forall x, decode_wide s (Int64.zero_ext (wide_bits s) (Int64.repr (valz x))) = specv x)
    (Hval : forall e le' m' bin inbase r v,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + voff + 8 <= Ptrofs.max_unsigned ->
      Mem.load Mint64 m' bin (inbase + sz * Int64.unsigned r + voff) = Some (Vlong v) ->
      eval_expr bitcoin_ge e le' m' ve (Vlong v))
    (Hshape : bitcoin_wrapper_shape f
      (bitcoin_indexed_rest tp cp countfield
        (bitcoin_indexed_then t3 t4 t5 arrfield sid ve wid) (bitcoin_skip_stmt (wide_bits s))))
    (spec : Ty.tySem Word32 -> Bitcoin.env -> option (Ty.tySem (Ty.Sum Ty.Unit (Word (wide_log s)))))
    (Hsem : forall a environment,
      spec a environment = Some (indexed_scalar_result s (elems_of environment) specv a)) :
  application_jet_local_spec_sep f bitcoin_ge Bitcoin.env Word32 (Ty.Sum Ty.Unit (Word (wide_log s)))
    (indexed_scalar_rep elems_of valz sz voff adelta cdelta) spec.
Proof.
  intros environment env m bd dbase bs sbase bi bw edge outedge cursor read_cursor a fp
    (be & ebase & bt & txbase & bin & inbase & nI & HEnvVal & He0 & He1 & Ht0 & Ht1 & Hi0 & Hi1 &
      HLtx & HLin & HLn & HnI & HLelem & HFp)
    HSep HB HA [HSedge HSoff] HR0 HRmax Hin HFrame.
  subst env fp.
  pose proof (wide_bits_bounds s) as Hwb.
  assert (HC : Z.of_nat (bitSize (Ty.Sum Ty.Unit (Word (wide_log s)))) = 1 + wide_bits s)
    by (symmetry; apply wide_bits_succ_frame).
  assert (HCA : Z.of_nat (bitSize Word32) = 32) by reflexivity.
  rewrite HC in HSep, HFrame. rewrite HCA in HRmax.
  rewrite Forall_forall in HSep.
  assert (S1 : out_sep bd dbase bw outedge cursor (1 + wide_bits s) be ebase (ebase + 8))
    by exact (HSep (be, ebase, ebase + 8) ltac:(simpl; auto)).
  assert (S4 : out_sep bd dbase bw outedge cursor (1 + wide_bits s) bt (txbase + adelta) (txbase + adelta + 8))
    by exact (HSep (bt, txbase + adelta, txbase + adelta + 8) ltac:(simpl; auto)).
  assert (S5 : out_sep bd dbase bw outedge cursor (1 + wide_bits s) bin inbase
    (inbase + sz * Z.of_nat (length (elems_of environment))))
    by exact (HSep (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment))) ltac:(simpl; auto)).
  apply frame_input_word_at_encode in Hin.
  destruct (frame_loadbytes_at m bs sbase (Vptr bi (Ptrofs.repr edge))
      (Vlong (Int64.repr read_cursor)) HSedge HSoff) as [bytes HBytes].
  destruct (bitcoin_wrapper_layout f
    (bitcoin_indexed_rest tp cp countfield
      (bitcoin_indexed_then t3 t4 t5 arrfield sid ve wid) (bitcoin_skip_stmt (wide_bits s)))
    (encode (indexed_scalar_result s (elems_of environment) specv a)) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs
    sbase bw outedge cursor (1 + wide_bits s) bytes Hshape HB HA HBytes ltac:(slia) HFrame
    (bitcoin_indexed_scalar_mid s (elems_of environment) valz specv tp cp t3 t4 t5 countfield arrfield sid wid
      cdelta adelta sz voff ve wf f Htp Hcp Ht3i Ht3d Ht4i Ht4d Ht5d Hwin Hwty Hwnone Hwf Hcf Haf Hcb Hab
      Hsz Hvoff Hspec Hval m bd dbase bs sbase bi bw edge outedge cursor read_cursor a be ebase bt txbase
      bin inbase nI bytes He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HLn HnI HLelem S1 S4 S5 (conj HSedge HSoff)
      ltac:(slia) Hin HFrame HBytes))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, (indexed_scalar_result s (elems_of environment) specv a). split.
  - apply Hsem.
  - split; [exact HCall|]. split; [exact HCells|]. split; [exact HPrefix|].
    rewrite HC. split; [exact HFields|]. exact HMem.
Qed.
