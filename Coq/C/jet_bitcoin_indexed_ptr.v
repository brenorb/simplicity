(** Generic proof of the indexed Bitcoin getters whose payload is written by a
    pointer-taking Bitcoin helper (writeHash, prevOutpoint): [i = read32(src)],
    a bounds bit, then the helper applied to the selected element's payload
    structure, or padding.  The consumer supplies the payload representation,
    its cells and the helper's layout contract. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Memory Maps Errors Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.BitMachine Simplicity.Primitive.Bitcoin.
Require Import C.jet_application_sep C.jet_frame_copy C.jet_frame_copy_layout C.jet_bitmachine_rep.
Require Import C.jet_frame_layout C.jet_write_layout C.jet_output_layout C.jet_output_slice.
Require Import C.jet_wide C.jet_wide_spec C.jet_encoding C.jet_input_layout C.jet_output_layout_step.
Require Import C.jets_bitcoin C.jet_bitcoin_linkage C.jet_bitcoin_version_exec C.jet_exec.
Require C.jets.
Require Import C.jet_bitcoin_field_eval C.jet_bitcoin_effects C.jet_bitcoin_wrapper.
Require Import C.jet_bitcoin_transport C.jet_bitcoin_call C.jet_bitcoin_read_step C.jet_bitcoin_steps.
Require Import C.jet_bitcoin_index_eval C.jet_bitcoin_indexed_exec C.jet_bitcoin_indexed_ptr_then.
Require Import C.jet_bitcoin_env_load C.jet_bitcoin_indexed_scalar.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Local Opaque bitcoin_ge ge0.
Set Default Timeout 60.

Lemma out_sep_range bf base bw edge cursor count b lo hi lo' hi' :
  out_sep bf base bw edge cursor count b lo hi -> lo <= lo' -> hi' <= hi ->
  out_sep bf base bw edge cursor count b lo' hi'.
Proof.
  intros [Hf Hw] H1 H2. split.
  - destruct Hf as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
  - destruct Hw as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
Qed.

Definition indexed_ptr_cells {A} (elems : list A) (nbits : Z) (pcells : A -> list Cell) (a : Ty.tySem Word32) : list Cell :=
  match nth_error elems (Z.to_nat (toZ32 a)) with
  | Some x => Some true :: pcells x
  | None => Some false :: repeat None (Z.to_nat nbits)
  end.

Definition indexed_ptr_rep {E : Set} {A} (elems_of : E -> list A) (elemrep : mem -> block -> Z -> A -> Prop)
    (sz poff adelta cdelta : Z) (m : mem) (env : val) (environment : E)
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
      elemrep m bin (inbase + sz * Z.of_nat j + poff) x) /\
    fp = [(be, ebase, ebase + 8); (bt, txbase + adelta, txbase + adelta + 8);
          (bin, inbase, inbase + sz * Z.of_nat (length (elems_of environment)))].

Lemma bitcoin_cast_const' nb m : 0 <= nb <= 1000 ->
  sem_cast (Vint (Int.repr nb)) tint tulong m = Some (Vlong (Int64.repr nb)).
Proof.
  intros H. unfold sem_cast. simpl. unfold cast_int_long. rewrite Int.signed_repr; [reflexivity|].
  change Int.min_signed with (-2147483648). change Int.max_signed with 2147483647. lia.
Qed.

Lemma bitcoin_indexed_ptr_mid {A} (elems : list A) (nbits : Z) (pcells : A -> list Cell)
    (elemrep : mem -> block -> Z -> A -> Prop)
    (tp cp t3 t4 countfield arrfield sid cid : ident) (pt : type)
    (cdelta adelta sz poff psz : Z) (pexpr : expr) (cf f : function)
    (Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> _t'2 /\ tp <> cp)
    (Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> _t'2)
    (Ht3i : t3 <> _i) (Ht3d : t3 <> _dst) (Ht4i : t4 <> _i) (Ht4d : t4 <> _dst)
    (Hnb : 1 <= nbits <= 1000) (Hlen : forall x, Z.of_nat (length (pcells x)) = nbits)
    (Hpty : typeof pexpr = tptr pt)
    (Hnone : forall bl, (bitcoin_version_locals bl)!cid = None)
    (Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) cid = Some (bitcoin_symbol_block cid))
    (Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block cid) Ptrofs.zero) =
      Some (Internal cf))
    (Hty : type_of_fundef (Internal cf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default)
    (Hcf : bitcoin_field_at _bitcoinTransaction countfield cdelta)
    (Haf : bitcoin_field_at _bitcoinTransaction arrfield adelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 488) (Hab : 0 <= adelta /\ adelta + 8 <= 488)
    (Hsz : 0 < sz <= 1000) (Hpoff : 0 <= poff /\ poff + psz <= sz)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + psz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    bd dbase bw outedge
    (Hpay : forall m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs -> ofs + psz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur nbits bin ofs (ofs + psz) ->
      write_frame_at m' bd dbase bw outedge cur nbits ->
      exists me, Clight2.eval_funcall bitcoin_ge m' (Internal cf)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
        write_effect m' me bd dbase bw outedge cur nbits (pcells x))
    (Hptr : forall e le' m' bin inbase r,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + poff + psz <= Ptrofs.max_unsigned ->
      eval_expr bitcoin_ge e le' m' pexpr (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poff))))
    m bs sbase bi edge cursor read_cursor
    (a : Ty.tySem Word32) be ebase bt txbase bin inbase nI bytes :
  0 <= ebase -> ebase + 56 <= Ptrofs.max_unsigned ->
  0 <= txbase -> txbase + 488 <= Ptrofs.max_unsigned ->
  0 <= inbase -> inbase + sz * Z.of_nat (length elems) <= Ptrofs.max_unsigned ->
  Mem.load Mptr m be (ebase + 0) = Some (Vptr bt (Ptrofs.repr txbase)) ->
  Mem.load Mptr m bt (txbase + adelta) = Some (Vptr bin (Ptrofs.repr inbase)) ->
  Mem.load Mint64 m bt (txbase + cdelta) = Some (Vlong nI) ->
  Int64.unsigned nI = Z.of_nat (length elems) ->
  (forall j x, nth_error elems j = Some x -> elemrep m bin (inbase + sz * Z.of_nat j + poff) x) ->
  out_sep bd dbase bw outedge cursor (1 + nbits) be ebase (ebase + 8) ->
  out_sep bd dbase bw outedge cursor (1 + nbits) bt (txbase + adelta) (txbase + adelta + 8) ->
  out_sep bd dbase bw outedge cursor (1 + nbits) bin inbase (inbase + sz * Z.of_nat (length elems)) ->
  frame_fields_at m bs sbase bi edge read_cursor ->
  0 <= read_cursor <= Int64.max_unsigned - 32 ->
  frame_input_word_at m bi edge read_cursor a ->
  write_frame_at m bd dbase bw outedge cursor (1 + nbits) ->
  Mem.loadbytes m bs sbase 16 = Some bytes ->
  bitcoin_wrapper_mid f
    (bitcoin_indexed_rest tp cp countfield
      (bitcoin_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt) (bitcoin_skip_stmt nbits))
    (indexed_ptr_cells elems nbits pcells a) (Vptr be (Ptrofs.repr ebase))
    m bd dbase bs sbase bw outedge cursor (1 + nbits) bytes.
Proof.
  intros He0 He1 Ht0 Ht1 Hi0 Hi1 HLtx HLin HLn HnI HLelem S1 S4 S5 HRF HRC HIn HFrame HBytes.
  pose proof Hnb as Hwb.
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
  destruct (bitcoin_writeBit_step mr bd dbase bw outedge cursor (Int64.ltu r nI) HF1)
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
    Clight2.exec_stmt bitcoin_ge (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      mc (bitcoin_indexed_rest tp cp countfield
        (bitcoin_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt) (bitcoin_skip_stmt nbits))
      E0 le1 me bitcoin_returned_one /\
    write_effect mr me bd dbase bw outedge cursor (1 + nbits) V).
  { refine (exec_bitcoin_indexed_rest tp cp Htp Hcp (bitcoin_version_locals bl)
      (bitcoin_wrapper_temps f (Vptr be (Ptrofs.repr ebase)) bd dbase bs sbase)
      countfield cdelta (bitcoin_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt)
      (bitcoin_skip_stmt nbits) mc mr mb be ebase bt txbase bl bd dbase r nI
      (fun me => write_effect mr me bd dbase bw outedge cursor (1 + nbits) V)
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
      assert (Hm : sz * Int64.unsigned r + sz <= szn).
      { subst szn. assert (sz * (Int64.unsigned r + 1) <= sz * nn) by (apply Z.mul_le_mono_nonneg_l; slia). slia. }
      assert (Hs0 : 0 <= sz * Int64.unsigned r) by (apply Z.mul_nonneg_nonneg; slia).
      set (ofs := inbase + sz * Int64.unsigned r + poff).
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
      assert (HSp : out_sep bd dbase bw outedge (cursor - 1) nbits bin ofs (ofs + psz)).
      { eapply out_sep_range with (lo := inbase) (hi := inbase + sz * nn); [|slia|slia].
        eapply out_sep_sub with (cursor := cursor) (count := 1 + nbits); [slia|slia|slia|slia|exact S5]. }
      destruct (Hpay mb bin ofs x (cursor - 1) Hrepb ltac:(slia) ltac:(slia) HSp HFb)
        as (me & HCallP & E2).
      destruct (exec_bitcoin_indexed_then_ptr (bitcoin_version_locals bl) le' t3 t4 arrfield adelta sid pexpr cid pt
        cf ofs mb me be ebase bt txbase bin inbase bd dbase r
        Ht3i Ht3d Ht4i Ht4d Hpty (Hnone bl) Hsym Hfun Hty He Hd Hi
        He0 ltac:(slia) Ht0 (proj1 Hab) ltac:(slia) Haf Hmb0 Hmb1
        (fun le'' H4 HI' => Hptr _ le'' mb bin inbase r H4 HI' Hi0 ltac:(slia)) HCallP)
        as [le'' HExec].
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
      destruct (bitcoin_skipBits_step mb bd dbase bw outedge (cursor - 1) (Z.to_nat nbits) HFb')
        as (me & HCallS & E2).
      exists le', me. split.
      + unfold bitcoin_skip_stmt.
        assert (Hargs : eval_exprlist bitcoin_ge (bitcoin_version_locals bl) le' mb
          [Etempvar _dst (tptr (Tstruct _frameItem noattr)); Econst_int (Int.repr nbits) tint]
          (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons tulong Tnil))
          [Vptr bd (Ptrofs.repr dbase); Vlong (Int64.repr (Z.of_nat (Z.to_nat nbits)))]).
        { eapply eval_Econs; [apply eval_Etempvar; exact Hd|reflexivity|].
          eapply eval_Econs; [apply eval_Econst_int| |apply eval_Enil].
          rewrite Z2Nat.id by slia. apply bitcoin_cast_const'; slia. }
        exact (exec_bitcoin_helper_call (bitcoin_version_locals bl) le' mb None _skipBits jets.f_skipBits
          _ _ _ _ _ _ me ltac:(helper_in) ltac:(reflexivity) Hargs ltac:(reflexivity) HCallS).
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

Theorem bitcoin_indexed_ptr_local {E : Set} {A} (elems_of : E -> list A) (nbits : Z) (pcells : A -> list Cell)
    (elemrep : mem -> block -> Z -> A -> Prop) (Bpay : Ty)
    (tp cp t3 t4 countfield arrfield sid cid : ident) (pt : type)
    (cdelta adelta sz poff psz : Z) (pexpr : expr) (cf f : function)
    (Htp : tp <> _env /\ tp <> _dst /\ tp <> _i /\ tp <> _t'1 /\ tp <> _t'2 /\ tp <> cp)
    (Hcp : cp <> _env /\ cp <> _dst /\ cp <> _i /\ cp <> _t'1 /\ cp <> _t'2)
    (Ht3i : t3 <> _i) (Ht3d : t3 <> _dst) (Ht4i : t4 <> _i) (Ht4d : t4 <> _dst)
    (Hnb : 1 <= nbits <= 1000) (Hlen : forall x, Z.of_nat (length (pcells x)) = nbits)
    (Hpty : typeof pexpr = tptr pt)
    (Hnone : forall bl, (bitcoin_version_locals bl)!cid = None)
    (Hsym : Genv.find_symbol (Clight.genv_genv bitcoin_ge) cid = Some (bitcoin_symbol_block cid))
    (Hfun : Genv.find_funct (Clight.genv_genv bitcoin_ge) (Vptr (bitcoin_symbol_block cid) Ptrofs.zero) =
      Some (Internal cf))
    (Hty : type_of_fundef (Internal cf) =
      Tfunction (Tcons (tptr (Tstruct _frameItem noattr)) (Tcons (tptr pt) Tnil)) tvoid cc_default)
    (Hcf : bitcoin_field_at _bitcoinTransaction countfield cdelta)
    (Haf : bitcoin_field_at _bitcoinTransaction arrfield adelta)
    (Hcb : 0 <= cdelta /\ cdelta + 8 <= 488) (Hab : 0 <= adelta /\ adelta + 8 <= 488)
    (Hsz : 0 < sz <= 1000) (Hpoff : 0 <= poff /\ poff + psz <= sz)
    (Hpres : forall m1 m2 b ofs x, elemrep m1 b ofs x ->
      (forall chunk o v, ofs <= o -> o + size_chunk chunk <= ofs + psz ->
        Mem.load chunk m1 b o = Some v -> Mem.load chunk m2 b o = Some v) -> elemrep m2 b ofs x)
    (Hpay : forall bd dbase bw outedge m' bin ofs x cur, elemrep m' bin ofs x -> 0 <= ofs ->
      ofs + psz <= Ptrofs.max_unsigned ->
      out_sep bd dbase bw outedge cur nbits bin ofs (ofs + psz) ->
      write_frame_at m' bd dbase bw outedge cur nbits ->
      exists me, Clight2.eval_funcall bitcoin_ge m' (Internal cf)
        [Vptr bd (Ptrofs.repr dbase); Vptr bin (Ptrofs.repr ofs)] E0 me Vundef /\
        write_effect m' me bd dbase bw outedge cur nbits (pcells x))
    (Hptr : forall e le' m' bin inbase r,
      le'!t4 = Some (Vptr bin (Ptrofs.repr inbase)) -> le'!_i = Some (Vlong r) ->
      0 <= inbase -> inbase + sz * Int64.unsigned r + poff + psz <= Ptrofs.max_unsigned ->
      eval_expr bitcoin_ge e le' m' pexpr (Vptr bin (Ptrofs.repr (inbase + sz * Int64.unsigned r + poff))))
    (Hshape : bitcoin_wrapper_shape f
      (bitcoin_indexed_rest tp cp countfield
        (bitcoin_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt) (bitcoin_skip_stmt nbits)))
    (HB : Z.of_nat (bitSize (Ty.Sum Ty.Unit Bpay)) = 1 + nbits)
    (spec : Ty.tySem Word32 -> E -> option (Ty.tySem (Ty.Sum Ty.Unit Bpay)))
    (Hsem : forall a environment, exists V, spec a environment = Some V /\
      encode V = indexed_ptr_cells (elems_of environment) nbits pcells a) :
  application_jet_local_spec_sep f bitcoin_ge E Word32 (Ty.Sum Ty.Unit Bpay)
    (indexed_ptr_rep elems_of elemrep sz poff adelta cdelta) spec.
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
  destruct (bitcoin_wrapper_layout f
    (bitcoin_indexed_rest tp cp countfield
      (bitcoin_indexed_then_ptr t3 t4 arrfield sid pexpr cid pt) (bitcoin_skip_stmt nbits))
    (indexed_ptr_cells (elems_of environment) nbits pcells a) (Vptr be (Ptrofs.repr ebase)) m bd dbase bs
    sbase bw outedge cursor (1 + nbits) bytes Hshape HBf HA HBytes ltac:(slia) HFrame
    (bitcoin_indexed_ptr_mid (elems_of environment) nbits pcells elemrep tp cp t3 t4 countfield arrfield sid cid
      pt cdelta adelta sz poff psz pexpr cf f Htp Hcp Ht3i Ht3d Ht4i Ht4d Hnb Hlen Hpty Hnone Hsym Hfun Hty
      Hcf Haf Hcb Hab Hsz Hpoff Hpres bd dbase bw outedge (Hpay bd dbase bw outedge) Hptr
      m bs sbase bi edge cursor read_cursor a be ebase bt txbase bin inbase nI bytes He0 He1 Ht0 Ht1 Hi0 Hi1
      HLtx HLin HLn HnI HLelem S1 S4 S5 (conj HSedge HSoff) ltac:(slia) Hin HFrame HBytes))
    as (mf & HCall & HCells & HPrefix & HFields & HMem).
  exists mf, V. split; [exact HVs|].
  split; [exact HCall|]. split; [rewrite HVenc; exact HCells|]. split; [exact HPrefix|].
  rewrite HB. split; [exact HFields|]. exact HMem.
Qed.
