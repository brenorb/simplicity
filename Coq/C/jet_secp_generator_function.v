(** Whole original Strauss call on generate's actual num=1, zero-na path.
    Entry, preparation, scalar split, both wNAF calls, the point stage and
    all nine local frees are composed. Only the exact original external
    memset steps remain conditional; no helper execution/result is assumed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib AST Ctypes Clight Clightdefs ClightBigstep
  Integers Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word.
Require Simplicity.Alg Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp
  C.jet_secp_fe_nv C.jet_secp_fe_math C.jet_secp_curve_frame C.jet_secp_field_read_preservation
  C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product
  C.jet_secp_square_columns C.jet_secp_rescale_literal C.jet_secp_canonical_zero
  C.jet_secp_canonical_scalar C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_scalar_add_reader_support C.jet_secp_statement_prefix
  C.jet_secp_generator_initialize C.jet_secp_generator_globalz_call C.jet_secp_generator_entry
  C.jet_secp_generator_zero_global C.jet_secp_generator_globals C.jet_secp_generator_main
  C.jet_secp_generate_program C.jet_secp_wnaf_digit C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_loop
  C.jet_clight_internal_preserve C.jet_clight_readonly_frame.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_generate rescale_field_output.

Lemma generator_local_blocks bt bz b0 b128 bw0 bw128 bj bn bl :
  blocks_of_env secp_ge (generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl)=
  [(bw128,0,516);(bw0,0,516);(bt,0,88);(bj,0,128);(bz,0,40);
   (b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)].
Proof. reflexivity. Qed.

Theorem eval_generator_strauss_from_owned value m bs bx ba bp bng (a:val) :
  generator_zero_global_state m -> (forall h,generator_table_state h m) ->
  Mem.load Mptr m bs 0=Some (Vptr bx Ptrofs.zero) ->
  Mem.load Mptr m bs 8=Some (Vptr ba Ptrofs.zero) -> bp<>bng ->
  Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m bng 0 32 Cur Freeable ->
  scalar_at m bng 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value)))) ->
  (forall ma mi local ba b,Mem.alloc ma 0 32=(mi,local) ->
    Mem.range_perm ma b 0 516 Cur Freeable -> exists mz,
    Clight2.exec_stmt secp_ge (wnaf_env local)
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero)))
      mi wnaf_memset_call E0
      (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba Ptrofs.zero))) mz Out_normal /\
    (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) /\
    wnaf_memory_effect b mi mz) ->
  exists mf ox oy oz,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_strauss_wnaf)
      [Vptr bs Ptrofs.zero;Vptr bp Ptrofs.zero;Vlong Int64.one;a;
       Vptr generator_zero_block Ptrofs.zero;Vptr bng Ptrofs.zero] E0 mf Vundef /\
    fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
    Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
    Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf bng 0 32 Cur Freeable /\
    square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
    ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
      @literal_generate Alg.CoreFunSem value /\
    lframe (fun b _=>b<>bp /\ b<>bng) m mf.
Proof.
  intros Zero Tables X A Separate PF SF Input ZeroSteps.
  assert (VP:Mem.valid_block m bp) by (eapply Mem.perm_valid_block;exact (PF 0 ltac:(clear;lia))).
  assert (VNG:Mem.valid_block m bng) by (eapply Mem.perm_valid_block;exact (SF 0 ltac:(clear;lia))).
  destruct (generator_entry_and_prepare m bs bx ba (Vptr bp Ptrofs.zero) a (Vptr bng Ptrofs.zero) Zero X A)
    as (mi & mp & bt & bz & b0 & b128 & bw0 & bw128 & bj & bn & bl &
        Entry & Prepare & Denominator & Locals & Old & Free & PFrame & Preserve).
  set (e:=generator_local_env bt bz b0 b128 bw0 bw128 bj bn bl) in *.
  set (le:=generator_entry_temps bs (Vptr bp Ptrofs.zero) a (Vptr bng Ptrofs.zero)) in *.
  set (lr:=generator_ready_temps le (Vptr ba Ptrofs.zero) (Vptr bx Ptrofs.zero)) in *.
  assert (OutsideP:~In bp [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VP).
  assert (OutsideNG:~In bng [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) by (apply Old;exact VNG).
  assert (MainSep:NoDup [bp;bt;bz;b0;b128;bw0;bw128;bj;bn;bl;bng]).
  { pose proof Locals as Distinct;repeat rewrite NoDup_cons_iff in Distinct;
      cbn [In] in Distinct,OutsideP,OutsideNG.
    repeat rewrite NoDup_cons_iff;cbn [In];intuition congruence. }
  assert (PZ:bp<>bz) by (intro Same;apply OutsideP;subst bp;cbn [In];tauto).
  assert (NGZ:bng<>bz) by (intro Same;apply OutsideNG;subst bng;cbn [In];tauto).
  assert (PFP:Mem.range_perm mp bp 0 128 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact PF|exact PFrame|intros;exact PZ]. }
  assert (SFP:Mem.range_perm mp bng 0 32 Cur Freeable).
  { eapply curve_keep_free;[clear;lia|exact SF|exact PFrame|intros;exact NGZ]. }
  assert (InputP:scalar_at mp bng 0 (map Int64.repr (scalar_limbs_of
    (@toZ (WordToZ 8) (@canonical_scalar_normalize Alg.CoreFunSem value))))).
  { eapply scalar_at_lframe;[exact Input|exact PFrame|intros;exact NGZ]. }
  assert (ReadonlyP:readonly_preserved m mp).
  { eapply preserved_trans;[eapply entry_preserved;exact Entry|exact Preserve]. }
  assert (TablesP:forall h,generator_table_state h mp).
  { intro h;pose proof (Tables h) as [Table Bounds].
    apply (generator_table_state_unchanged h m mp);[|apply Tables].
    eapply Mem.unchanged_on_implies;[exact (proj2 ReadonlyP)|].
    intros b pos At Valid;subst b;split;[exact Valid|].
    apply (readonly_bounds_not_writable _ _ _ _ Bounds). }
  assert (PR:lr!_r=Some (Vptr bp Ptrofs.zero)).
  { unfold lr,generator_ready_temps;rewrite generator_no_points_preserves by discriminate.
    rewrite generator_initial_preserves by discriminate;reflexivity. }
  assert (NG:lr!_ng=Some (Vptr bng Ptrofs.zero)).
  { unfold lr,generator_ready_temps;rewrite generator_no_points_preserves by discriminate.
    rewrite generator_initial_preserves by discriminate;reflexivity. }
  assert (No:lr!_no=Some (Vlong Int64.zero)).
  { unfold lr,generator_ready_temps;rewrite generator_no_points_preserves by discriminate;apply PTree.gss. }
  assert (Bits:lr!_bits=Some (Vint Int.zero)).
  { unfold lr,generator_ready_temps;rewrite generator_no_points_preserves by discriminate.
    unfold generator_initial_temps;rewrite PTree.gso by discriminate;apply PTree.gss. }
  destruct (exec_generator_main_stage lr mp value bp bng bt bz b0 b128 bw0 bw128 bj bn bl
    MainSep TablesP PR NG No Bits InputP Denominator PFP SFP Free
    ltac:(intros high ma mm local Alloc Owned;exact (ZeroSteps ma mm local _ _ Alloc Owned)))
    as (lef & mu & ox & oy & oz & Main & PRF & XO & YO & ZO & Flag & PFU & SFU &
        FreeU & BX & BY & BZ & Literal & MFrame).
  destruct (free_list_exists
    [(bw128,0,516);(bw0,0,516);(bt,0,88);(bj,0,128);(bz,0,40);
     (b128,0,32);(b0,0,32);(bn,0,32);(bl,0,32)] mu) as (mf & Released & Unchanged).
  - pose proof Locals as Distinct;repeat rewrite NoDup_cons_iff in Distinct;cbn [In] in Distinct.
    clear -Distinct;cbn;repeat constructor;cbn;intuition congruence.
  - intros b lo hi Slot;clear -FreeU Slot;cbn [In] in Slot.
    repeat match type of Slot with _ \/ _=>destruct Slot as [Slot|Slot] end;try contradiction;
      inversion Slot;subst;apply FreeU;cbn [generator_local_storage In];tauto.
  - assert (FFrame:lframe (fun b _=>~In b [bt;bz;b0;b128;bw0;bw128;bj;bn;bl]) mu mf).
    { eapply lframe_implies;[apply lframe_unchanged;exact Unchanged|].
      intros b pos Outside Valid;clear -Outside;cbn [map fst In] in *;intuition congruence. }
    assert (XF:fe_at mf bp 0 (words5 ox)).
    { eapply field_at_lframe;[exact XO|exact FFrame|intros;exact OutsideP]. }
    assert (YF:fe_at mf bp 40 (words5 oy)).
    { eapply field_at_lframe;[exact YO|exact FFrame|intros;exact OutsideP]. }
    assert (ZF:fe_at mf bp 80 (words5 oz)).
    { eapply field_at_lframe;[exact ZO|exact FFrame|intros;exact OutsideP]. }
    assert (FlagF:Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Simplicity.Bit.toBool
      (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz)))))).
    { rewrite (proj1 FFrame Mint32 bp 120);[exact Flag| |intros;exact OutsideP].
      eapply Mem.perm_valid_block;exact (PFU 0 ltac:(clear;lia)). }
    assert (PFF:Mem.range_perm mf bp 0 128 Cur Freeable).
    { eapply curve_keep_free;[clear;lia|exact PFU|exact FFrame|intros;exact OutsideP]. }
    assert (SFF:Mem.range_perm mf bng 0 32 Cur Freeable).
    { eapply curve_keep_free;[clear;lia|exact SFU|exact FFrame|intros;exact OutsideNG]. }
    assert (Frame:lframe (fun b _=>b<>bp /\ b<>bng) m mf).
    { eapply lframe_implies with (P:=fun b _=>Mem.valid_block m b /\ b<>bp /\ b<>bng).
      - eapply lframe_trans.
        + eapply lframe_implies;[exact PFrame|].
          intros b pos [Valid [NotP NotNG]] _ Same;subst b;apply (Old bz Valid);cbn [In];tauto.
        + eapply lframe_trans.
          * eapply lframe_implies;[exact MFrame|].
            intros b pos [Valid [NotP NotNG]] _;split;[exact NotP|];split;[apply Old;exact Valid|exact NotNG].
          * eapply lframe_implies;[exact FFrame|].
            intros b pos [Valid [NotP NotNG]] _;apply Old;exact Valid.
      - intros b pos [NotP NotNG] Valid;split;[exact Valid|];split;assumption. }
    exists mf,ox,oy,oz;split.
    + eapply eval_funcall_internal with (e:=e) (le1:=le) (le2:=lef) (m1:=mi) (m2:=mu) (out:=Out_normal).
      * exact Entry.
      * rewrite generator_body_main_source;eapply exec_statement_prefix_then_last;[exact Prepare|exact Main].
      * reflexivity.
      * unfold e;rewrite generator_local_blocks;exact Released.
    + split;[exact XF|];split;[exact YF|];split;[exact ZF|];split;[exact FlagF|];
      split;[exact PFF|];split;[exact SFF|];split;[exact BX|];split;[exact BY|];split;[exact BZ|];
      split;[exact Literal|exact Frame].
Qed.
