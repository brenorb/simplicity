(** The generator's original 129/15 wNAF helper, including actual entry,
    return conversion and release of its private scalar. The single original
    external memset step and its zeroing/frame effects remain explicit premises.
    This is conditional internal composition, not an external-call model or a
    complete public jet proof. No implementation or specification is replaced. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs
  ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_toZ C.jet_word_repr C.jet_sx_mem C.jet_secp_linkage C.jets_secp.
Require Import C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
  C.jet_secp_wnaf_prepare C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_literal
  C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_literal_prepare
  C.jet_secp_wnaf_return_length C.jet_secp_statement_prefix.
Require Import C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
  C.jet_secp_scalar_add_reader_support.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma wnaf_array_lframe m mf b base len w sign bit last digits P :
  wnaf_array_state m b base len w sign bit last digits ->
  lframe P m mf -> (forall pos, P b pos) ->
  wnaf_array_state mf b base len w sign bit last digits.
Proof.
  intros [Access Load Suffix Digits Last] Frame Cover;constructor;try assumption.
  - intros i Range;destruct (Access i Range) as [Cells Align];split;[|exact Align].
    intros pos R;apply (proj1 (proj2 Frame));
      [eapply Mem.perm_valid_block;apply Cells;exact R|apply Cover|apply Cells;exact R].
  - intros i Range;rewrite (proj1 Frame).
    + apply Load;exact Range.
    + eapply Mem.perm_valid_block;apply (proj1 (Access i Range) (base+4*i)).
      change (base+4*i<=base+4*i<base+4*i+4);lia.
    + intros;apply Cover.
Qed.

Lemma wnaf_local_blocks bs : blocks_of_env secp_ge (wnaf_env bs)=[(bs,0,32)].
Proof. reflexivity. Qed.

Theorem eval_wnaf_literal15_from_memset_step
  (word : Ty.tySem (Word 7)) m mi mz bs ba abase b :
  scalar_at m ba abase (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word))) ->
  ba<>b -> Mem.range_perm m b 0 516 Cur Freeable ->
  Mem.alloc m 0 32=(mi,bs) ->
  Clight2.exec_stmt secp_ge (wnaf_env bs)
    (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba (Ptrofs.repr abase))))
    mi wnaf_memset_call E0
    (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba (Ptrofs.repr abase))))
    mz Out_normal ->
  (forall i,0<=i<129 -> Mem.load Mint32 mz b (4*i)=Some (Vint Int.zero)) ->
  wnaf_memory_effect b mi mz ->
  exists mf last digits,
    Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_wnaf)
      [Vptr b Ptrofs.zero;Vint (Int.repr 129);Vptr ba (Ptrofs.repr abase);Vint (Int.repr 15)]
      E0 mf (Vint (Int.repr (last+1))) /\
    wnaf_array_state mf b 0 129 15 1 129 last digits /\
    0<=last+1<=129 /\ Mem.range_perm mf b 0 516 Cur Freeable /\
    Mem.nextblock mf=Mem.nextblock mi /\
    lframe (fun old _=>old<>b) m mf /\
    scalar_at mf ba abase (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word))) /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
      rev (map (fun i=>digits (Z.of_nat i)) (seq 0 129)) /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
      repeat 0 (129-Z.to_nat (last+1))++rev (wnaf_slice (Z.to_nat (last+1)) digits 0) /\
    (forall old pos k p,Mem.valid_block m old ->
      (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)).
Proof.
  intros Input Separate Owned Alloc ZeroStep Zeros [ZeroBlocks [ZeroPerm ZeroFrame]].
  assert (AllocFrame:lframe (fun _ _=>True) m mi).
  { apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc. }
  assert (SourceValid:Mem.valid_block m ba).
  { destruct Input as (_ & Base & _ & _ & Read & _).
    eapply Mem.perm_valid_block;apply (Read abase);lia. }
  assert (OutputValid:Mem.valid_block m b).
  { eapply Mem.perm_valid_block;apply (Owned 0);lia. }
  assert (SourcePrivate:ba<>bs).
  { intro Same;subst ba;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc SourceValid). }
  assert (OutputPrivate:b<>bs).
  { intro Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc OutputValid). }
  assert (InputI:scalar_at mi ba abase (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word)))).
  { eapply scalar_at_lframe;[exact Input|exact AllocFrame|intros;exact I]. }
  assert (InputZ:scalar_at mz ba abase (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word)))).
  { eapply scalar_at_lframe;[exact InputI|exact ZeroFrame|intros;exact Separate]. }
  assert (PrivateZ:Mem.range_perm mz bs 0 32 Cur Freeable).
  { intros pos Range;apply (proj1 (ZeroPerm bs pos Cur Freeable)).
    eapply Mem.perm_alloc_2;[exact Alloc|exact Range]. }
  assert (OutputZ:Mem.range_perm mz b 0 516 Cur Freeable).
  { intros pos Range;apply (proj1 (ZeroPerm b pos Cur Freeable)).
    apply (proj1 (proj2 AllocFrame));[exact OutputValid|exact I|apply Owned;exact Range]. }
  assert (Access:forall i,0<=i<129 -> Mem.valid_access mz Mint32 b (0+4*i) Writable).
  { intros i Range;split.
    - intros pos R;eapply Mem.perm_implies;[apply OutputZ;change (0+4*i<=pos<0+4*i+4) in R;lia|constructor].
    - change (4|0+4*i);exists i;ring. }
  assert (Fields:wnaf_loop_fields
    (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba (Ptrofs.repr abase))))
    0 129 15 0 1 b 0 (-1)).
  { unfold wnaf_loop_fields,wnaf_before_temps,wnaf_entry15_temps;repeat split;reflexivity. }
  assert (N:0<=@toZ (WordToZ 7) word<2^128).
  { pose proof (word_toZ_range 7 word) as Range;exact Range. }
  destruct (exec_wnaf_post_memset_literal15
    (wnaf_before_temps (wnaf_entry15_temps b 0 (Vptr ba (Ptrofs.repr abase))))
    mz (@toZ (WordToZ 7) word) ba abase bs b 0 word N eq_refl
    ltac:(rewrite wnaf_before_preserves by discriminate;reflexivity)
    Fields InputZ SourcePrivate OutputPrivate
    ltac:(intros pos Range;eapply Mem.perm_implies;[apply PrivateZ;exact Range|constructor])
    ltac:(lia) ltac:(change (516<=18446744073709551615);lia) Access Zeros)
    as (lef & mr & last & digits & Tail & Final & PrivateScalar & Array & Bound &
        TailBlocks & TailPerm & TailFrame & Literal).
  assert (PrivateR:Mem.range_perm mr bs 0 32 Cur Freeable).
  { intros pos Range;apply (proj2 (TailPerm bs pos Cur Freeable));apply PrivateZ;exact Range. }
  destruct (Mem.range_perm_free mr bs 0 32 PrivateR) as [mf Free].
  assert (FreeFrame:lframe (fun old _=>old<>bs) mr mf).
  { apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Free|].
    intros pos Range NotSame;apply NotSame;reflexivity. }
  assert (ArrayF:wnaf_array_state mf b 0 129 15 1 129 last digits).
  { eapply wnaf_array_lframe;[exact Array|exact FreeFrame|intros;exact OutputPrivate]. }
  assert (WholeFrame:lframe (fun old _=>old<>b) m mf).
  { eapply lframe_implies with (P:=fun old _=>Mem.valid_block m old /\ old<>b).
    - eapply lframe_trans.
      + eapply lframe_implies;[exact AllocFrame|intros;exact I].
      + eapply lframe_trans.
        * eapply lframe_implies;[exact ZeroFrame|intros old pos [Valid Other] _;exact Other].
        * eapply lframe_trans.
          -- eapply lframe_implies;[exact TailFrame|].
             intros old pos [Valid Other] _;split;[|exact Other].
             intro Same;subst old;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
          -- eapply lframe_implies;[exact FreeFrame|].
             intros old pos [Valid Other] _ Same;subst old.
             exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
    - intros old pos Other Valid;split;assumption. }
  exists mf,last,digits;split.
  - eapply eval_funcall_internal with (e:=wnaf_env bs)
      (le1:=wnaf_entry15_temps b 0 (Vptr ba (Ptrofs.repr abase)))
      (le2:=lef) (m1:=mi) (m2:=mr)
      (out:=Out_return (Some (Vint (Int.repr (last+1)),tint))).
    + apply wnaf_entry15;exact Alloc.
    + rewrite wnaf_body_to_memset_source;eapply exec_statement_prefix_then_last.
      * apply exec_wnaf_before_memset15;reflexivity.
      * unfold wnaf_at_memset;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
          [exact ZeroStep|exact Tail].
    + split;[discriminate|reflexivity].
    + rewrite wnaf_local_blocks;cbn [Mem.free_list];rewrite Free;reflexivity.
  - split;[exact ArrayF|];split;[exact Bound|];split.
    + intros pos Range;eapply Mem.perm_free_1;[exact Free|left;exact OutputPrivate|].
      apply (proj2 (TailPerm b pos Cur Freeable));apply OutputZ;exact Range.
    + split.
      * rewrite (Mem.nextblock_free _ _ _ _ _ Free),TailBlocks,ZeroBlocks;reflexivity.
      * split;[exact WholeFrame|];split.
        -- eapply scalar_at_lframe;[exact Input|exact WholeFrame|intros;exact Separate].
        -- split;[exact Literal|];split.
           ++ eapply wnaf_literal_return_length;[exact ArrayF|exact Literal].
           ++ intros old pos k p Valid.
              assert (NotPrivate:old<>bs).
              { intro Same;subst old;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid). }
              split;intro Perm.
              ** eapply Mem.perm_alloc_4;[exact Alloc| |exact NotPrivate].
                 apply (proj2 (ZeroPerm old pos k p));apply (proj1 (TailPerm old pos k p)).
                 eapply Mem.perm_free_3;[exact Free|exact Perm].
              ** eapply Mem.perm_free_1;[exact Free|left;exact NotPrivate|].
                 apply (proj2 (TailPerm old pos k p));apply (proj1 (ZeroPerm old pos k p)).
                 eapply Mem.perm_alloc_1;[exact Alloc|exact Perm].
Qed.
