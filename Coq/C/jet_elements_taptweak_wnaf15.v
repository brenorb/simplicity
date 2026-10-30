(** Whole original 129/15 wNAF call in the linked Elements program.
    Derives the real clear from the existing memset model, reuses the proved
    pure tail, and retains the literal digits, exact allocation count,
    old permissions, readonly state, entry and final private-scalar free. *)
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

Require Import C.jet_secp_wnaf_function15 C.jet_secp_wnaf_memset C.jet_memset_model
 C.jet_secp_wnaf5_prepare C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_elements_taptweak_pure.
Require Import C.jet_elements_taptweak_wnaf_transport C.jet_elements_taptweak_wnaf_memset.
Local Opaque elements_taptweak_ge.
Theorem eval_elements_taptweak_wnaf15(Model:memset_model)
  (word:Ty.tySem(Word 7))m ba abase b:
  scalar_at m ba abase (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word))) ->
  ba<>b -> Mem.range_perm m b 0 516 Cur Freeable ->
  exists mf last digits,
    Clight2.eval_funcall elements_taptweak_ge m (Internal f_secp256k1_ecmult_wnaf)
      [Vptr b Ptrofs.zero;Vint (Int.repr 129);Vptr ba (Ptrofs.repr abase);Vint (Int.repr 15)]
      E0 mf (Vint (Int.repr (last+1))) /\
    wnaf_array_state mf b 0 129 15 1 129 last digits /\
    0<=last+1<=129 /\ Mem.range_perm mf b 0 516 Cur Freeable /\
    Mem.nextblock mf=Pos.succ(Mem.nextblock m) /\
    lframe (fun old _=>old<>b) m mf /\
    scalar_at mf ba abase (map Int64.repr (scalar_limbs_of (@toZ (WordToZ 7) word))) /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
      rev (map (fun i=>digits (Z.of_nat i)) (seq 0 129)) /\
    map wnaf_literal_value (literal_wnaf15_digits (Bit.zero,word))=
      repeat 0 (129-Z.to_nat (last+1))++rev (wnaf_slice (Z.to_nat (last+1)) digits 0) /\
    (forall old pos k p,Mem.valid_block m old ->
      (Mem.perm mf old pos k p <-> Mem.perm m old pos k p)) /\
    readonly_preserved m mf /\keeps_permissions m mf.
Proof.
  intros Input Separate Owned.
  destruct(Mem.alloc m 0 32)as[mi bs]eqn:Alloc.
  assert(ClearSpace:Mem.range_perm mi b 0(0+4*129)Cur Writable).
  { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc|].
    eapply Mem.perm_implies;[apply Owned;lia|constructor]. }
  destruct(exec_elements_taptweak_wnaf_memset Model(wnaf_env bs)
   (wnaf_before_temps(wnaf_entry15_temps b 0(Vptr ba(Ptrofs.repr abase))))mi b 0 129
   eq_refl eq_refl eq_refl ltac:(lia)ltac:(lia)
   ltac:(change(516<=18446744073709551615);lia)ClearSpace)as(mz & ZeroStep & Store).
  pose proof(memset_memory_effect _ _ _ _ _ Store)as[ZeroBlocks[ZeroPerm ZeroFrame]].
  assert(Zeros:forall i,0<=i<129 ->Mem.load Mint32 mz b(4*i)=Some(Vint Int.zero)).
  { intros i Range;exact(memset_zero_load _ _ _ _ _ _ Store(Z.divide_0_r 4)Range). }

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
  pose proof(elements_taptweak_wnaf_statement_transport bs
   (wnaf_before_temps(wnaf_entry15_temps b 0(Vptr ba(Ptrofs.repr abase))))mz wnaf_post_memset E0 lef mr
   (Out_return(Some(Vint(Int.repr(last+1)),tint)))ltac:(right;left;reflexivity)Tail)as TailT.

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
  assert(Perms:forall old pos k p,Mem.valid_block m old ->
    (Mem.perm mf old pos k p <->Mem.perm m old pos k p)).
  { intros old pos k p Valid.
              assert (NotPrivate:old<>bs).
              { intro Same;subst old;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid). }
              split;intro Perm.
 - eapply Mem.perm_alloc_4;[exact Alloc| |exact NotPrivate].
                 apply (proj2 (ZeroPerm old pos k p));apply (proj1 (TailPerm old pos k p)).
                 eapply Mem.perm_free_3;[exact Free|exact Perm].
 - eapply Mem.perm_free_1;[exact Free|left;exact NotPrivate|].
                 apply (proj2 (TailPerm old pos k p));apply (proj1 (ZeroPerm old pos k p)).
                 eapply Mem.perm_alloc_1;[exact Alloc|exact Perm]. }
  assert(Readonly:readonly_preserved m mf).
  { eapply preserved_trans;[eapply alloc_preserved;exact Alloc|].
    eapply preserved_trans;[eapply storebytes_preserved;exact Store|].
    eapply preserved_trans;[eapply wnaf_post_memset_readonly;exact Tail|].
    eapply free_preserved;exact Free. }
  assert(Keep:keeps_permissions m mf).
  { intros old pos k p Perm;apply(proj2(Perms old pos k p(Mem.perm_valid_block _ _ _ _ _ Perm)));exact Perm. }
  exists mf,last,digits;split.
  - eapply eval_funcall_internal with (e:=wnaf_env bs)
      (le1:=wnaf_entry15_temps b 0 (Vptr ba (Ptrofs.repr abase)))
      (le2:=lef) (m1:=mi) (m2:=mr)
      (out:=Out_return (Some (Vint (Int.repr (last+1)),tint))).
    + apply elements_taptweak_wnaf_entry15;exact Alloc.
    + rewrite wnaf_body_to_memset_source;eapply exec_statement_prefix_then_last.
      * apply exec_elements_taptweak_wnaf_before15;reflexivity.
      * unfold wnaf_at_memset;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);
          [exact ZeroStep|exact TailT].
    + split;[discriminate|reflexivity].
    + rewrite elements_taptweak_wnaf_local_blocks;cbn [Mem.free_list];rewrite Free;reflexivity.
  - split;[exact ArrayF|];split;[exact Bound|];split.
    + intros pos Range;eapply Mem.perm_free_1;[exact Free|left;exact OutputPrivate|].
      apply (proj2 (TailPerm b pos Cur Freeable));apply OutputZ;exact Range.
    + split.
      * rewrite(Mem.nextblock_free _ _ _ _ _ Free),TailBlocks,ZeroBlocks;exact(Mem.nextblock_alloc _ _ _ _ _ Alloc).
      * split;[exact WholeFrame|];split.
        -- eapply scalar_at_lframe;[exact Input|exact WholeFrame|intros;exact Separate].
        -- split;[exact Literal|];split.
           ++ eapply wnaf_literal_return_length;[exact ArrayF|exact Literal].
           ++ split;[exact Perms|split;[exact Readonly|exact Keep]].
Qed.
