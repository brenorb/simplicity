(** The original 129/5 C function against every literal signed input state,
    including entry, its real memset call, sign preparation, all iterations,
    return conversion and private-scalar release. The external memset contract
    is explicit; no intermediate execution or desired output is a premise. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_sx_exec C.jet_secp_linkage C.jets_secp
 C.jet_memset_model C.jet_secp_wnaf_slice_frame C.jet_clight_internal_permissions C.jet_clight_internal_preserve
 C.jet_secp_scalar_get_b32_storage C.jet_secp_scalar_get_b32_numeric
 C.jet_secp_scalar_add_reader_support C.jet_secp_statement_prefix
 C.jet_secp_wnaf_digit C.jet_secp_wnaf_control C.jet_secp_wnaf_loop
 C.jet_secp_wnaf_prepare C.jet_secp_wnaf_entry15 C.jet_secp_wnaf_entry5
 C.jet_secp_wnaf_function15 C.jet_secp_wnaf_memset C.jet_secp_wnaf5_prepare
 C.jet_secp_wnaf5_input C.jet_secp_wnaf5_literal C.jet_secp_wnaf5_signed_array.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Theorem eval_wnaf_literal5_slice (Model:memset_model) sb (word:Ty.tySem (Word 7)) m ba abase b base :
 scalar_at m ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) ->
 ba<>b -> 0<=base -> (4|base) -> base+516<=Ptrofs.max_unsigned ->
 Mem.range_perm m b base (base+516) Cur Freeable -> exists mf last digits,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_wnaf)
  [Vptr b (Ptrofs.repr base);Vint (Int.repr 129);Vptr ba (Ptrofs.repr abase);Vint (Int.repr 5)]
  E0 mf (Vint (Int.repr (last+1))) /\
 wnaf_array_state mf b base 129 5 (wnaf5_input_sign sb) 129 last digits /\
 0<=last+1<=129 /\ Mem.range_perm mf b base (base+516) Cur Freeable /\
 lframe (wnaf_slice_outside b base 129) m mf /\
 scalar_at mf ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb,word))=
  rev (map (fun i=>wnaf5_input_sign sb*digits (Z.of_nat i)) (seq 0 129)).
Proof.
 intros Input Separate Base Align Fits Owned.
 destruct (Mem.alloc m 0 32) as [mi bs] eqn:Alloc.
 assert (AllocFrame:lframe (fun _ _=>True) m mi).
 { apply lframe_unchanged;eapply Mem.alloc_unchanged_on;exact Alloc. }
 assert (SourceValid:Mem.valid_block m ba).
 { destruct Input as (_ & SrcBase & _ & _ & Read & _).
   eapply Mem.perm_valid_block;apply (Read abase);lia. }
 assert (OutputValid:Mem.valid_block m b).
 { eapply Mem.perm_valid_block;apply (Owned base);lia. }
 assert (SourcePrivate:ba<>bs).
 { intro Same;subst ba;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc SourceValid). }
 assert (OutputPrivate:b<>bs).
 { intro Same;subst b;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc OutputValid). }
 set (le:=wnaf_before_temps (wnaf_entry5_temps b base (Vptr ba (Ptrofs.repr abase)))).
 assert (OutputI:Mem.range_perm mi b base (base+4*129) Cur Writable).
 { intros pos Range;eapply Mem.perm_alloc_1;[exact Alloc|].
   eapply Mem.perm_implies;[apply Owned;lia|constructor]. }
 destruct (exec_wnaf_memset Model (wnaf_env bs) le mi b base 129
  eq_refl eq_refl eq_refl ltac:(lia) Base Fits OutputI)
  as (mz & ZeroStep & Store).
 destruct (memset_memory_effect _ _ _ _ _ Store) as [ZeroBlocks [ZeroPerm ZeroFrame]].
 assert (InputI:scalar_at mi ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word)))).
 { eapply scalar_at_lframe;[exact Input|exact AllocFrame|intros;exact I]. }
 assert (InputZ:scalar_at mz ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word)))).
 { eapply scalar_at_lframe;[exact InputI|exact ZeroFrame|intros;exact Separate]. }
 assert (PrivateZ:Mem.range_perm mz bs 0 32 Cur Freeable).
 { intros pos Range;apply (proj1 (ZeroPerm bs pos Cur Freeable)).
   eapply Mem.perm_alloc_2;[exact Alloc|exact Range]. }
 assert (OutputZ:Mem.range_perm mz b base (base+516) Cur Freeable).
 { intros pos Range;apply (proj1 (ZeroPerm b pos Cur Freeable)).
   eapply Mem.perm_alloc_1;[exact Alloc|apply Owned;exact Range]. }
 assert (Access:forall i,0<=i<129 -> Mem.valid_access mz Mint32 b (base+4*i) Writable).
 { intros i Range;split.
   - intros pos R;eapply Mem.perm_implies;[apply OutputZ;change (base+4*i<=pos<base+4*i+4) in R;lia|constructor].
   - change (4|base+4*i);apply Z.divide_add_r;[exact Align|exists i;ring]. }
 assert (Zeros:forall i,0<=i<129 -> Mem.load Mint32 mz b (base+4*i)=Some (Vint Int.zero)).
 { intros i Range;exact (memset_zero_load _ _ _ _ _ _ Store Align Range). }
 assert (Fields:wnaf_loop_fields le 0 129 5 0 1 b base (-1)).
 { unfold le,wnaf_loop_fields,wnaf_before_temps,wnaf_entry5_temps;repeat split;reflexivity. }
 destruct (exec_wnaf5_post_memset le mz sb word ba abase bs b base
  eq_refl Fields InputZ SourcePrivate OutputPrivate PrivateZ Base Fits Access Zeros)
  as (lef & mr & carry & last & digits & Tail & Final & Carry & ScalarR & PrivateR
    & Array & Bound & TailFrame & TailKeep & Literal & TailSlice).
 destruct (Mem.range_perm_free mr bs 0 32 PrivateR) as [mf Free].
 assert (FreeFrame:lframe (fun old _=>old<>bs) mr mf).
 { apply lframe_unchanged;eapply Mem.free_unchanged_on;[exact Free|].
   intros pos Range NotSame;apply NotSame;reflexivity. }
 assert (ArrayF:wnaf_array_state mf b base 129 5 (wnaf5_input_sign sb) 129 last digits).
 { eapply wnaf_array_lframe;[exact Array|exact FreeFrame|intros;exact OutputPrivate]. }
 assert (ZeroSlice:lframe (wnaf_slice_outside b base 129) mi mz).
 { eapply wnaf_slice_memset_frame;[lia|exact Store]. }
 assert (WholeFrame:lframe (wnaf_slice_outside b base 129) m mf).
 { eapply lframe_implies with
    (P:=fun old pos=>Mem.valid_block m old /\ wnaf_slice_outside b base 129 old pos).
   - eapply lframe_trans.
     + eapply lframe_implies;[exact AllocFrame|intros;exact I].
     + eapply lframe_trans.
       * eapply lframe_implies;[exact ZeroSlice|intros old pos [Valid Outside] _;exact Outside].
       * eapply lframe_trans.
         -- eapply lframe_implies;[exact TailSlice|].
            intros old pos [Valid Outside] _;split;[|exact Outside].
            intro Same;subst old;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
         -- eapply lframe_implies;[exact FreeFrame|].
            intros old pos [Valid Outside] _ Same;subst old.
            exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc Valid).
   - intros old pos Outside Valid;split;assumption. }
 exists mf,last,digits;split.
 - eapply eval_funcall_internal with (e:=wnaf_env bs)
    (le1:=wnaf_entry5_temps b base (Vptr ba (Ptrofs.repr abase))) (le2:=lef) (m1:=mi) (m2:=mr)
    (out:=Out_return (Some (Vint (Int.repr (last+1)),tint))).
   + apply wnaf_entry5;exact Alloc.
   + rewrite wnaf_body_to_memset_source;eapply exec_statement_prefix_then_last.
     * apply exec_wnaf_before_memset5;reflexivity.
     * unfold wnaf_at_memset;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact ZeroStep|exact Tail].
   + split;[discriminate|reflexivity].
   + rewrite wnaf_local_blocks;cbn [Mem.free_list];rewrite Free;reflexivity.
 - split;[exact ArrayF|];split;[exact Bound|];split.
   + intros pos Range;eapply Mem.perm_free_1;[exact Free|left;exact OutputPrivate|].
     apply TailKeep,OutputZ;exact Range.
   + split;[exact WholeFrame|];split.
     * eapply scalar_at_lframe;[exact Input|exact WholeFrame|intros;left;exact Separate].
     * split.
       -- intros old pos k p Perm.
          assert (NotPrivate:old<>bs).
          { intro Same;subst old;exact (Mem.fresh_block_alloc _ _ _ _ _ Alloc (Mem.perm_valid_block _ _ _ _ _ Perm)). }
          eapply Mem.perm_free_1;[exact Free|left;exact NotPrivate|].
          apply TailKeep;apply (proj1 (ZeroPerm old pos k p));eapply Mem.perm_alloc_1;[exact Alloc|exact Perm].
       -- split;[|exact Literal].
          eapply preserved_trans;[eapply alloc_preserved;exact Alloc|].
          eapply preserved_trans;[eapply storebytes_preserved;exact Store|].
          eapply preserved_trans;[eapply wnaf_post_memset_readonly;exact Tail|].
          eapply free_preserved;exact Free.
Qed.

(** Compatibility specialization: the previously published full contract. *)
Theorem eval_wnaf_literal5 (Model:memset_model) sb (word:Ty.tySem (Word 7)) m ba abase b :
 scalar_at m ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) ->
 ba<>b -> Mem.range_perm m b 0 516 Cur Freeable -> exists mf last digits,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ecmult_wnaf)
  [Vptr b Ptrofs.zero;Vint (Int.repr 129);Vptr ba (Ptrofs.repr abase);Vint (Int.repr 5)]
  E0 mf (Vint (Int.repr (last+1))) /\
 wnaf_array_state mf b 0 129 5 (wnaf5_input_sign sb) 129 last digits /\
 0<=last+1<=129 /\ Mem.range_perm mf b 0 516 Cur Freeable /\
 lframe (fun old _=>old<>b) m mf /\
 scalar_at mf ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) /\
 keeps_permissions m mf /\ readonly_preserved m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb,word))=
  rev (map (fun i=>wnaf5_input_sign sb*digits (Z.of_nat i)) (seq 0 129)).
Proof.
 intros Input Separate Owned.
 destruct (eval_wnaf_literal5_slice Model sb word m ba abase b 0 Input Separate
  ltac:(lia) (Z.divide_0_r 4) ltac:(change (516<=18446744073709551615);lia) Owned)
  as (mf & last & digits & Call & Array & Bound & Free & Frame & Source & Keep & Readonly & Literal).
 exists mf,last,digits;split;[exact Call|];split;[exact Array|];split;[exact Bound|];split;[exact Free|];split.
 - eapply lframe_implies;[exact Frame|intros old pos Outside _;left;exact Outside].
 - split;[exact Source|];split;[exact Keep|];split;assumption.
Qed.
