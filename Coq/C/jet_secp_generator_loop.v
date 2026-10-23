(** Bounded induction for the original descending generator loop. *)
From Coq Require Import ZArith Lia List.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Alg.
Require Simplicity.Bit.
Require Import C.jet_readBit_layout C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_curve_statements C.jet_secp_fe_math C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product C.jet_secp_square_columns C.jet_secp_generator_globals
 C.jet_secp_wnaf_literal C.jet_secp_wnaf_literal_array C.jet_secp_wnaf_literal_values
 C.jet_secp_generate_literal C.jet_secp_double_literal C.jet_secp_rescale_literal C.jet_secp_canonical_zero.
Require Import C.jet_secp_generator_digit_control C.jet_secp_generator_loop_control C.jet_secp_generator_iteration.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge generator_digit_action literal_gej_double rescale_field_output.

Fixpoint generator_loop_result (count : nat) (digits1 digits128 : Z->Ty.tySem literal_wnaf_digit)
 (point : Ty.tySem literal_generator_jacobian) := match count with
 | Datatypes.O=>point
 | Datatypes.S count=>generator_loop_result count digits1 digits128
     (generator_digit_action true (digits128 (Z.of_nat count))
       (generator_digit_action false (digits1 (Z.of_nat count)) (@literal_gej_double Alg.CoreFunSem point)))
 end.

Section Loop.
Variable e : env.
Variables bp ba bb b1 b128 : block.
Variable inv : nat->int64.
Variables bits1 bits128 : Z.
Variables digits1 digits128 : Z->Ty.tySem literal_wnaf_digit.
Hypothesis Len1 : 0<=bits1<=129.
Hypothesis Len128 : 0<=bits128<=129.
Hypothesis Sep : NoDup [bp;ba;bb;b1;b128].
Hypothesis Valid1 : forall j,0<=j<129 -> wnaf_literal_valid (digits1 j).
Hypothesis Valid128 : forall j,0<=j<129 -> wnaf_literal_valid (digits128 j).
Hypothesis Absent1 : forall j,0<=j<129 -> bits1<=j -> digits1 j=inl tt.
Hypothesis Absent128 : forall j,0<=j<129 -> bits128<=j -> digits128 j=inl tt.
Hypothesis Array1 : e!_wnaf_ng_1=Some (b1,tarray tint 129).
Hypothesis Array128 : e!_wnaf_ng_128=Some (b128,tarray tint 129).
Hypothesis EA : e!_tmpa=Some (ba,curve_ge_type).
Hypothesis EZ : e!_Z=Some (bb,curve_fe_type).
Hypothesis EL : e!_secp256k1_ecmult_table_get_ge_storage=None.
Hypothesis EAdd : e!_secp256k1_gej_add_zinv_var=None.
Hypothesis ED : e!_secp256k1_gej_double_var=None.
Hypothesis ET1 : e!(generator_table_id false)=None.
Hypothesis ET128 : e!(generator_table_id true)=None.
Hypothesis BI : square_input_bounds inv.
Hypothesis One : radix_value inv mod feP=1.

Theorem exec_generator_loop count : (count<=129)%nat ->
 forall le m x y z (ax ay az : Ty.tySem (Word 8)),
 (forall h,generator_table_state h m) ->
 le!_r=Some (Vptr bp Ptrofs.zero) -> le!_no=Some (Vlong Int64.zero) ->
 le!_i=Some (Vint (Int.repr (Z.of_nat count-1))) ->
 le!_bits_ng_1=Some (Vint (Int.repr bits1)) -> le!_bits_ng_128=Some (Vint (Int.repr bits128)) ->
 (forall j,0<=j<bits1 -> Mem.load Mint32 m b1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digits1 j))))) ->
 (forall j,0<=j<bits128 -> Mem.load Mint32 m b128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digits128 j))))) ->
 square_input_bounds x -> square_input_bounds y -> square_input_bounds z ->
 ((rescale_field_output x,rescale_field_output y),rescale_field_output z)=((ax,ay),az) ->
 Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool (@canonical_fe_is_zero Alg.CoreFunSem az)))) ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) -> fe_at m bp 80 (words5 z) ->
 fe_at m bb 0 (words5 inv) ->
 Mem.range_perm m bp 0 128 Cur Freeable -> Mem.range_perm m ba 0 88 Cur Freeable ->
 Mem.range_perm m bb 0 40 Cur Freeable -> exists lef mf ox oy oz,
 Clight2.exec_stmt secp_ge e le m generator_descending_loop E0 lef mf Out_normal /\
 lef!_r=Some (Vptr bp Ptrofs.zero) /\ lef!_i=Some (Vint (Int.repr (-1))) /\
 fe_at mf bp 0 (words5 ox) /\ fe_at mf bp 40 (words5 oy) /\ fe_at mf bp 80 (words5 oz) /\
 Mem.load Mint32 mf bp 120=Some (Vint (bit_int (Bit.toBool
   (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output oz))))) /\
 fe_at mf bb 0 (words5 inv) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bb 0 40 Cur Freeable /\
 square_input_bounds ox /\ square_input_bounds oy /\ square_input_bounds oz /\
 ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
   generator_loop_result count digits1 digits128 ((ax,ay),az) /\
 (forall h,generator_table_state h mf) /\ lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf.
Proof.
 induction count as [|count IH];intros Count le m x y z ax ay az Tables PR No PI PL1 PL128
   Load1 Load128 BX BY BZ Repr Flag X Y ZAt Inv PF AF IF.
 - exists le,m,x,y,z;split;[apply exec_generator_loop_done;exact PI|].
   assert (AZ : rescale_field_output z=az) by congruence.
   assert (FlagO : Mem.load Mint32 m bp 120=Some (Vint (bit_int (Bit.toBool
     (@canonical_fe_is_zero Alg.CoreFunSem (rescale_field_output z)))))) by (rewrite AZ;exact Flag).
   assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m m) by apply lframe_refl.
   repeat first [assumption|split].
 - assert (Index : 0<=Z.of_nat count<129) by (pose proof (Nat2Z.is_nonneg count);lia).
   assert (PIC : le!_i=Some (Vint (Int.repr (Z.of_nat count)))).
   { replace (Z.of_nat count) with (Z.of_nat (S count)-1) by (rewrite Nat2Z.inj_succ;lia);exact PI. }
   destruct (exec_generator_iteration (digits1 (Z.of_nat count)) (digits128 (Z.of_nat count)) x y z inv ax ay az
     e le m (Z.of_nat count) bits1 bits128 b1 b128 bp ba bb
     Index Len1 Len128 (Valid1 _ Index) (Valid128 _ Index) Sep Tables PR No PIC PL1 PL128
     Array1 Array128 EA EZ EL EAdd ED ET1 ET128
     ltac:(intro Range;apply Load1;lia) ltac:(intro Range;apply Load128;lia)
     (Absent1 _ Index) (Absent128 _ Index) BX BY BZ BI One Repr Flag X Y ZAt Inv PF AF IF)
     as (mi & ix & iy & iz & Body & XI & YI & ZI & FlagI & InvI & PFI & AFI & IFI & BXI & BYI & BZI & LiteralI & TablesI & FrameI).
   set (li:=generator_digit_temps true
     (generator_digit_temps false (PTree.set _np (Vlong Int64.zero) le) (Z.of_nat count) bits1 (digits1 (Z.of_nat count)))
     (Z.of_nat count) bits128 (digits128 (Z.of_nat count))) in *.
   assert (Keep : forall id,In id [_r;_no;_i;_bits_ng_1;_bits_ng_128] -> li!id=le!id).
   { intros id Member;repeat destruct Member as [Member|Member];try contradiction;subst id;
       unfold li;rewrite generator_digit_temps_other by discriminate;
       rewrite generator_digit_temps_other by discriminate;rewrite PTree.gso by discriminate;reflexivity. }
   set (ln:=PTree.set _i (Vint (Int.repr (Z.of_nat count-1))) li).
   assert (PRN : ln!_r=Some (Vptr bp Ptrofs.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;rewrite Keep by (cbn [In];tauto);exact PR. }
   assert (NoN : ln!_no=Some (Vlong Int64.zero)).
   { unfold ln;rewrite PTree.gso by discriminate;rewrite Keep by (cbn [In];tauto);exact No. }
   assert (PL1N : ln!_bits_ng_1=Some (Vint (Int.repr bits1))).
   { unfold ln;rewrite PTree.gso by discriminate;rewrite Keep by (cbn [In];tauto);exact PL1. }
   assert (PL128N : ln!_bits_ng_128=Some (Vint (Int.repr bits128))).
   { unfold ln;rewrite PTree.gso by discriminate;rewrite Keep by (cbn [In];tauto);exact PL128. }
   pose proof Sep as Sep0;repeat rewrite NoDup_cons_iff in Sep0;cbn [In] in Sep0.
   assert (Outside1 : b1<>bp /\ b1<>ba /\ b1<>bb) by intuition congruence.
   assert (Outside128 : b128<>bp /\ b128<>ba /\ b128<>bb) by intuition congruence.
   assert (Load1I : forall j,0<=j<bits1 -> Mem.load Mint32 mi b1 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digits1 j))))).
   { intros j Range;pose proof (Load1 j Range) as Load;rewrite (proj1 FrameI Mint32 b1 (4*j));[exact Load| |].
     - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
         [eapply Mem.load_valid_access;exact Load|constructor].
     - intros;exact Outside1. }
   assert (Load128I : forall j,0<=j<bits128 -> Mem.load Mint32 mi b128 (4*j)=Some (Vint (Int.repr (wnaf_literal_value (digits128 j))))).
   { intros j Range;pose proof (Load128 j Range) as Load;rewrite (proj1 FrameI Mint32 b128 (4*j));[exact Load| |].
     - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
         [eapply Mem.load_valid_access;exact Load|constructor].
     - intros;exact Outside128. }
   destruct (IH ltac:(lia) ln mi ix iy iz (rescale_field_output ix) (rescale_field_output iy) (rescale_field_output iz)
     TablesI PRN NoN ltac:(unfold ln;apply PTree.gss) PL1N PL128N Load1I Load128I
     BXI BYI BZI eq_refl FlagI XI YI ZI InvI PFI AFI IFI)
     as (lef & mf & ox & oy & oz & Rest & PRF & PIF & XO & YO & ZO & FlagO & InvO & PFO & AFO & IFO &
       BXO & BYO & BZO & LiteralO & TablesO & FrameO).
   assert (Frame : lframe (fun b _=>b<>bp /\ b<>ba /\ b<>bb) m mf) by (eapply lframe_trans;eassumption).
   assert (Literal : ((rescale_field_output ox,rescale_field_output oy),rescale_field_output oz)=
     generator_loop_result (S count) digits1 digits128 ((ax,ay),az)).
   { rewrite LiteralI in LiteralO;exact LiteralO. }
   exists lef,mf,ox,oy,oz;split;[|repeat first [assumption|split]].
   eapply exec_generator_loop_join with (i:=Z.of_nat count) (lei:=li) (mi:=mi);
     [exact Index|exact PIC| |exact Body|exact Rest].
   rewrite Keep by (cbn [In];tauto);exact PIC.
Qed.
End Loop.
