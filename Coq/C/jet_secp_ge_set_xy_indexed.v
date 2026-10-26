(** Whole original affine constructor at an arbitrary aligned table offset.
    Only the selected entry's X/Y/flag bytes change; all permissions and the
    surrounding table entries are preserved. The source is an actual point. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_exec C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv
 C.jet_secp_affine_fields C.jet_secp_curve_statements C.jet_secp_curve_frame C.jet_secp_field_read_preservation
 C.jet_secp_ge_set_xy C.jet_secp_field_copy_owned C.jet_secp_local_regions
 C.jet_secp_multiply_normalize_bridge C.jet_secp_closed_helpers C.jet_clight_internal_preserve.
Import ListNotations Values Ctypes.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition ge_set_xy_indexed_temps bd base bp :=
 PTree.set _y (Vptr bp (Ptrofs.repr 40)) (PTree.set _x (Vptr bp Ptrofs.zero)
 (PTree.set _r (Vptr bd (Ptrofs.repr base)) (create_undef_temps (fn_temps f_secp256k1_ge_set_xy)))).

Theorem eval_ge_set_xy_indexed x y m bd base bp :
 bd<>bp -> 0<=base -> (8|base) -> base+88<=Ptrofs.max_unsigned ->
 fe_at m bp 0 (words5 x) -> fe_at m bp 40 (words5 y) ->
 Mem.range_perm m bd base (base+88) Cur Freeable -> exists mf,
 Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xy)
  [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero;Vptr bp (Ptrofs.repr 40)] E0 mf Vundef /\
 fe_at mf bd base (words5 x) /\ fe_at mf bd (base+40) (words5 y) /\
 Mem.load Mint32 mf bd (base+80)=Some (Vint Int.zero) /\
 Mem.range_perm mf bd base (base+88) Cur Freeable /\
 (forall b pos k p,Mem.perm mf b pos k p <-> Mem.perm m b pos k p) /\
 lframe (fun b pos=>b<>bd \/ pos<base \/ base+84<=pos) m mf /\ readonly_preserved m mf.
Proof.
 intros Sep Base Align Max X Y Free.
 set (le:=ge_set_xy_indexed_temps bd base bp).
 assert (R:le!_r=Some (Vptr bd (Ptrofs.repr base))) by reflexivity.
 assert (TX:le!_x=Some (Vptr bp Ptrofs.zero)) by reflexivity.
 assert (TY:le!_y=Some (Vptr bp (Ptrofs.repr 40))) by reflexivity.
 assert (Access:Mem.valid_access m Mint32 bd (base+80) Writable).
 { split.
   - intros pos Range;apply (freeable_range_writable m bd base (base+88) Free).
     change (base+80<=pos<base+80+4) in Range;lia.
   - change (4|base+80);destruct Align as [k Eq];exists (2*k+20);lia. }
 destruct (Mem.valid_access_store m Mint32 bd (base+80) (Vint Int.zero) Access) as (m1 & Store).
 assert (F1:Mem.range_perm m1 bd base (base+88) Cur Freeable) by
  (intros pos Range;eapply Mem.perm_store_1;[exact Store|apply Free;exact Range]).
 assert (L1:lframe (fun b pos=>b<>bd \/ pos<base+80 \/ base+84<=pos) m m1).
 { apply lframe_unchanged;eapply Mem.store_unchanged_on;[exact Store|].
   intros pos Range;change (base+80<=pos<base+80+4) in Range;
    intros [NE|[Low|High]];[contradiction|lia|lia]. }
 assert (X1:fe_at m1 bp 0 (words5 x)) by
  (eapply field_at_lframe;[exact X|exact L1|];intros;left;congruence).
 assert (Y1:fe_at m1 bp 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y|exact L1|];intros;left;congruence).
 assert (LXVal:eval_lvalue secp_ge empty_env le m1 (ge_set_xy_field _x curve_fe_type) bd (Ptrofs.repr base) Full).
 { pose proof (eval_affine_pointer_field le m1 bd base _r _x 0 curve_fe_type
    ltac:(left;reflexivity) Base Max R) as LV;rewrite Z.add_0_r in LV;exact LV. }
 destruct (exec_field_copy_owned empty_env le m1 (ge_set_xy_input _x) (ge_set_xy_field _x curve_fe_type)
   bp 0 bd base x eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TX|apply deref_loc_copy;reflexivity])
   LXVal (not_eq_sym Sep) X1 Base Align ltac:(lia)
   ltac:(intros pos Range;apply F1;lia)) as (m2 & CopyX & XO & PermX & LX).
 assert (Y2:fe_at m2 bp 40 (words5 y)) by
  (eapply field_at_lframe;[exact Y1|exact LX|];intros;left;congruence).
 assert (F2:Mem.range_perm m2 bd base (base+88) Cur Freeable).
 { intros pos Range;apply (proj2 (PermX bd pos Cur Freeable));apply F1;exact Range. }
 assert (AlignY:(8|base+40)) by (destruct Align as [k Eq];exists (k+5);lia).
 destruct (exec_field_copy_owned empty_env le m2 (ge_set_xy_input _y) (ge_set_xy_field _y curve_fe_type)
   bp 40 bd (base+40) y eq_refl eq_refl
   ltac:(eapply eval_Elvalue;[apply eval_Ederef;apply eval_Etempvar;exact TY|apply deref_loc_copy;reflexivity])
   ltac:(apply eval_affine_pointer_field;[right;left;reflexivity|exact Base|exact Max|exact R])
   (not_eq_sym Sep) Y2 ltac:(lia) AlignY ltac:(lia)
   ltac:(intros pos Range;apply F2;lia)) as (mf & CopyY & YO & PermY & LY).
 assert (XF:fe_at mf bd base (words5 x)).
 { eapply curve_keep_field_range;[reflexivity|exact XO|exact LY|];intros pos Range;right;left;lia. }
 assert (FF:Mem.range_perm mf bd base (base+88) Cur Freeable).
 { intros pos Range;apply (proj2 (PermY bd pos Cur Freeable));apply F2;exact Range. }
 assert (V1:Mem.valid_block m1 bd) by (eapply Mem.perm_valid_block;exact (F1 base ltac:(lia))).
 assert (V2:Mem.valid_block m2 bd) by (eapply Mem.perm_valid_block;exact (F2 base ltac:(lia))).
 assert (Flag:Mem.load Mint32 mf bd (base+80)=Some (Vint Int.zero)).
 { rewrite (proj1 LY Mint32 bd (base+80) V2),(proj1 LX Mint32 bd (base+80) V1).
   - exact (Mem.load_store_same _ _ _ _ _ _ Store).
   - intros pos Range;change (base+80<=pos<base+80+4) in Range;right;right;lia.
   - intros pos Range;change (base+80<=pos<base+80+4) in Range;right;right;lia. }
 assert (Frame:lframe (fun b pos=>b<>bd \/ pos<base \/ base+84<=pos) m mf).
 { eapply lframe_trans.
   - eapply lframe_implies;[exact L1|];intros b pos [NE|[Low|High]] Valid;
      [left;exact NE|right;left;lia|right;right;exact High].
   - eapply lframe_trans;eapply lframe_implies;[exact LX| |exact LY|];
      intros b pos [NE|[Low|High]] Valid;
      [left;exact NE|right;left;lia|right;right;lia|
       left;exact NE|right;left;lia|right;right;lia]. }
 assert (Body:Clight2.exec_stmt secp_ge empty_env le m (fn_body f_secp256k1_ge_set_xy) E0 le mf Out_normal).
 { eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m1) (le1:=le).
   - eapply exec_Sassign with (loc:=bd) (ofs:=Ptrofs.repr (base+80)) (bf:=Full)
      (v2:=Vint Int.zero) (v:=Vint Int.zero).
     + apply eval_affine_pointer_field;[right;right;left;reflexivity|exact Base|exact Max|exact R].
     + constructor.
     + reflexivity.
     + eapply assign_loc_value with (chunk:=Mint32);[reflexivity|].
       cbn [Mem.storev];rewrite Ptrofs.unsigned_repr by lia;exact Store.
   - eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (m1:=m2) (le1:=le);[exact CopyX|exact CopyY]. }
 assert (Call:Clight2.eval_funcall secp_ge m (Internal f_secp256k1_ge_set_xy)
   [Vptr bd (Ptrofs.repr base);Vptr bp Ptrofs.zero;Vptr bp (Ptrofs.repr 40)] E0 mf Vundef).
 { eapply eval_funcall_internal with (e:=empty_env) (le1:=le) (le2:=le) (m1:=m) (m2:=mf) (out:=Out_normal).
   - assert (OK:fn_okb f_secp256k1_ge_set_xy=true) by reflexivity.
     destruct (fn_okb_true _ OK) as (Vars & Params & Disjoint).
     constructor;[exact Vars|exact Params|exact Disjoint|constructor|reflexivity].
   - exact Body.
   - reflexivity.
   - reflexivity. }
 exists mf;split;[exact Call|];split;[exact XF|];split;[exact YO|];split;[exact Flag|];split;[exact FF|];split.
 - intros b pos k p;rewrite (PermY b pos k p),(PermX b pos k p);split;intro Perm;
    [eapply Mem.perm_store_2|eapply Mem.perm_store_1];eassumption.
 - split;[exact Frame|];eapply (secp_closed_function_preserved f_secp256k1_ge_set_xy);
    [reflexivity|reflexivity|exact Call].
Qed.
