(** Original parity test and conditional magnitude-one negation at affine Y. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Cop Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_expr C.jet_sx_state C.jet_sx_eval C.jet_sx_mem C.jet_sx_rep.
Require Import C.jet_secp_linkage C.jets_secp C.jet_secp_fns C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_curve_statements C.jet_secp_decompress_statements C.jet_secp_affine_odd_y
 C.jet_secp_affine_negate_owned C.jet_secp_affine_weak_exec C.jet_secp_point_write_run
 C.jet_secp_field_negate_values C.jet_secp_field_negate_storage C.jet_secp_write_fe_numeric
 C.jet_secp_affine_normalize_y C.jet_secp_square_columns C.jet_secp_multiply_normalize_bridge
 C.jet_secp_multiply_finish_product.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Definition decompress_parity_temps le value := PTree.set _t'2
 (Vint (Int.repr (Z.b2z (Z.testbit value 0)))) le.
Definition decompress_parity_limbs value (odd : bool) := if xorb (Z.testbit value 0) odd
 then negate_values (write_fe_rho value 0) else map Int64.repr (fe_limbs_of value).

Theorem exec_decompress_parity_owned e le m b value (odd : bool) :
 le!_r=Some (Vptr b Ptrofs.zero) -> le!_odd=Some (Vint (if odd then Int.one else Int.zero)) ->
 e!_secp256k1_fe_is_odd=None -> e!_secp256k1_fe_negate=None ->
 fe_at m b 40 (map Int64.repr (fe_limbs_of value)) -> Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m decompress_odd_test E0 (decompress_parity_temps le value) mf Out_normal /\
 fe_at mf b 40 (decompress_parity_limbs value odd) /\ Mem.range_perm mf b 0 88 Cur Freeable /\
 lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros HR HO EO EN Field Free.
 destruct (eval_affine_odd_y_value m b value Field Free) as (mi & Odd & Source & Owned & FrameO).
 assert (ReadR : (decompress_parity_temps le value)!_r=Some (Vptr b Ptrofs.zero)).
 { unfold decompress_parity_temps;rewrite PTree.gso by discriminate;exact HR. }
 assert (ReadOdd : (decompress_parity_temps le value)!_odd=Some (Vint (if odd then Int.one else Int.zero))).
 { unfold decompress_parity_temps;rewrite PTree.gso by discriminate;exact HO. }
 assert (Call : Clight2.exec_stmt secp_ge e le m decompress_odd_call E0
  (decompress_parity_temps le value) mi Out_normal).
 { unfold decompress_odd_call,decompress_parity_temps;eapply exec_curve_call with
    (vargs:=[Vptr b (Ptrofs.repr 40)]) (v:=Vint (Int.repr (Z.b2z (Z.testbit value 0)))).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EO.
   - eapply eval_Econs.
     + apply eval_decompress_field_address;[right;left;reflexivity|exact HR].
     + reflexivity.
     + constructor.
   - exact Odd. }
 assert (Condition : eval_expr secp_ge e (decompress_parity_temps le value) mi
  (Ebinop One (Etempvar _t'2 tint) (Etempvar _odd tint) tint)
  (Vint (if xorb (Z.testbit value 0) odd then Int.one else Int.zero))).
 { eapply eval_Ebinop.
   - apply eval_Etempvar;unfold decompress_parity_temps;apply PTree.gss.
   - apply eval_Etempvar;exact ReadOdd.
   - destruct (Z.testbit value 0),odd;reflexivity. }
 destruct (xorb (Z.testbit value 0) odd) eqn:Flip.
 - destruct (eval_affine_negate_reader_owned AffineY mi b value Source Owned)
    as (mf & Negate & Output & OwnedF & FrameN0).
   assert (FrameN : lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) mi mf).
   { eapply lframe_implies;[exact FrameN0|].
     intros bx pos Outside _ (r & sh & d & ch & NS & HC & HB & Range).
     destruct r;[|destruct r;discriminate NS].
     injection NS as <-.
     cbn [affine_initial_regs affine_coordinate_offset affine_point_coordinate point_coordinate_offset
      rshape fst snd rcells u64_cells vars5 map cshape In] in HC.
     repeat destruct HC as [HC|HC];try contradiction;injection HC as <- <-;
      cbn [bas blk lay nth fst snd size_chunk] in HB,Range;
      destruct Outside as [Outside|[Outside|Outside]];congruence || lia. }
   exists mf;split.
   + unfold decompress_odd_test;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
     eapply exec_Sifthenelse with (v1:=Vint Int.one) (b:=true);[exact Condition|reflexivity|].
     unfold decompress_negate_stmt;eapply exec_curve_call with
      (vargs:=[Vptr b (Ptrofs.repr 40);Vptr b (Ptrofs.repr 40);Vint Int.one]) (v:=Vundef).
     * unfold secp_pure;repeat (first [left;reflexivity|right]).
     * exact EN.
     * eapply eval_Econs.
       -- apply eval_decompress_field_address;[right;left;reflexivity|exact ReadR].
       -- reflexivity.
       -- eapply eval_Econs.
          ++ apply eval_decompress_field_address;[right;left;reflexivity|exact ReadR].
          ++ reflexivity.
          ++ eapply eval_Econs;[constructor|reflexivity|constructor].
     * exact Negate.
   + unfold decompress_parity_limbs;rewrite Flip;split;[exact Output|];split;[exact OwnedF|].
     eapply lframe_trans;[exact FrameO|exact FrameN].
 - exists mi;split.
   + unfold decompress_odd_test;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
     eapply exec_Sifthenelse with (v1:=Vint Int.zero) (b:=false);[exact Condition|reflexivity|apply exec_Sskip].
   + unfold decompress_parity_limbs;rewrite Flip;split;[exact Source|];split;assumption.
Qed.

Definition decompress_success_tail := Ssequence decompress_normalize_stmt
 (Ssequence decompress_odd_test (Sreturn (Some (Econst_int Int.one tint)))).
Lemma decompress_rest_source : decompress_rest=Ssequence decompress_root_test decompress_success_tail.
Proof. reflexivity. Qed.

Theorem exec_decompress_success_tail e le m b w (odd : bool) :
 le!_r=Some (Vptr b Ptrofs.zero) -> le!_odd=Some (Vint (if odd then Int.one else Int.zero)) ->
 e!_secp256k1_fe_normalize_var=None -> e!_secp256k1_fe_is_odd=None -> e!_secp256k1_fe_negate=None ->
 square_input_bounds w -> fe_at m b 40 (words5 w) -> Mem.range_perm m b 0 88 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m decompress_success_tail E0
  (decompress_parity_temps le (radix_value w mod feP)) mf (Out_return (Some (Vint Int.one,tint))) /\
 fe_at mf b 40 (decompress_parity_limbs (radix_value w mod feP) odd) /\
 Mem.range_perm mf b 0 88 Cur Freeable /\ lframe (fun bx pos=>bx<>b \/ pos<40 \/ 80<=pos) m mf.
Proof.
 intros HR HO EV EO EN Bounds Field Free.
 destruct (eval_affine_nv_y_words w m b Bounds Field Free) as (mi & Normalize & Normal & Owned & FrameV).
 destruct (exec_decompress_parity_owned e le mi b (radix_value w mod feP) odd HR HO EO EN Normal Owned)
  as (mf & Parity & Output & OwnedF & FrameP).
 assert (Call : Clight2.exec_stmt secp_ge e le m decompress_normalize_stmt E0 le mi Out_normal).
 { unfold decompress_normalize_stmt;eapply exec_curve_call with
    (vargs:=[Vptr b (Ptrofs.repr 40)]) (v:=Vundef).
   - unfold secp_pure;repeat (first [left;reflexivity|right]).
   - exact EV.
   - eapply eval_Econs.
     + apply eval_decompress_field_address;[right;left;reflexivity|exact HR].
     + reflexivity.
     + constructor.
   - exact Normalize. }
 exists mf;split.
 - unfold decompress_success_tail.
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Call|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Parity|].
   apply exec_Sreturn_some;constructor.
 - split;[exact Output|];split;[exact OwnedF|].
   eapply lframe_trans;[exact FrameV|exact FrameP].
Qed.
