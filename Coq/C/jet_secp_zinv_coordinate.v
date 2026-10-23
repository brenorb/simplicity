(** Shared original X/Y preparation with both raw point coordinates loose. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp C.jet_secp_fe_nv C.jet_secp_fe_math
 C.jet_secp_multiply_normalize_bridge C.jet_secp_multiply_finish_product C.jet_secp_point_mul_storage
 C.jet_secp_square_columns C.jet_secp_field_mul_small C.jet_secp_curve_square
 C.jet_secp_curve_statements C.jet_secp_field_weak_loose C.jet_secp_mixed_copy_weak
 C.jet_secp_mixed_copy_weak_loose C.jet_secp_mixed_affine_product
 C.jet_secp_curve_frame C.jet_secp_field_read_preservation C.jet_secp_statement_prefix.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge point_mul_words weak_loose_words.
Definition zinv_coordinate_statements (y : bool) :=
 [mixed_copy_coordinate y;mixed_weak_coordinate y;mixed_affine_call y].
Definition zinv_coordinate_frame (y : bool) (bc bo ba bz bx : block) pos :=
 bx<>bc /\ bx<>bo /\ bx<>bz /\
 (bx<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos).

Theorem exec_zinv_coordinate (y : bool) w a t e le m bp ba bc bo bz :
 le!_a=Some (Vptr bp Ptrofs.zero) -> le!_b=Some (Vptr ba Ptrofs.zero) ->
 e!(if y then _s1 else _u1)=Some (bc,curve_fe_type) ->
 e!(if y then _s2 else _u2)=Some (bo,curve_fe_type) -> e!_z12=Some (bz,curve_fe_type) ->
 e!_secp256k1_fe_normalize_weak=None -> e!_secp256k1_fe_mul=None ->
 NoDup [bp;ba;bc;bo;bz] ->
 (forall i,(i<5)%nat -> Int64.unsigned (w i)<=2^60) -> square_input_bounds a -> square_input_bounds t ->
 fe_at m bp (curve_square_offset y) (words5 w) -> fe_at m ba (curve_square_offset y) (words5 a) ->
 fe_at m bz 0 (words5 t) -> Mem.range_perm m bp 0 128 Cur Freeable ->
 Mem.range_perm m ba 0 88 Cur Freeable -> Mem.range_perm m bc 0 40 Cur Freeable ->
 Mem.range_perm m bo 0 40 Cur Freeable -> Mem.range_perm m bz 0 40 Cur Freeable -> exists mf,
 Clight2.exec_stmt secp_ge e le m (statement_sequence (zinv_coordinate_statements y) Sskip) E0 le mf Out_normal /\
 fe_at mf bp (curve_square_offset y) (words5 w) /\ fe_at mf ba (curve_square_offset y) (words5 a) /\
 fe_at mf bz 0 (words5 t) /\ fe_at mf bc 0 (words5 (weak_loose_words w)) /\
 fe_at mf bo 0 (words5 (point_mul_words a t)) /\
 Mem.range_perm mf bp 0 128 Cur Freeable /\ Mem.range_perm mf ba 0 88 Cur Freeable /\
 Mem.range_perm mf bc 0 40 Cur Freeable /\ Mem.range_perm mf bo 0 40 Cur Freeable /\ Mem.range_perm mf bz 0 40 Cur Freeable /\
 radix_value (weak_loose_words w) mod feP=radix_value w mod feP /\
 mul_small_input_bounds (weak_loose_words w) /\
 radix_value (point_mul_words a t) mod feP=(radix_value a*radix_value t) mod feP /\
 square_input_bounds (point_mul_words a t) /\ lframe (zinv_coordinate_frame y bc bo ba bz) m mf.
Proof.
 intros HA HB EC EO EZ EW EM Sep BW BA BT W A T PF AF CF OF ZF.
 repeat rewrite NoDup_cons_iff in Sep;cbn [In] in Sep.
 assert (W' : fe_at m bp (if y then 40 else 0) (words5 w)) by (destruct y;exact W).
 destruct (exec_mixed_copy_weak_loose e le m bp bc y w HA EC EW ltac:(intuition congruence) BW W' PF CF)
   as (mc & mi & Copy & Weak & C & CFI & WI & PFI & ValueW & TightW & FI).
 assert (AI : fe_at mi ba (curve_square_offset y) (words5 a)).
 { eapply field_at_lframe;[exact A|exact FI|intros;intuition congruence]. }
 assert (TI : fe_at mi bz 0 (words5 t)).
 { eapply field_at_lframe;[exact T|exact FI|intros;intuition congruence]. }
 assert (AFI : Mem.range_perm mi ba 0 88 Cur Freeable).
 { eapply curve_keep_free;[lia|exact AF|exact FI|intros;intuition congruence]. }
 assert (OFI : Mem.range_perm mi bo 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact OF|exact FI|intros;intuition congruence]. }
 assert (ZFI : Mem.range_perm mi bz 0 40 Cur Freeable).
 { eapply curve_keep_free;[lia|exact ZF|exact FI|intros;intuition congruence]. }
 destruct (exec_mixed_affine_call y a t e le mi bo ba bz EO EZ HB EM BA BT
   ltac:(intuition congruence) ltac:(intuition congruence) ltac:(intuition congruence) OFI AI AFI TI ZFI)
   as (mf & Mul & O & AOut & TOut & OFF & AFF & ZFF & ValueO & BoundO & FM).
 assert (OutP : forall pos,bp<>bo /\ bp<>bz /\ (bp<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos))
   by (intro pos;repeat split;try (left;intuition congruence);intuition congruence).
 assert (OutC : forall pos,bc<>bo /\ bc<>bz /\ (bc<>ba \/ pos<curve_square_offset y \/ curve_square_offset y+40<=pos))
   by (intro pos;repeat split;try (left;intuition congruence);intuition congruence).
 assert (WF : fe_at mf bp (curve_square_offset y) (words5 w)).
 { eapply field_at_lframe;[destruct y;exact WI|exact FM|exact OutP]. }
 pose proof (field_at_lframe _ _ _ _ _ _ C FM OutC) as COut.
 pose proof (curve_keep_free _ _ _ _ 128 ltac:(lia) PFI FM OutP) as PFF.
 pose proof (curve_keep_free _ _ _ _ 40 ltac:(lia) CFI FM OutC) as CFF.
 exists mf;split.
 - unfold zinv_coordinate_statements;cbn [statement_sequence].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mc);[exact Copy|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mi);[exact Weak|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0) (le1:=le) (m1:=mf);[exact Mul|constructor].
 - split;[exact WF|];split;[exact AOut|];split;[exact TOut|];split;[exact COut|];split;[exact O|];
   split;[exact PFF|];split;[exact AFF|];split;[exact CFF|];split;[exact OFF|];split;[exact ZFF|];
   split;[exact ValueW|];split;[exact TightW|];split;[exact ValueO|];split;[exact BoundO|].
   eapply lframe_trans.
   + eapply lframe_implies;[exact FI|];intros bx pos (NC & NO & NZ & NA) Valid;exact NC.
   + eapply lframe_implies;[exact FM|];intros bx pos (NC & NO & NZ & NA) Valid;split;[exact NO|];split;assumption.
Qed.
