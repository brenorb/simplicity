(** Actual scalar copy, sign selection, complete window-5 loop and return.
    The caller supplies a zeroed digit buffer at this internal boundary;
    function entry, the original memset and final free are separate steps. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Clightdefs ClightBigstep Maps Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit.
Require Import C.jet_sx_mem C.jet_secp_linkage C.jets_secp
 C.jet_clight_internal_permissions C.jet_clight_internal_frame C.jet_clight_internal_preserve
 C.jet_secp_closed_helpers C.jet_secp_scalar_get_b32_storage
 C.jet_secp_scalar_get_b32_numeric C.jet_secp_wnaf_digit C.jet_secp_wnaf_control
 C.jet_secp_wnaf_loop C.jet_secp_wnaf_prepare C.jet_secp_wnaf_negative_prepare
 C.jet_secp_wnaf5_input C.jet_secp_wnaf5_signed_loop C.jet_secp_wnaf5_signed_array
 C.jet_secp_wnaf5_literal C.jet_secp_wnaf_literal_signed.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge.

Lemma exec_wnaf5_input_sign le m sb word bs b base :
 scalar_at m bs 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) ->
 Mem.range_perm m bs 0 32 Cur Freeable ->
 wnaf_loop_fields le 0 129 5 0 1 b base (-1) -> exists ls ms,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_sign_select E0 ls ms Out_normal /\
 scalar_at ms bs 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_magnitude sb word))) /\
 Mem.range_perm ms bs 0 32 Cur Freeable /\
 wnaf_loop_fields ls 0 129 5 0 (wnaf5_input_sign sb) b base (-1) /\
 lframe (fun old _=>old<>bs) m ms /\ keeps_permissions m ms.
Proof.
 intros Storage Free Fields;destruct sb as [u|u];destruct u.
 - destruct (wnaf5_input_positive word) as [Range Value].
   exists (wnaf_small_temps le),m;split.
   + eapply exec_wnaf_sign_small;[exact Range|exact Storage].
   + split;[exact Storage|];split;[exact Free|];split.
     * apply wnaf_small_fields;exact Fields.
     * split;[apply lframe_refl|apply keeps_permissions_refl].
 - destruct (wnaf5_input_negative word) as [Range Value].
   destruct (exec_wnaf_sign_large le m (wnaf5_input_scalar (inr tt) word) bs Range Storage Free)
    as (ms & Run & Output & FreeS & Frame & Keep & Readonly).
   exists (wnaf_negative_temps le),ms;split;[exact Run|].
   rewrite Value in Output;split;[exact Output|];split;[exact FreeS|];split.
   + apply wnaf_negative_fields with (sign:=1);exact Fields.
   + split;assumption.
Qed.

Lemma wnaf_post_memset_closed : closed_stmtb secp_closed_helpers wnaf_post_memset=Datatypes.true.
Proof. reflexivity. Qed.
Lemma wnaf_env_plain bs : plain_env (wnaf_env bs).
Proof.
 intros id b ty Lookup;unfold wnaf_env in Lookup.
 destruct (peq id _s) as [->|Different].
 - rewrite PTree.gss in Lookup;inversion Lookup;reflexivity.
 - rewrite PTree.gso in Lookup by exact Different;discriminate Lookup.
Qed.
Lemma wnaf_post_memset_readonly bs le m lef mf out :
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_post_memset E0 lef mf out ->
 readonly_preserved m mf.
Proof.
 intro Run;eapply secp_closed_stmt_preserved;
 [exact Run|apply wnaf_env_plain|exact wnaf_post_memset_closed].
Qed.

Theorem exec_wnaf5_post_memset le m sb word ba abase bs b base :
 le!_a=Some (Vptr ba (Ptrofs.repr abase)) ->
 wnaf_loop_fields le 0 129 5 0 1 b base (-1) ->
 scalar_at m ba abase (map Int64.repr (scalar_limbs_of (wnaf5_input_scalar sb word))) ->
 ba<>bs -> b<>bs -> Mem.range_perm m bs 0 32 Cur Freeable ->
 0<=base -> base+4*129<=Ptrofs.max_unsigned ->
 (forall i,0<=i<129 -> Mem.valid_access m Mint32 b (base+4*i) Writable) ->
 (forall i,0<=i<129 -> Mem.load Mint32 m b (base+4*i)=Some (Vint Int.zero)) ->
 exists lef mf carry last digits,
 Clight2.exec_stmt secp_ge (wnaf_env bs) le m wnaf_post_memset E0 lef mf
  (Out_return (Some (Vint (Int.repr (last+1)),tint))) /\
 wnaf_loop_fields lef 129 129 5 carry (wnaf5_input_sign sb) b base last /\
 (carry=0 \/ carry=1) /\
 scalar_at mf bs 0 (map Int64.repr (scalar_limbs_of (wnaf5_input_magnitude sb word))) /\
 Mem.range_perm mf bs 0 32 Cur Freeable /\
 wnaf_array_state mf b base 129 5 (wnaf5_input_sign sb) 129 last digits /\
 0<=last+1<=129 /\ lframe (fun old _=>old<>bs /\ old<>b) m mf /\
 keeps_permissions m mf /\
 map wnaf5_literal_value (literal_wnaf5_digits (sb,word))=
  rev (map (fun i=>wnaf5_input_sign sb*digits (Z.of_nat i)) (seq 0 129)).
Proof.
 intros HA Fields Input SourceSeparate OutputSeparate Free Base Max Access Zeros.
 destruct (exec_wnaf_scalar_copy le m (wnaf5_input_scalar sb word) ba abase bs HA SourceSeparate Input
  ltac:(intros pos Range;eapply Mem.perm_implies;[apply Free;exact Range|constructor]))
  as (mc & Copy & Copied & BlocksC & PermC & FrameC).
 assert (FreeC:Mem.range_perm mc bs 0 32 Cur Freeable).
 { intros pos Range;apply (proj2 (PermC bs pos Cur Freeable));apply Free;exact Range. }
 destruct (exec_wnaf5_input_sign le mc sb word bs b base Copied FreeC Fields)
  as (ls & ms & Select & Prepared & FreeS & FieldsS & FrameS & KeepS).
 assert (FrameCS:lframe (fun old _=>old<>bs) m ms) by (eapply lframe_trans;eassumption).
 assert (KeepC:keeps_permissions m mc).
 { intros old pos k p Perm;apply (proj2 (PermC old pos k p));exact Perm. }
 assert (KeepCS:keeps_permissions m ms) by (eapply keeps_permissions_trans;eassumption).
 assert (AccessS:forall i,0<=i<129 -> Mem.valid_access ms Mint32 b (base+4*i) Writable).
 { intros i Range;destruct (Access i Range) as [Cells Align];split;[|exact Align].
   intros pos R;apply KeepCS,Cells;exact R. }
 assert (ZerosS:forall i,0<=i<129 -> Mem.load Mint32 ms b (base+4*i)=Some (Vint Int.zero)).
 { intros i Range;rewrite (proj1 FrameCS).
   - apply Zeros;exact Range.
   - eapply Mem.valid_access_valid_block;eapply Mem.valid_access_implies;
     [apply Access;exact Range|constructor].
   - intros;exact OutputSeparate. }
 destruct (exec_wnaf5_loop_zero_signed ls ms (wnaf5_input_magnitude sb word)
  (wnaf5_input_sign sb) b base bs sb word (wnaf5_input_magnitude_range sb word)
  (wnaf5_input_sign_cases sb) (wnaf5_input_signed_value sb word) FieldsS Prepared OutputSeparate
  Base Max AccessS ZerosS)
  as (lef & mf & carry & last & digits & Loop & Final & Carry & StorageF & ArrayF & Bound
    & (BlocksF & PermF & FrameF) & Literal).
 exists lef,mf,carry,last,digits;split.
 - rewrite wnaf_post_memset_source;eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Copy|].
   eapply exec_Sseq_1 with (t1:=E0) (t2:=E0);[exact Select|exact Loop].
 - split;[exact Final|];split;[exact Carry|];split;[exact StorageF|];split.
   + intros pos Range;apply (proj1 (PermF bs pos Cur Freeable));apply FreeS;exact Range.
   + split;[exact ArrayF|];split;[exact Bound|];split.
     * eapply lframe_trans.
       -- eapply lframe_implies;[exact FrameCS|intros old pos [NS NB] _;exact NS].
       -- eapply lframe_implies;[exact FrameF|intros old pos [NS NB] _;exact NB].
     * split;[|exact Literal].
       intros old pos k p Perm;apply (proj1 (PermF old pos k p));apply KeepCS;exact Perm.
Qed.
