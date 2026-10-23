(** The original beta jet runs on every input from actual program startup.
    Fresh frames preserve the real readonly beta global; no readiness, frame
    or intermediate execution premise remains in the actual-init theorem. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Values Memory Globalenvs Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_encoding C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_sx_mem.
Require Import C.jet_frame_constructible C.jet_secp_beta_global C.jet_secp_beta_spec C.jet_secp_beta_public.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque beta_block literal_fe_multiply_beta encode secp_ge Genv.init_mem jets_secp.prog.

Lemma beta_words_readable m b :
 (forall i w, nth_error beta_words i = Some w ->
   Mem.load Mint64 m b (8 * Z.of_nat i) = Some (Vlong w)) ->
 Mem.range_perm m b 0 40 Cur Readable.
Proof.
 intros Loads pos Range.
 set (q := pos / 8).
 assert (Q0 : 0 <= q) by (unfold q; apply Z.div_pos; lia).
 assert (Q5 : q < 5) by (unfold q; apply Z.div_lt_upper_bound; lia).
 assert (Load : Mem.load Mint64 m b (8 * Z.of_nat (Z.to_nat q)) =
   Some (Vlong (nth (Z.to_nat q) beta_words Int64.zero))).
 { apply Loads, nth_error_nth'. rewrite beta_words_count; lia. }
 pose proof (proj1 (Mem.load_valid_access _ _ _ _ _ Load)) as Perm.
 apply Perm. change (size_chunk Mint64) with 8.
 rewrite Z2Nat.id by exact Q0.
 pose proof (Z.div_mod pos 8 ltac:(lia)) as Division.
 pose proof (Z.mod_pos_bound pos 8 ltac:(lia)) as Remainder.
 fold q in Division; lia.
Qed.

Theorem beta_initialized_old_blocks m m' :
 beta_initialized m ->
 (forall b, Mem.valid_block m b ->
   Mem.valid_block m' b /\
   (forall chunk ofs, Mem.load chunk m' b ofs = Mem.load chunk m b ofs) /\
   (forall ofs k p, Mem.perm m' b ofs k p -> Mem.perm m b ofs k p)) ->
 beta_initialized m'.
Proof.
 intros ((Valid & Readable & Words) & Bounds) Old.
 destruct (Old beta_block Valid) as (Valid' & Loads & Perms).
 assert (Words' : forall i w, nth_error beta_words i = Some w ->
   Mem.load Mint64 m' beta_block (8 * Z.of_nat i) = Some (Vlong w)).
 { intros i w Index; rewrite Loads; exact (Words i w Index). }
 pose proof (beta_words_readable m' beta_block Words') as Readable'.
 split; [exact (conj Valid' (conj Readable' Words'))|].
 intros ofs k p; split.
 - intro Final; apply (proj1 (Bounds ofs k p)); exact (Perms ofs k p Final).
 - intros (Range & Order); eapply Mem.perm_implies; [|exact Order].
   destruct k; [apply Mem.perm_cur_max; exact (Readable' ofs Range)|exact (Readable' ofs Range)].
Qed.

Theorem beta_runs_from_initialized (value : Ty.tySem (Word 8)) env m0 :
 beta_initialized m0 ->
 exists m bd bs bi bw edge mf,
 beta_initialized m /\
 frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
 write_frame_at m bd 0 bw 0 256 256 /\
 (forall b chunk ofs, Mem.valid_block m0 b -> Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_fe_multiply_beta)
   [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; env] E0 mf (Vint Int.one) /\
 finv m bd 0 bw 0 256 256 bi mf true (encode (@literal_fe_multiply_beta Alg.CoreFunSem value)) /\
 beta_initialized mf /\
 (forall b chunk ofs, Mem.valid_block m0 b -> Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).
Proof.
 intro Ready.
 destruct (jet_frames_constructible m0 (encode value) 256)
   as (m & bd & bs & bi & bw & edge & Base & Align & Fields & Input & Output & Sep & Old).
 { rewrite encode_length; change (256 <= 18446744073709551615); lia. }
 { change (0 <= 256 <= 18446744073709551615); lia. }
 assert (ReadyM : beta_initialized m).
 { eapply beta_initialized_old_blocks; [exact Ready|].
   intros b Valid; destruct (Old b Valid) as (HV & _ & _ & _ & _ & Loads & Perms).
   exact (conj HV (conj Loads Perms)). }
 pose proof Input as Reader; rewrite encode_word in Reader.
 destruct (eval_public_beta env m bd 0 bs 0 bw 0 256 256 bi edge 0 value
   ReadyM Output ltac:(lia) Base Align Fields Reader ltac:(lia)
   ltac:(change (256 <= 18446744073709551615); lia))
   as (mf & Call & Final & Frame & ReadyF).
 exists m,bd,bs,bi,bw,edge,mf.
 split; [exact ReadyM|]; split; [exact Fields|]; split; [exact Input|];
 split; [exact Output|]; split.
 - intros b chunk ofs Valid; destruct (Old b Valid) as (_ & _ & _ & _ & _ & Loads & _).
   exact (Loads chunk ofs).
 - split; [exact Call|]; split; [exact Final|]; split; [exact ReadyF|].
   intros b chunk ofs Valid; destruct (Old b Valid) as (HV & ND & _ & NI & NW & Loads & _).
   rewrite (proj1 Frame); [exact (Loads chunk ofs)|exact HV|].
   intros pos Range; unfold extA, fext; intros [[Eq|[Eq|Eq]] _]; contradiction.
Qed.

Theorem beta_runs_from_actual_init (value : Ty.tySem (Word 8)) env :
 exists mi m bd bs bi bw edge mf,
 Genv.init_mem jets_secp.prog = Some mi /\ beta_initialized mi /\
 beta_initialized m /\
 frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
 write_frame_at m bd 0 bw 0 256 256 /\
 (forall b chunk ofs, Mem.valid_block mi b -> Mem.load chunk m b ofs = Mem.load chunk mi b ofs) /\
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_fe_multiply_beta)
   [Vptr bd Ptrofs.zero; Vptr bs Ptrofs.zero; env] E0 mf (Vint Int.one) /\
 finv m bd 0 bw 0 256 256 bi mf true (encode (@literal_fe_multiply_beta Alg.CoreFunSem value)) /\
 beta_initialized mf /\
 (forall b chunk ofs, Mem.valid_block mi b -> Mem.load chunk mf b ofs = Mem.load chunk mi b ofs).
Proof.
 destruct beta_initialized_memory_exists as (mi & Init & Ready).
 destruct (beta_runs_from_initialized value env mi Ready)
   as (m & bd & bs & bi & bw & edge & mf & ReadyM & Fields & Input & Output & Before & Call & Final & ReadyF & After).
 exists mi,m,bd,bs,bi,bw,edge,mf.
 exact (conj Init (conj Ready (conj ReadyM (conj Fields (conj Input (conj Output
   (conj Before (conj Call (conj Final (conj ReadyF After)))))))))).
Qed.

