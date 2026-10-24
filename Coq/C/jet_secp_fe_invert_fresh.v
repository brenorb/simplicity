(** Original public field-invert execution from actual initialized program
    memory on freshly constructed frames, for every Word256 input. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Values Memory Globalenvs Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_encoding C.jet_secp_frame C.jet_secp_wrapper_run C.jet_secp_linkage C.jets_secp C.jet_sx_mem
 C.jet_frame_constructible C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_copy C.jet_secp_modinfo_fe_caller
 C.jet_secp_modinv_normalize62_exec C.jet_secp_scalar_lambda_init_exists
 C.jet_secp_fe_invert_lifecycle C.jet_secp_invert_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_fe_invert encode secp_ge Genv.init_mem jets_secp.prog modinfo_fe_block.

Lemma modinfo_fe_state_old_blocks m mf : modinfo_fe_state m ->
 (forall b,Mem.valid_block m b -> Mem.valid_block mf b /\
  (forall chunk ofs,Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\
  (forall ofs k p,Mem.perm mf b ofs k p -> Mem.perm m b ofs k p)) -> modinfo_fe_state mf.
Proof.
 intros((Valid & Read & Loads) & Readonly) Old.
 destruct(Old modinfo_fe_block Valid) as(ValidF & SameLoad & PermBack).
 assert(LoadsF:forall i w,nth_error modinfo_fe_words i=Some w ->
  Mem.load Mint64 mf modinfo_fe_block(8*Z.of_nat i)=Some(Vlong w)).
 { intros i w At;rewrite SameLoad;exact(Loads i w At). }
 assert(First:Mem.range_perm mf modinfo_fe_block 0 40 Cur Readable).
 { apply(norm62_words_readable mf modinfo_fe_block modinfo_fe_limb).
   intros i I;apply LoadsF;destruct i as[|[|[|[|[|i]]]]];try lia;reflexivity. }
 assert(ReadF:Mem.range_perm mf modinfo_fe_block 0 48 Cur Readable).
 { intros ofs Range;destruct(Z_lt_dec ofs 40);[apply First;lia|].
   pose proof(LoadsF 5%nat _ eq_refl) as Last;apply Mem.load_valid_access in Last.
   apply(proj1 Last);change(40<=ofs<48);lia. }
 split;[exact(conj ValidF(conj ReadF LoadsF))|].
 intros ofs Write;apply(Readonly ofs);exact(PermBack ofs Max Writable Write).
Qed.

Theorem field_invert_runs_from_initialized (value:Ty.tySem(Word 8)) env m0 :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong x]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_fe_state m0 -> exists m bd bs bi bw edge mf,
 modinfo_fe_state m /\ frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0(encode value) /\
 write_frame_at m bd 0 bw 0 256 256 /\
 (forall b chunk ofs,Mem.valid_block m0 b -> Mem.load chunk m b ofs=Mem.load chunk m0 b ofs) /\
 Clight2.eval_funcall secp_ge m(Internal f_simplicity_fe_invert)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env] E0 mf(Vint Int.one) /\
 finv m bd 0 bw 0 256 256 bi mf true(encode(@literal_fe_invert Alg.CoreFunSem value)) /\
 modinfo_fe_state mf /\
 (forall b chunk ofs,Mem.valid_block m0 b -> Mem.load chunk mf b ofs=Mem.load chunk m0 b ofs).
Proof.
 intros CountCall Ready.
 destruct(jet_frames_constructible m0(encode value)256)
  as(m & bd & bs & bi & bw & edge & Base & Align & Fields & Input & Output & Sep & Old).
 { rewrite encode_length;change(256<=18446744073709551615);lia. }
 { change(0<=256<=18446744073709551615);lia. }
 assert(ReadyM:modinfo_fe_state m).
 { eapply modinfo_fe_state_old_blocks;[exact Ready|].
   intros b Valid;destruct(Old b Valid) as(VF & _ & _ & _ & _ & Loads & Perms).
   exact(conj VF(conj Loads Perms)). }
 pose proof Input as ReaderInput;rewrite encode_word in ReaderInput.
 destruct(eval_secp_fe_invert_initialized env m bd 0 bs 0 bw 0 256 256 bi edge 0 value
  CountCall ReadyM Output ltac:(lia) Base Align Fields ReaderInput ltac:(lia)
  ltac:(change(256<=18446744073709551615);lia))
  as(mf & Call & Final & Frame & ReadyF & Preserved).
 exists m,bd,bs,bi,bw,edge,mf;split;[exact ReadyM|];split;[exact Fields|];split;[exact Input|];
 split;[exact Output|];split.
 - intros b chunk ofs Valid;destruct(Old b Valid) as(_ & _ & _ & _ & _ & Loads & _);exact(Loads chunk ofs).
 - split;[exact Call|];split;[exact Final|];split;[exact ReadyF|].
   intros b chunk ofs Valid;destruct(Old b Valid) as(VF & ND & _ & NI & NW & Loads & _).
   rewrite(proj1 Frame);[exact(Loads chunk ofs)|exact VF|].
   intros pos Range;unfold extA,fext;intros[[Same|[Same|Same]] _];contradiction.
Qed.

Theorem field_invert_runs_from_actual_init (value:Ty.tySem(Word 8)) env :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong x]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 exists mi m bd bs bi bw edge mf,
 Genv.init_mem jets_secp.prog=Some mi /\ modinfo_fe_state mi /\
 frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0(encode value) /\
 write_frame_at m bd 0 bw 0 256 256 /\
 Clight2.eval_funcall secp_ge m(Internal f_simplicity_fe_invert)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env] E0 mf(Vint Int.one) /\
 finv m bd 0 bw 0 256 256 bi mf true(encode(@literal_fe_invert Alg.CoreFunSem value)) /\
 modinfo_fe_state mf /\
 (forall b chunk ofs,Mem.valid_block mi b -> Mem.load chunk mf b ofs=Mem.load chunk mi b ofs).
Proof.
 intro CountCall;destruct secp_initial_memory_exists as(mi & Init).
 pose proof(modinfo_fe_state_initial mi Init) as Ready.
 destruct(field_invert_runs_from_initialized value env mi CountCall Ready)
  as(m & bd & bs & bi & bw & edge & mf & ReadyM & Fields & Input & Output & Before & Call & Final & ReadyF & After).
 exists mi,m,bd,bs,bi,bw,edge,mf.
 exact(conj Init(conj Ready(conj Fields(conj Input(conj Output(conj Call(conj Final(conj ReadyF After)))))))).
Qed.
