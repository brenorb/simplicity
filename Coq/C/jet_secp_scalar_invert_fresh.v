(** Original scalar-invert execution from actual initialized program memory
    on fresh caller frames. Every memory/frame/global premise is discharged;
    the postponed counting-call obligation is still explicit. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Values Memory Globalenvs Clight ClightBigstep Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_encoding C.jet_secp_frame C.jet_secp_wrapper_run C.jet_secp_linkage C.jets_secp C.jet_sx_mem
 C.jet_frame_constructible C.jet_secp_modinfo_scalar_initialized
 C.jet_secp_scalar_invert_lifecycle C.jet_secp_scalar_invert_literal.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque literal_scalar_invert encode secp_ge Genv.init_mem jets_secp.prog.

Theorem scalar_invert_runs_from_initialized (value:Ty.tySem(Word 8)) env m0 :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 modinfo_scalar_initialized m0 -> exists m bd bs bi bw edge mf,
 modinfo_scalar_initialized m /\
 frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
 write_frame_at m bd 0 bw 0 256 256 /\
 (forall b chunk ofs,Mem.valid_block m0 b -> Mem.load chunk m b ofs=Mem.load chunk m0 b ofs) /\
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_scalar_invert)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env] E0 mf (Vint Int.one) /\
 finv m bd 0 bw 0 256 256 bi mf true (encode(@literal_scalar_invert Alg.CoreFunSem value)) /\
 modinfo_scalar_initialized mf /\
 (forall b chunk ofs,Mem.valid_block m0 b -> Mem.load chunk mf b ofs=Mem.load chunk m0 b ofs).
Proof.
 intros CountCall Ready.
 destruct(jet_frames_constructible m0 (encode value) 256)
  as(m & bd & bs & bi & bw & edge & Base & Align & Fields & Input & Output & Sep & Old).
 { rewrite encode_length;change(256<=18446744073709551615);lia. }
 { change(0<=256<=18446744073709551615);lia. }
 assert(ReadyM:modinfo_scalar_initialized m).
 { eapply modinfo_scalar_initialized_old_blocks;[exact Ready|].
   intros b Valid;destruct(Old b Valid) as(VF & _ & _ & _ & _ & Loads & Perms).
   exact(conj VF (conj Loads Perms)). }
 pose proof Input as ReaderInput;rewrite encode_word in ReaderInput.
 destruct(eval_secp_scalar_invert_initialized env m bd 0 bs 0 bw 0 256 256 bi edge 0 value
  CountCall ReadyM Output ltac:(lia) Base Align Fields ReaderInput ltac:(lia)
  ltac:(change(256<=18446744073709551615);lia))
  as(mf & Call & Final & Frame & ReadyF & Preserved).
 exists m,bd,bs,bi,bw,edge,mf;split;[exact ReadyM|];split;[exact Fields|];
 split;[exact Input|];split;[exact Output|];split.
 - intros b chunk ofs Valid;destruct(Old b Valid) as(_ & _ & _ & _ & _ & Loads & _);exact(Loads chunk ofs).
 - split;[exact Call|];split;[exact Final|];split;[exact ReadyF|].
   intros b chunk ofs Valid;destruct(Old b Valid) as(VF & ND & _ & NI & NW & Loads & _).
   rewrite(proj1 Frame);[exact(Loads chunk ofs)|exact VF|].
   intros pos Range;unfold extA,fext;intros[[Same|[Same|Same]] _];contradiction.
Qed.

Theorem scalar_invert_runs_from_actual_init (value:Ty.tySem(Word 8)) env :
 (forall mc x,Int64.unsigned x<>0 ->
   Clight2.eval_funcall secp_ge mc (Internal f_secp256k1_ctz64_var) [Vlong x]
    E0 mc (Vint(Int.repr(Z_ctz(Int64.unsigned x))))) ->
 exists mi m bd bs bi bw edge mf,
 Genv.init_mem jets_secp.prog=Some mi /\ modinfo_scalar_initialized mi /\
 frame_fields_at m bs 0 bi edge 0 /\ frame_input_cells_at m bi edge 0 (encode value) /\
 write_frame_at m bd 0 bw 0 256 256 /\
 Clight2.eval_funcall secp_ge m (Internal f_simplicity_scalar_invert)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env] E0 mf (Vint Int.one) /\
 finv m bd 0 bw 0 256 256 bi mf true (encode(@literal_scalar_invert Alg.CoreFunSem value)) /\
 modinfo_scalar_initialized mf /\
 (forall b chunk ofs,Mem.valid_block mi b -> Mem.load chunk mf b ofs=Mem.load chunk mi b ofs).
Proof.
 intro CountCall;destruct modinfo_scalar_initialized_exists as(mi & Init & Ready).
 destruct(scalar_invert_runs_from_initialized value env mi CountCall Ready)
  as(m & bd & bs & bi & bw & edge & mf & ReadyM & Fields & Input & Output & Before & Call & Final & ReadyF & After).
 exists mi,m,bd,bs,bi,bw,edge,mf.
 exact(conj Init (conj Ready (conj Fields (conj Input (conj Output (conj Call (conj Final (conj ReadyF After)))))))).
Qed.
