(** Every input admits original gej_normalize execution from actual program
    initialization plus fresh frames, at the explicit deferred CTZ boundary. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_output_layout C.jet_frame_inv
 C.jet_encoding C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_frame_constructible
 C.jet_secp_modinfo_fe_global C.jet_secp_modinfo_fe_caller C.jet_secp_scalar_lambda_init_exists
 C.jet_secp_fe_invert_fresh C.jet_secp_gej_norm_branch C.jet_secp_gej_norm_lifecycle C.jet_secp_gej_norm_local.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_normalize encode Genv.init_mem jets_secp.prog.

Theorem gej_normalize_runs_from_actual_init (x y z:Ty.tySem Word256) env :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 exists mi m bd bs bi bw edge mf,
 Genv.init_mem jets_secp.prog=Some mi /\ modinfo_fe_state mi /\
 frame_fields_at m bs 0 bi edge 0 /\
 frame_input_cells_at m bi edge 0(@encode(Ty.Prod(Ty.Prod Word256 Word256)Word256)((x,y),z)) /\
 write_frame_at m bd 0 bw 0 513 513 /\
 Clight2.eval_funcall secp_ge m(Internal f_simplicity_gej_normalize)
  [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;env]E0 mf(Vint Int.one) /\
 finv m bd 0 bw 0 513 513 bi mf true(encode(@literal_gej_normalize Alg.CoreFunSem ((x,y),z))) /\
 modinfo_fe_state mf /\
 (forall b chunk ofs,Mem.valid_block mi b -> Mem.load chunk mf b ofs=Mem.load chunk mi b ofs).
Proof.
 intro CountCall;destruct secp_initial_memory_exists as(mi & Init).
 pose proof(modinfo_fe_state_initial mi Init) as Ready.
 destruct(jet_frames_constructible mi(@encode(Ty.Prod(Ty.Prod Word256 Word256)Word256)((x,y),z))513)
  as(m & bd & bs & bi & bw & edge & Base & Align & Fields & Input & Output & Sep & Old).
 { rewrite encode_length;change(768<=18446744073709551615);lia. }
 { change(0<=513<=18446744073709551615);lia. }
 assert(ReadyM:modinfo_fe_state m).
 { eapply modinfo_fe_state_old_blocks;[exact Ready|].
   intros b V;destruct(Old b V) as(VF & _ & _ & _ & _ & Loads & Perms);exact(conj VF(conj Loads Perms)). }
 destruct(gej_norm_split_input _ _ _ _ _ _ _ Input) as(IX & IY & IZ).
 destruct(eval_gej_normalize_initialized env m bd 0 bs 0 bw 0 513 513 bi edge 0 x y z
  CountCall ReadyM Output ltac:(lia) Base Align Fields IX IY IZ ltac:(lia)
  ltac:(change(768<=18446744073709551615);lia))
  as(mf & Call & Final & Frame & ReadyF & Preserved).
 exists mi,m,bd,bs,bi,bw,edge,mf;split;[exact Init|];split;[exact Ready|];split;[exact Fields|];
 split;[exact Input|];split;[exact Output|];split;[exact Call|];split;[exact Final|];split;[exact ReadyF|].
 intros b chunk ofs V;destruct(Old b V) as(VF & ND & _ & NI & NW & Loads & _).
 rewrite(proj1 Frame);[exact(Loads chunk ofs)|exact VF|].
 intros pos Range;unfold extA,fext;intros[[E|[E|E]]_];contradiction.
Qed.
