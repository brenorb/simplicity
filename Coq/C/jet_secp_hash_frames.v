(** Actual initialized hash_to_curve execution for every input on constructed
    frames. The unresolved canonical return/infinity boundary stays explicit. *)
From Coq Require Import ZArith List Lia Bool.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events Globalenvs.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate Simplicity.Util.Option.
Require Simplicity.Alg.
Require Import C.jet_memcpy_model C.jet_ctz_model C.jet_encoding C.jet_frame_layout C.jet_input_layout
 C.jet_output_layout C.jet_frame_inv C.jet_sx_mem C.jet_frame_constructible
 C.jet_secp_frame C.jet_secp_linkage C.jets_secp C.jet_secp_field_cmov C.jet_secp_rescale_literal
 C.jet_secp_generator_hash_map C.jet_secp_generator_sha_absorb C.jet_secp_swu_startup
 C.jet_secp_sha_startup C.jet_secp_sha_dispatch C.jet_secp_taptweak_writer_state
 C.jet_secp_fe_invert_fresh C.jet_secp_modinv_normalize62_exec C.jet_clight_readonly_frame
 C.jet_secp_hash_to_curve_spec C.jet_secp_hash_public_call.
Require Import C.jet_secp_hash_startup C.jet_secp_hash_initialized.
Import ListNotations Ctypes Values.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_hash_to_curve encode rescale_field_output.
Definition hash_old_blocks m mf:=forall b,Mem.valid_block m b ->Mem.valid_block mf b /\
 (forall chunk ofs,Mem.load chunk mf b ofs=Mem.load chunk m b ofs) /\
 (forall ofs kind perm,Mem.perm mf b ofs kind perm ->Mem.perm m b ofs kind perm).
Lemma hash_swu_constant_old_blocks d m mf:
 swu_constant_state d m ->hash_old_blocks m mf ->swu_constant_state d mf.
Proof.
 intros State Old;pose proof(swu_constant_valid d m State)as Valid.
 destruct State as(Range & Loads & Bounds).
 destruct(Old _ Valid)as(ValidF & Same & Back).
 assert(LoadsF:forall i,(i<5)%nat ->Mem.load Mint64 mf(swu_constant_block d)(8*Z.of_nat i)=Some(Vlong(swu_constant_digits d i))).
 { intros i Index;rewrite Same;apply Loads;exact Index. }
 assert(RangeF:Mem.range_perm mf(swu_constant_block d)0 40 Cur Readable).
 { apply norm62_words_readable with(w:=swu_constant_digits d);exact LoadsF. }
 split;[exact RangeF|];split;[exact LoadsF|].
 intros pos kind perm;split.
 - intro P;apply(proj1(Bounds pos kind perm));apply Back;exact P.
 - intros[At Order];eapply Mem.perm_implies;[|exact Order].
   destruct kind;[apply Mem.perm_cur_max|];apply RangeF;exact At.
Qed.
Theorem hash_to_curve_ready_old_blocks m mf:hash_to_curve_ready m ->hash_old_blocks m mf ->hash_to_curve_ready mf.
Proof.
 intros(SHA & SWU & Prefix & ValidD & Extent)Old.
 destruct SHA as((Dispatch & Counter)&NoWrite&NoFree).
 assert(VD:Mem.valid_block m secp_sha_dispatch_block)by(eapply load_valid;exact Dispatch).
 assert(VC:Mem.valid_block m secp_sha_counter_block)by(eapply load_valid;exact Counter).
 destruct(Old _ VD)as(VDf & LD & PD);destruct(Old _ VC)as(VCf & LC & PC).
 split.
 - split.
   + split.
     * unfold secp_sha_dispatch_ok in *;change(Mem.load Mptr mf secp_sha_dispatch_block 0=Some(Vptr(secp_symbol_block jets_secp._sha256_compression_portable)Ptrofs.zero)).
       rewrite LD;exact Dispatch.
     * rewrite LC;exact Counter.
   + split;[intros ofs P;apply(NoWrite ofs);apply PC;exact P|intros ofs P;apply(NoFree ofs);apply PD;exact P].
 - split.
   + destruct SWU as[Constants Modulus];split.
     * intro d;eapply hash_swu_constant_old_blocks;[apply Constants|exact Old].
     * eapply modinfo_fe_state_old_blocks;[exact Modulus|exact Old].
   + split.
     * intro prefix;destruct(Prefix prefix)as[Bytes Read].
       assert(VP:Mem.valid_block m(generator_sha_prefix_block prefix))by(eapply load_valid;exact(Bytes 0%nat ltac:(lia))).
       destruct(Old _ VP)as(VPf & LP & PP);split.
       -- intros i Index;rewrite LP;apply Bytes;exact Index.
       -- intros pos P;apply(Read pos);apply PP;exact P.
     * split;[exact VDf|];intros pos kind perm P;apply(Extent pos kind perm);apply PD;exact P.
Qed.
Theorem hash_to_curve_runs_from_actual_init (Copy:memcpy_model)(Count:ctz_model)(key:Ty.tySem(Word 8))ve:
 exists mi m bd bs bi bw edge mf sx sy sz flag ox oy,
 Genv.init_mem jets_secp.prog=Some mi /\hash_to_curve_ready mi /\hash_to_curve_ready m /\
 hash_old_blocks mi m /\
 (forall b,Mem.valid_block mi b ->b<>bd /\b<>bs /\b<>bi /\b<>bw) /\
 (bd<>bi /\bd<>bw /\bd<>bs /\bi<>bw /\bs<>bi /\bs<>bw) /\
 frame_fields_at m bs 0 bi edge 0 /\frame_input_cells_at m bi edge 0(encode key) /\
 write_frame_at m bd 0 bw 0 512 512 /\
 Clight2.eval_funcall secp_ge m(Internal f_simplicity_hash_to_curve)
 [Vptr bd Ptrofs.zero;Vptr bs Ptrofs.zero;ve]E0 mf
 (Vint(cmov_int(generator_hash_accepted false key&&generator_hash_accepted true key))) /\
 @literal_hash_to_curve(Alg.AssertionSem option_Monad_Zero)key=
 (if generator_hash_accepted false key&&generator_hash_accepted true key then
  if Int.eq flag Int.zero then Some(rescale_field_output ox,rescale_field_output oy)else None else None) /\
 hash_public_value key sx sy sz flag ox oy /\
 finv m bd 0 bw 0 512 512 bi mf(generator_hash_accepted false key&&generator_hash_accepted true key)
 (if generator_hash_accepted false key&&generator_hash_accepted true key then
  @encode(Ty.Prod(Word 8)(Word 8))(rescale_field_output ox,rescale_field_output oy)else []) /\
 hash_to_curve_ready mf /\
 (forall b chunk ofs,Mem.valid_block mi b ->Mem.load chunk mf b ofs=Mem.load chunk mi b ofs).
Proof.
 destruct hash_to_curve_ready_exists as(mi & Init & Ready).
 destruct(jet_frames_constructible mi(encode key)512)as(m & bd & bs & bi & bw & edge & Base & Align & Fields & Input & Output & Sep & Old).
 - rewrite encode_length;change(256<=18446744073709551615);lia.
 - change(0<=512<=18446744073709551615);lia.
 - assert(ReadyM:hash_to_curve_ready m).
   { eapply hash_to_curve_ready_old_blocks;[exact Ready|].
     intros b V;destruct(Old b V)as(Vf & ND & NS & NI & NW & Loads & Perms);exact(conj Vf(conj Loads Perms)). }
   destruct(eval_hash_to_curve_initialized_characterization Copy Count key ve m bd 0 bs 0 bi bw edge 0 512 0
    ReadyM Base Align Fields ltac:(lia)ltac:(change(256<=18446744073709551615);lia)Input Output)
   as(mf & sx & sy & sz & flag & ox & oy & Call & Spec & Value & Final & Frame & Read & ReadyF).
   exists mi,m,bd,bs,bi,bw,edge,mf,sx,sy,sz,flag,ox,oy;
   split;[exact Init|];split;[exact Ready|];split;[exact ReadyM|];split.
   + intros b V;destruct(Old b V)as(Vf & ND & NS & NI & NW & Loads & Perms);exact(conj Vf(conj Loads Perms)).
   + split.
     * intros b V;destruct(Old b V)as(Vf & ND & NS & NI & NW & Loads & Perms);repeat split;assumption.
     * split;[exact Sep|];split;[exact Fields|];split;[exact Input|];
       split;[exact Output|];split;[exact Call|];split;[exact Spec|];split;[exact Value|];split;[exact Final|];split;[exact ReadyF|].
       intros b chunk ofs V;destruct(Old b V)as(Vf & ND & NS & NI & NW & Loads & Perms).
   rewrite(proj1 Frame);[exact(Loads chunk ofs)|exact Vf|].
   intros pos Range;unfold extA,fext;intros[[Same|[Same|Same]]_];contradiction.
Qed.
