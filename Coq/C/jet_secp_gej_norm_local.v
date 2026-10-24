(** Full existing initialized local contract for original gej_normalize.
    CTZ remains explicit; no all-input coverage row is claimed. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
 C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_gej_norm_branch C.jet_secp_gej_norm_lifecycle C.jet_secp_modinfo_fe_caller C.jet_secp_initialized_contract.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_normalize encode.

Lemma gej_norm_split_input m bi edge rc (x y z:Ty.tySem Word256) :
 frame_input_cells_at m bi edge rc(@encode(Ty.Prod(Ty.Prod Word256 Word256)Word256)((x,y),z)) ->
 frame_input_cells_at m bi edge rc(map Some(frame_input_word_bits x)) /\
 frame_input_cells_at m bi edge(rc+256)(map Some(frame_input_word_bits y)) /\
 frame_input_cells_at m bi edge(rc+512)(map Some(frame_input_word_bits z)).
Proof.
 intro Input.
 change(frame_input_cells_at m bi edge rc((encode x++encode y)++encode z)) in Input.
 rewrite !frame_input_cells_at_app,!app_length,!encode_word_length in Input.
 destruct Input as[[IX IY]IZ];split;[rewrite <-encode_word;exact IX|];split;
 rewrite <-encode_word;assumption.
Qed.

Theorem gej_normalize_initialized_local_spec_from_count_calls :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 secp_jet_initialized_local_spec modinfo_fe_state f_simplicity_gej_normalize
  (Ty.Prod(Ty.Prod Word256 Word256)Word256)(Ty.Sum Ty.Unit(Ty.Prod Word256 Word256))
  (@literal_gej_normalize Alg.CoreFunSem).
Proof.
 intros CountCall env m bd base bs sbase bi bw edge outedge cursor rc[[x y]z]
  Ready Base Align Source RC Max Input Output.
 change(rc+768<=Int64.max_unsigned) in Max.
 change(write_frame_at m bd base bw outedge cursor 513) in Output.
 destruct(gej_norm_split_input _ _ _ _ _ _ _ Input) as(IX & IY & IZ).
 destruct(eval_gej_normalize_initialized env m bd base bs sbase bw outedge cursor 513 bi edge rc x y z
  CountCall Ready Output ltac:(lia) Base Align Source IX IY IZ RC Max)
  as(mf & Call & Final & Frame & ReadyF & Preserved).
 destruct Final as[Valid[FinFrame[Capacity[[Cells[Prefix[Fields[Loads Perms]]]]Written]]]].
 rewrite encode_length in Fields,Loads.
 exists mf;split;[exact Call|];split;[exact Cells|];split;[exact Prefix|];split;[exact Fields|];split;[|exact ReadyF].
 intros chunk b ofs V FrameOther OutputOther.
 destruct(Pos.eq_dec b bd) as[D|D];
  [apply Loads;[split;[left;exact D|exact V]|exact FrameOther|exact OutputOther]|].
 destruct(Pos.eq_dec b bw) as[W|W];
  [apply Loads;[split;[right;left;exact W|exact V]|exact FrameOther|exact OutputOther]|].
 destruct(Pos.eq_dec b bi) as[I|I];
  [apply Loads;[split;[right;right;exact I|exact V]|exact FrameOther|exact OutputOther]|].
 apply(proj1 Frame);[exact V|];intros pos Range.
 unfold extA,fext;intros[[E|[E|E]]_];contradiction.
Qed.
