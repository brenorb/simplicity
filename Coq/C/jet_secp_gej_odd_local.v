(** Existing full initialized local contract for original gej_y_is_odd.
    The deferred CTZ parameter is not an accepted coverage row. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Ctypes Clight ClightBigstep Memory Values Events.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Bit Simplicity.Translate.
Require Simplicity.Alg.
Require Import C.extraMath C.jet_frame_layout C.jet_input_layout C.jet_write_layout C.jet_output_layout
 C.jet_encoding C.jet_frame_inv C.jet_sx_mem C.jet_secp_frame C.jet_secp_linkage C.jets_secp
 C.jet_secp_gej_odd_literal C.jet_secp_gej_odd_lifecycle C.jet_secp_gej_norm_local
 C.jet_secp_modinfo_fe_caller C.jet_secp_initialized_contract.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.
Local Opaque secp_ge literal_gej_y_is_odd encode.

Theorem gej_y_is_odd_initialized_local_spec_from_count_calls :
 (forall mc w,Int64.unsigned w<>0 ->
   Clight2.eval_funcall secp_ge mc(Internal f_secp256k1_ctz64_var)[Vlong w]
    E0 mc(Vint(Int.repr(Z_ctz(Int64.unsigned w))))) ->
 secp_jet_initialized_local_spec modinfo_fe_state f_simplicity_gej_y_is_odd
  (Ty.Prod(Ty.Prod Word256 Word256)Word256)Bit(@literal_gej_y_is_odd Alg.CoreFunSem).
Proof.
 intros CountCall env m bd base bs sbase bi bw edge outedge cursor rc[[x y]z]
  Ready Base Align Source RC Max Input Output.
 change(rc+768<=Int64.max_unsigned) in Max.
 change(write_frame_at m bd base bw outedge cursor 1) in Output.
 destruct(gej_norm_split_input _ _ _ _ _ _ _ Input) as(IX & IY & IZ).
 destruct(eval_gej_y_is_odd_initialized env m bd base bs sbase bw outedge cursor 1 bi edge rc x y z
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
