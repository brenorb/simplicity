(** The registered secp256k1 field jets run on fresh frames for every input.

    [secp_jet_local_spec] is the frame-only contract shape in the secp
    translation unit ([secp_ge]).  As for the core contracts, the frame
    premises are constructible for every input, so each function proved
    against it runs to completion on freshly built frames, returns 1, leaves
    the encoded canonical result and changes no pre-existing load. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Memory Values Events Ctypes Clight ClightBigstep.
Require Simplicity.Alg.
Require Import Simplicity.Ty Simplicity.Word Simplicity.BitMachine Simplicity.Translate.
Require Import C.jet_frame_layout C.jet_input_layout.
Require Import C.jet_write_layout C.jet_output_layout C.jet_encoding.
Require Import C.jet_frame_constructible.
Require Import C.jets_secp C.jet_secp_linkage C.jet_secp_normalize_local.
Require C.jet_secp_odd_local C.jet_secp_zero_local.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 60.

Definition secp_jet_runs_on_fresh_frames (f : function) (A B : Ty) (spec : A -> B) : Prop :=
  forall (a : A) (env : val) (m0 : mem),
  exists m bd bs bw mf,
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk m b ofs = Mem.load chunk m0 b ofs) /\
    Clight2.eval_funcall secp_ge m (Internal f)
      [Vptr bd (Ptrofs.repr 0); Vptr bs (Ptrofs.repr 0); env] E0 mf (Vint Int.one) /\
    frame_output_cells_at mf bw 0 (Z.of_nat (bitSize B)) (encode (spec a)) /\
    (forall b chunk ofs, Mem.valid_block m0 b ->
      Mem.load chunk mf b ofs = Mem.load chunk m0 b ofs).

Theorem secp_jet_local_spec_executable f A B spec :
  secp_jet_local_spec f A B spec ->
  Z.of_nat (bitSize A) <= Int64.max_unsigned ->
  Z.of_nat (bitSize B) <= Int64.max_unsigned ->
  secp_jet_runs_on_fresh_frames f A B spec.
Proof.
  intros HSpec HA HB a env m0.
  destruct (jet_frames_constructible m0 (encode a) (Z.of_nat (bitSize B)))
    as (m & bd & bs & bi & bw & edge & HBase & HAlign & HFields & HInput & HOutput & _ & HOld).
  { rewrite encode_length. exact HA. }
  { lia. }
  destruct (HSpec env m bd 0 bs 0 bi bw edge 0 (Z.of_nat (bitSize B)) 0 a
    HBase HAlign HFields ltac:(lia) ltac:(lia) HInput HOutput)
    as (mf & HCall & HOut & _ & _ & HLoads).
  exists m, bd, bs, bw, mf.
  split; [intros b chunk ofs Hb; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (HOld b Hb)))))) chunk ofs)|].
  split; [exact HCall|]. split; [exact HOut|].
  intros b chunk ofs Hb.
  destruct (HOld b Hb) as (Hvalid & Nd & _ & _ & Nw & HL & _).
  rewrite HLoads; [exact (HL chunk ofs)|exact Hvalid|left; exact Nd|left; exact Nw].
Qed.

Local Ltac bound := vm_compute; discriminate.

Theorem fe_normalize_local_spec_executable :
  ltac:(let T := type of fe_normalize_local_spec in
        lazymatch T with secp_jet_local_spec ?f ?A ?B ?s =>
          exact (secp_jet_runs_on_fresh_frames f A B s) end).
Proof. apply (secp_jet_local_spec_executable _ _ _ _ fe_normalize_local_spec); bound. Qed.

Theorem fe_odd_local_spec_executable :
  ltac:(let T := type of jet_secp_odd_local.fe_odd_local_spec in
        lazymatch T with secp_jet_local_spec ?f ?A ?B ?s =>
          exact (secp_jet_runs_on_fresh_frames f A B s) end).
Proof.
  apply (secp_jet_local_spec_executable _ _ _ _ jet_secp_odd_local.fe_odd_local_spec); bound.
Qed.

Theorem fe_zero_local_spec_executable :
  ltac:(let T := type of jet_secp_zero_local.fe_zero_local_spec in
        lazymatch T with secp_jet_local_spec ?f ?A ?B ?s =>
          exact (secp_jet_runs_on_fresh_frames f A B s) end).
Proof.
  apply (secp_jet_local_spec_executable _ _ _ _ jet_secp_zero_local.fe_zero_local_spec); bound.
Qed.
