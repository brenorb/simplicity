(** Shared exact-load transport within an actually owned enclosing allocation. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import AST Integers Values Memory.
Require Import C.jet_sx_state C.jet_sx_eval C.jet_sx_rep C.jet_sx_mem.
Require Import C.jet_secp_fe_nv C.jet_secp_local_regions C.jet_secp_point_write_preservation.
Require Import C.jet_secp_owned_field_slice.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Lemma owned_field_slice_foot_bounds offset size b bx pos :
  foot [(b,0)] (map rshape (owned_field_slice offset size)) bx pos ->
  bx = b /\ offset <= pos < offset+40.
Proof.
  intros (r & s & d & ch & HN & HC & HB & HR).
  destruct r as [|r]; [|destruct r; discriminate].
  change (bx = b) in HB; subst bx; split; [reflexivity|].
  cbn [owned_field_slice free_region u64_cells vars5 rshape rcells rw rfree
    map nth_error cshape cofs cchunk] in HN.
  inversion HN; subst s; cbn [fst] in HC.
  destruct HC as [HC|[HC|[HC|[HC|[HC|HC]]]]]; try contradiction;
    inversion HC; subst d ch;
    cbn [bas lay nth fst snd] in HR;
    change (size_chunk Mint64) with 8 in HR; lia.
Qed.

Lemma owned_field_load_transport offset size m mf b xs :
  offset+40 <= size -> (length xs <= 5)%nat -> fe_at m b offset xs ->
  Mem.range_perm mf b 0 size Cur Freeable ->
  (forall i, (i < 5)%nat ->
    Mem.load Mint64 mf b (offset+8*Z.of_nat i) =
    Mem.load Mint64 m b (offset+8*Z.of_nat i)) ->
  fe_at mf b offset xs.
Proof.
  intros HS HLen (HB & HA & HM & HP & HL) HF HLoads.
  split; [exact HB|]; split; [exact HA|]; split; [exact HM|]; split.
  - apply freeable_range_writable; intros pos HPos; apply HF; lia.
  - intros i x HN; rewrite HLoads; [apply HL;exact HN|].
    assert (i < length xs)%nat by
      (apply (proj1 (nth_error_Some _ _)); rewrite HN;discriminate).
    lia.
Qed.
Print Assumptions owned_field_load_transport.
