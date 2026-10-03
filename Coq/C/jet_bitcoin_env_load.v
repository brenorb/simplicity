(** Environment loads survive output steps whose footprint they avoid. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Integers AST Memory Values.
Require Import C.jet_write_layout C.jet_output_layout C.jet_application_sep C.jet_bitcoin_effects.
Import Mem.
Local Open Scope Z_scope.

Lemma write_effect_env_load m mf bf base bw edge cursor n cells cursor0 count0 b lo hi chunk ofs :
  0 < n -> n <= cursor -> cursor <= cursor0 -> cursor0 - count0 <= cursor - n ->
  write_effect m mf bf base bw edge cursor n cells ->
  out_sep bf base bw edge cursor0 count0 b lo hi ->
  lo <= ofs -> ofs + size_chunk chunk <= hi ->
  Mem.load chunk mf b ofs = Mem.load chunk m b ofs.
Proof.
  intros Hn HnC HC HL HE Hsep Hlo Hhi.
  pose proof (out_sep_sub bf base bw edge cursor0 count0 cursor n b lo hi Hn HnC HC HL Hsep) as [Hf Hw].
  destruct HE as (_ & _ & _ & L & _).
  apply L.
  - destruct Hf as [H|[H|H]]; [left; exact H|right; left; lia|right; right; lia].
  - unfold out_low, out_high in Hw. destruct Hw as [H|[H|H]];
      [left; exact H|right; left; lia|right; right; lia].
Qed.
