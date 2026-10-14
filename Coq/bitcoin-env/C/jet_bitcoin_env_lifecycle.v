(** Life cycle of the Bitcoin environment: the two blocks returned by the
    real builders can be released with the real
    [simplicity_bitcoin_freeTapEnv] and [simplicity_bitcoin_freeTransaction],
    and after both calls every other block is as it was. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight ClightBigstep Values Memory Events.
Require Import C.jets_sha C.jet_sha_linkage C.jet_bitcoin_env_free.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 120.

Local Opaque sha_ge.

Theorem free_environment m (bT bE : block) (niv nov nb : int) :
  bT <> bE ->
  Mem.load Mptr m bT (-8) =
    Some (Vlong (Int64.repr (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov))) ->
  Mem.range_perm m bT (-8) (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov) Cur Freeable ->
  Mem.load Mptr m bE (-8) = Some (Vlong (Int64.repr (176 + 32 * Int.unsigned nb))) ->
  Mem.range_perm m bE (-8) (176 + 32 * Int.unsigned nb) Cur Freeable ->
  exists m1 m2,
    Clight2.eval_funcall sha_ge m (Internal f_simplicity_bitcoin_freeTapEnv) [Vptr bE Ptrofs.zero] E0 m1 Vundef /\
    Clight2.eval_funcall sha_ge m1 (Internal f_simplicity_bitcoin_freeTransaction) [Vptr bT Ptrofs.zero] E0 m2 Vundef /\
    (forall ch b ofs, b <> bT -> b <> bE -> Mem.load ch m2 b ofs = Mem.load ch m b ofs) /\
    (forall b ofs k p, b <> bT -> b <> bE -> Mem.perm m b ofs k p -> Mem.perm m2 b ofs k p).
Proof.
  intros NTE HT PT HE PE.
  pose proof (Int.unsigned_range_2 niv) as Hi. pose proof (Int.unsigned_range_2 nov) as Ho.
  pose proof (Int.unsigned_range_2 nb) as Hb. change Int.max_unsigned with 4294967295 in *.
  destruct (eval_freeTapEnv m bE (176 + 32 * Int.unsigned nb)
              ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia) HE PE) as (m1 & HC1 & HF1).
  destruct (eval_freeTransaction m1 bT (488 + 160 * Int.unsigned niv + 40 * Int.unsigned nov)
              ltac:(change Ptrofs.max_unsigned with 18446744073709551615; lia)) as (m2 & HC2 & HF2).
  { rewrite (Mem.load_free _ _ _ _ _ HF1) by (left; exact NTE). exact HT. }
  { intros o Hr. eapply Mem.perm_free_1; [exact HF1|left; exact NTE|apply PT, Hr]. }
  exists m1, m2. split; [exact HC1|]. split; [exact HC2|]. split.
  - intros ch b ofs N1 N2. rewrite (Mem.load_free _ _ _ _ _ HF2) by (left; exact N1).
    apply (Mem.load_free _ _ _ _ _ HF1). left. exact N2.
  - intros b ofs k p N1 N2 Hp. eapply Mem.perm_free_1; [exact HF2|left; exact N1|].
    eapply Mem.perm_free_1; [exact HF1|left; exact N2|exact Hp].
Qed.
