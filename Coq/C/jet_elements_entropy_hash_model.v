(** Pure hash formula extracted verbatim; no environment-unit execution imported. *)
From Coq Require Import ZArith List.
From compcert Require Import Integers.
Require Import C.jet_sha256_iv_init C.jet_elements_support_sha_uchars_prep C.jet_elements_support_sha_ctx_abs C.jet_elements_support_sha_finalize_exec.
Import ListNotations.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition hash_buffer_regs (bs : list int) : list int :=
  snd (absorb_i (fst (absorb_i [] sha256_iv_words bs)) (snd (absorb_i [] sha256_iv_words bs))
    (sha_pad (Int64.repr (Z.of_nat (length bs))))).
