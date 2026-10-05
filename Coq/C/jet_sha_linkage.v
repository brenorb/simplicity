(** Linkage of the SHA translation unit (core jets together with the portable
    SHA-256 compression function) and execution of its pure helper functions
    Ch, Maj, Sigma0, Sigma1, sigma0, sigma1 against the functional SHA-256
    model of [sha.SHA256]. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Cop Clight ClightBigstep Maps Globalenvs Errors Values Memory Events.
Require sha.SHA256.
Require Import C.jets_sha.
Import Ctypes Values ListNotations Clightdefs.
Local Open Scope Z_scope.
Local Transparent Archi.ptr64.
Set Default Timeout 120.

Definition sha_ge : Clight.genv := Clight.globalenv jets_sha.prog.
Definition sha_symbol_block (id : ident) : block :=
  match Genv.find_symbol (Clight.genv_genv sha_ge) id with
  | Some b => b | None => 1%positive end.

Ltac sha_symbol := vm_compute; reflexivity.

Lemma sha_Ch_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _Ch = Some (sha_symbol_block _Ch).
Proof. sha_symbol. Qed.
Lemma sha_Ch_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _Ch) Ptrofs.zero) = Some (Internal f_Ch).
Proof. sha_symbol. Qed.
Lemma sha_Maj_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _Maj = Some (sha_symbol_block _Maj).
Proof. sha_symbol. Qed.
Lemma sha_Maj_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _Maj) Ptrofs.zero) = Some (Internal f_Maj).
Proof. sha_symbol. Qed.
Lemma sha_Sigma0_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _Sigma0 = Some (sha_symbol_block _Sigma0).
Proof. sha_symbol. Qed.
Lemma sha_Sigma0_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _Sigma0) Ptrofs.zero) = Some (Internal f_Sigma0).
Proof. sha_symbol. Qed.
Lemma sha_Sigma1_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _Sigma1 = Some (sha_symbol_block _Sigma1).
Proof. sha_symbol. Qed.
Lemma sha_Sigma1_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _Sigma1) Ptrofs.zero) = Some (Internal f_Sigma1).
Proof. sha_symbol. Qed.
Lemma sha_sigma0_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _sigma0 = Some (sha_symbol_block _sigma0).
Proof. sha_symbol. Qed.
Lemma sha_sigma0_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sigma0) Ptrofs.zero) = Some (Internal f_sigma0).
Proof. sha_symbol. Qed.
Lemma sha_sigma1_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _sigma1 = Some (sha_symbol_block _sigma1).
Proof. sha_symbol. Qed.
Lemma sha_sigma1_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sigma1) Ptrofs.zero) = Some (Internal f_sigma1).
Proof. sha_symbol. Qed.
Lemma sha_Round_symbol : Genv.find_symbol (Clight.genv_genv sha_ge) _Round = Some (sha_symbol_block _Round).
Proof. sha_symbol. Qed.
Lemma sha_Round_funct : Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _Round) Ptrofs.zero) = Some (Internal f_Round).
Proof. sha_symbol. Qed.
Lemma sha_compression_symbol :
  Genv.find_symbol (Clight.genv_genv sha_ge) _sha256_compression_portable =
    Some (sha_symbol_block _sha256_compression_portable).
Proof. sha_symbol. Qed.
Lemma sha_compression_funct :
  Genv.find_funct (Clight.genv_genv sha_ge) (Vptr (sha_symbol_block _sha256_compression_portable) Ptrofs.zero) =
    Some (Internal f_sha256_compression_portable).
Proof. sha_symbol. Qed.

Local Opaque sha_ge.

(** The C expressions of the helpers. *)
Definition c_Ch (x y z : int) : int := Int.xor z (Int.and x (Int.xor y z)).
Definition c_Maj (x y z : int) : int := Int.or (Int.and x y) (Int.and z (Int.or x y)).
Definition c_rot (r : Z) (x : int) : int :=
  Int.or (Int.shru x (Int.repr r)) (Int.shl (Int.mul (Int.repr 1) x) (Int.repr (32 - r))).
Definition c_Sigma0 (x : int) : int := Int.xor (Int.xor (c_rot 2 x) (c_rot 13 x)) (c_rot 22 x).
Definition c_Sigma1 (x : int) : int := Int.xor (Int.xor (c_rot 6 x) (c_rot 11 x)) (c_rot 25 x).
Definition c_sigma0 (x : int) : int := Int.xor (Int.xor (c_rot 7 x) (c_rot 18 x)) (Int.shru x (Int.repr 3)).
Definition c_sigma1 (x : int) : int := Int.xor (Int.xor (c_rot 17 x) (c_rot 19 x)) (Int.shru x (Int.repr 10)).

Ltac sha_ev :=
  first [apply eval_Etempvar; reflexivity | apply eval_Econst_int
        | eapply eval_Ebinop; [sha_ev|sha_ev|reflexivity]].

Ltac sha_pure m :=
  eapply eval_funcall_internal with (e := empty_env) (m1 := m) (m2 := m);
  [ apply function_entry2_intro;
    [ apply list_norepet_nil
    | repeat constructor; simpl; intuition discriminate
    | intros x0 y0 HX HY; cbn in HY; contradiction
    | apply alloc_variables_nil
    | reflexivity ]
  | apply exec_Sreturn_some; sha_ev
  | cbn; split; [discriminate|reflexivity]
  | reflexivity ].

Lemma eval_sha_Ch m x y z :
  Clight2.eval_funcall sha_ge m (Internal f_Ch) [Vint x; Vint y; Vint z] E0 m (Vint (c_Ch x y z)).
Proof. sha_pure m. Qed.
Lemma eval_sha_Maj m x y z :
  Clight2.eval_funcall sha_ge m (Internal f_Maj) [Vint x; Vint y; Vint z] E0 m (Vint (c_Maj x y z)).
Proof. sha_pure m. Qed.
Lemma eval_sha_Sigma0 m x :
  Clight2.eval_funcall sha_ge m (Internal f_Sigma0) [Vint x] E0 m (Vint (c_Sigma0 x)).
Proof. sha_pure m. Qed.
Lemma eval_sha_Sigma1 m x :
  Clight2.eval_funcall sha_ge m (Internal f_Sigma1) [Vint x] E0 m (Vint (c_Sigma1 x)).
Proof. sha_pure m. Qed.
Lemma eval_sha_sigma0 m x :
  Clight2.eval_funcall sha_ge m (Internal f_sigma0) [Vint x] E0 m (Vint (c_sigma0 x)).
Proof. sha_pure m. Qed.
Lemma eval_sha_sigma1 m x :
  Clight2.eval_funcall sha_ge m (Internal f_sigma1) [Vint x] E0 m (Vint (c_sigma1 x)).
Proof. sha_pure m. Qed.

(** Agreement with the functional model. *)
Lemma c_Ch_correct x y z : c_Ch x y z = SHA256.Ch x y z.
Proof.
  unfold c_Ch, SHA256.Ch. apply Int.same_bits_eq. intros i Hi.
  rewrite !Int.bits_xor, !Int.bits_and, Int.bits_xor, Int.bits_not by exact Hi.
  destruct (Int.testbit x i), (Int.testbit y i), (Int.testbit z i); reflexivity.
Qed.

Lemma c_Maj_correct x y z : c_Maj x y z = SHA256.Maj x y z.
Proof.
  unfold c_Maj, SHA256.Maj. apply Int.same_bits_eq. intros i Hi.
  rewrite Int.bits_or, !Int.bits_xor, !Int.bits_and, Int.bits_or by exact Hi.
  destruct (Int.testbit x i), (Int.testbit y i), (Int.testbit z i); reflexivity.
Qed.

Lemma c_rot_correct r x : 0 < r < 32 -> c_rot r x = SHA256.Rotr r x.
Proof.
  intros Hr. unfold c_rot, SHA256.Rotr.
  assert (Hmul : Int.mul (Int.repr 1) x = x) by (rewrite Int.mul_commut; apply Int.mul_one).
  rewrite Hmul. rewrite Int.or_commut.
  symmetry. apply Int.or_ror.
  - unfold Int.ltu. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    change (Int.unsigned Int.iwordsize) with 32. rewrite zlt_true by lia. reflexivity.
  - unfold Int.ltu. rewrite Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    change (Int.unsigned Int.iwordsize) with 32. rewrite zlt_true by lia. reflexivity.
  - unfold Int.add. rewrite !Int.unsigned_repr by (change Int.max_unsigned with 4294967295; lia).
    change Int.iwordsize with (Int.repr 32). f_equal. lia.
Qed.

Lemma c_Sigma0_correct x : c_Sigma0 x = SHA256.Sigma_0 x.
Proof. unfold c_Sigma0, SHA256.Sigma_0. rewrite !c_rot_correct by lia. reflexivity. Qed.
Lemma c_Sigma1_correct x : c_Sigma1 x = SHA256.Sigma_1 x.
Proof. unfold c_Sigma1, SHA256.Sigma_1. rewrite !c_rot_correct by lia. reflexivity. Qed.
Lemma c_sigma0_correct x : c_sigma0 x = SHA256.sigma_0 x.
Proof. unfold c_sigma0, SHA256.sigma_0. rewrite !c_rot_correct by lia. reflexivity. Qed.
Lemma c_sigma1_correct x : c_sigma1 x = SHA256.sigma_1 x.
Proof. unfold c_sigma1, SHA256.sigma_1. rewrite !c_rot_correct by lia. reflexivity. Qed.
