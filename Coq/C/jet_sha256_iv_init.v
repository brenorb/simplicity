(** Canonical Programs.Sha256.Lib.iv constant and the actual C sha256_iv
    initializer.  The enclosing simplicity_sha_256_iv jet still needs its
    write32s array serialization and allocation/copy/free lifecycle proved. *)
From Coq Require Import ZArith List Lia.
From compcert Require Import Coqlib Integers AST Ctypes Clight Maps.
From compcert Require Import ClightBigstep Memory Events.
Require Import Simplicity.Word Simplicity.Digest Simplicity.Translate.
Require Import C.jets C.jet_exec C.jet_uint32_array_init.
Import Values Mem Ctypes ListNotations Clightdefs.
Local Open Scope Z_scope.
Set Default Timeout 10.

Definition sha256_iv_constants : list Z :=
  [1779033703; 3144134277; 1013904242; 2773480762;
   1359893119; 2600822924; 528734635; 1541459225].
Definition sha256_iv_words := map uint32_init_value sha256_iv_constants.
Definition sha256_iv_spec {term : Alg.Core.Algebra} :
    @Alg.Core.domain term Ty.Unit (Word 8) :=
  Alg.scribe (@fromZ (WordToZ 8)
    0x6a09e667bb67ae853c6ef372a54ff53a510e527f9b05688c1f83d9ab5be0cd19).

Lemma sha256_iv_spec_parametric : Alg.Core.Parametric (@sha256_iv_spec).
Proof. intros alg1 alg2 R. unfold sha256_iv_spec. apply Alg.scribe_Parametric. Qed.

Lemma sha256_iv_words_registers : sha256_iv_words = SHA256.init_registers.
Proof. vm_compute; reflexivity. Qed.

Lemma sha256_iv_spec_digest :
  @sha256_iv_spec Alg.CoreFunSem tt = from_hash256 Digest.sha256_iv.
Proof. vm_compute; reflexivity. Qed.

Lemma sha256_iv_spec_cells :
  encode (@sha256_iv_spec Alg.CoreFunSem tt) =
    concat (map (fun x => encode (@fromZ (WordToZ 5) (Int.unsigned x))) sha256_iv_words).
Proof. vm_compute; reflexivity. Qed.

Lemma sha256_iv_init_body : f_sha256_iv.(fn_body) = uint32_init_stmts 0 sha256_iv_constants.
Proof. reflexivity. Qed.

Definition sha256_iv_init_env b base := PTree.set _iv (Vptr b (Ptrofs.repr base))
  (create_undef_temps f_sha256_iv.(fn_temps)).

Lemma sha256_iv_init_entry m b base :
  function_entry2 ge0 f_sha256_iv [Vptr b (Ptrofs.repr base)]
    m empty_env (sha256_iv_init_env b base) m.
Proof.
  constructor.
  - constructor.
  - repeat constructor; simpl; tauto.
  - intros i j HI HJ. contradiction.
  - constructor.
  - reflexivity.
Qed.

Theorem eval_sha256_iv_init_layout m b base :
  0 <= base -> base + 32 <= Ptrofs.max_unsigned -> (4 | base) ->
  Mem.range_perm m b base (base + 32) Cur Writable ->
  exists mf,
    Clight2.eval_funcall ge0 m (Internal f_sha256_iv) [Vptr b (Ptrofs.repr base)] E0 mf Vundef /\
    uint32_array_at mf b base sha256_iv_words /\
    (forall chunk bb ofs, bb <> b \/ ofs + size_chunk chunk <= base \/ base + 32 <= ofs ->
      Mem.load chunk mf bb ofs = Mem.load chunk m bb ofs) /\
    (forall bb ofs kind p, Mem.perm m bb ofs kind p -> Mem.perm mf bb ofs kind p) /\
    (forall bb, Mem.valid_block m bb -> Mem.valid_block mf bb).
Proof.
  intros HB HM HA HR.
  assert (HN : length sha256_iv_constants = 8%nat) by reflexivity.
  destruct (exec_uint32_init_array m (sha256_iv_init_env b base) b base 0 sha256_iv_constants
    ltac:(reflexivity) HB ltac:(change (base + 32 <= Ptrofs.max_unsigned); exact HM)
    ltac:(change (8 <= 2147483647); lia) HA
    ltac:(rewrite HN; replace (base + 4 * Z.of_nat 0) with base by lia;
      replace (base + 4 * (Z.of_nat 0 + Z.of_nat 8)) with (base + 32) by lia; exact HR))
    as [mf [Hbody [Harray [Hloads [Hperm Hvalid]]]]].
  exists mf. split.
  - eapply eval_funcall_internal with (e := empty_env)
      (le1 := sha256_iv_init_env b base) (le2 := sha256_iv_init_env b base)
      (m1 := m) (m2 := mf) (out := Out_normal).
    + apply sha256_iv_init_entry.
    + rewrite sha256_iv_init_body. exact Hbody.
    + reflexivity.
    + reflexivity.
  - split.
    + replace base with (base + 4 * Z.of_nat 0) by lia. exact Harray.
    + split.
      * intros chunk bb ofs HO. apply Hloads. rewrite HN.
        change (bb <> b \/ ofs + size_chunk chunk <= base + 0 \/ base + 32 <= ofs). lia.
      * split; assumption.
Qed.
