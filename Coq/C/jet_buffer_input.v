(** Canonical Buffer63 input decomposition, shared with present-chunk readers
    and writers. These representation facts do not add public jet coverage. *)
From Coq Require Import List Lia ZArith.
From compcert Require Import AST Memory.
Require Import Simplicity.Ty Simplicity.Word Simplicity.Translate.
Require Import C.jet_buffer_empty_spec C.jet_encoding C.jet_input_layout.
Import ListNotations.
Import Values.
Set Default Timeout 10.

Fixpoint vector_values (X : Ty.Ty) (n : nat) : Ty.tySem (Vector X n) -> list (Ty.tySem X) :=
  match n return Ty.tySem (Vector X n) -> list (Ty.tySem X) with
  | O => fun x => [x]
  | S n => fun x => vector_values X n (fst x) ++ vector_values X n (snd x)
  end.
Lemma vector_values_length X n (x : Ty.tySem (Vector X n)) :
  length (vector_values X n x) = Nat.pow 2 n.
Proof.
  induction n; [reflexivity|]. destruct x as [hi lo]. cbn [vector_values fst snd].
  rewrite app_length, (IHn hi), (IHn lo). cbn [Nat.pow]; lia.
Qed.

Lemma buffer_input_cells_preserved m mf bw edge cursor cells :
  (forall ofs w, Mem.load Mint64 m bw ofs = Some (Vlong w) ->
    Mem.load Mint64 mf bw ofs = Some (Vlong w)) ->
  frame_input_cells_at m bw edge cursor cells -> frame_input_cells_at mf bw edge cursor cells.
Proof.
  intros HL HC i c Hi. specialize (HC i c Hi). destruct c as [bit|]; cbn [cell_matches] in HC |- *.
  - eapply frame_input_bit_at_preserved; eauto.
  - destruct HC as [bit HC]. exists bit. eapply frame_input_bit_at_preserved; eauto.
Qed.
Lemma encode_vector_values X n (x : Ty.tySem (Vector X n)) :
  encode x = concat (map (@encode X) (vector_values X n x)).
Proof.
  induction n; [cbn [vector_values map concat]; rewrite app_nil_r; reflexivity|].
  destruct x as [hi lo]. change (encode hi ++ encode lo =
    concat (map (@encode X) (vector_values X n hi ++ vector_values X n lo))).
  rewrite map_app, concat_app, (IHn hi), (IHn lo). reflexivity.
Qed.

Lemma encode_present_sum X (x : Ty.tySem X) :
  @encode (Ty.Sum Ty.Unit X) (inr x) = Some true :: encode x.
Proof.
  change (Some true :: (repeat None (0 - Translate.bitSize X) ++ encode x) =
    Some true :: encode x).
  rewrite Nat.sub_0_l. reflexivity.
Qed.

Definition byte_chunk := (nat * option (list (Ty.tySem (Word 3))))%type.
Definition byte_chunk_cells (chunk : byte_chunk) : list BitMachine.Cell :=
  match snd chunk with
  | None => Some false :: repeat None (8 * fst chunk)
  | Some xs => Some true :: concat (map (@encode (Word 3)) xs)
  end.
Fixpoint buffer_byte_chunks (depth : nat) :
    Ty.tySem (buffer_type (Word 3) depth) -> list byte_chunk :=
  match depth return Ty.tySem (buffer_type (Word 3) depth) -> list byte_chunk with
  | O => fun x => [(1, match x with inl _ => None | inr x => Some [x] end)]
  | S d => fun x =>
    (Nat.pow 2 (S d), match fst x with inl _ => None | inr v => Some (vector_values (Word 3) (S d) v) end) ::
    buffer_byte_chunks d (snd x)
  end.

Lemma vector_byte_bitSize n : Translate.bitSize (Vector (Word 3) n) = (8 * Nat.pow 2 n)%nat.
Proof. induction n; [reflexivity|]. cbn [Vector Translate.bitSize]. rewrite IHn. cbn [Nat.pow]; lia. Qed.

Lemma buffer_byte_chunks_cells depth (x : Ty.tySem (buffer_type (Word 3) depth)) :
  encode x = concat (map byte_chunk_cells (buffer_byte_chunks depth x)).
Proof.
  induction depth.
  - destruct x as [[]|x].
    + reflexivity.
    + change (Some true :: encode x = Some true :: ((encode x ++ []) ++ [])).
      rewrite !app_nil_r. reflexivity.
  - destruct x as [[[]|head] tail].
    + change (@encode (Ty.Sum Ty.Unit (Vector (Word 3) (S depth))) (inl tt) ++ encode tail =
        (Some false :: repeat None (8 * Nat.pow 2 (S depth))) ++
        concat (map byte_chunk_cells (buffer_byte_chunks depth tail))).
      rewrite encode_empty_sum, vector_byte_bitSize, IHdepth. reflexivity.
    + change (@encode (Ty.Sum Ty.Unit (Vector (Word 3) (S depth))) (inr head) ++ encode tail =
        (Some true :: concat (map (@encode (Word 3)) (vector_values (Word 3) (S depth) head))) ++
        concat (map byte_chunk_cells (buffer_byte_chunks depth tail))).
      rewrite encode_present_sum, encode_vector_values, IHdepth. reflexivity.
Qed.

Lemma buffer_byte_chunks_lengths depth (x : Ty.tySem (buffer_type (Word 3) depth)) :
  Forall (fun chunk => match snd chunk with None => True | Some xs => length xs = fst chunk end)
    (buffer_byte_chunks depth x).
Proof.
  induction depth.
  - destruct x as [[]|x]; repeat constructor.
  - destruct x as [[[]|head] tail]; constructor; [exact I|apply IHdepth|apply vector_values_length|apply IHdepth].
Qed.

Lemma frame_input_byte_list m bw edge cursor (xs : list (Ty.tySem (Word 3))) :
  frame_input_cells_at m bw edge cursor (concat (map (@encode (Word 3)) xs)) <->
  forall i x, nth_error xs i = Some x ->
    frame_input_word_at m bw edge (cursor + 8 * Z.of_nat i)%Z x.
Proof.
  revert cursor. induction xs as [|x xs IH]; intros cursor.
  - split.
    + intros _ i v H; destruct i; discriminate.
    + intros _ i c H; destruct i; discriminate.
  - change (frame_input_cells_at m bw edge cursor (encode x ++ concat (map (@encode (Word 3)) xs)) <->
      forall i y, nth_error (x :: xs) i = Some y ->
        frame_input_word_at m bw edge (cursor + 8 * Z.of_nat i)%Z y).
    rewrite frame_input_cells_at_app, encode_word_length, <- frame_input_word_at_encode, IH.
    split.
    + intros [HX HT] [|i] y Hy.
      * cbn in Hy. injection Hy as <-. replace (cursor + 8 * Z.of_nat 0)%Z with cursor by lia. exact HX.
      * cbn in Hy. replace (cursor + 8 * Z.of_nat (S i))%Z with (cursor + 8 + 8 * Z.of_nat i)%Z by lia.
        exact (HT i y Hy).
    + intros H. split.
      * pose proof (H 0 x eq_refl) as HX. replace (cursor + 8 * Z.of_nat 0)%Z with cursor in HX by lia. exact HX.
      * intros i y Hy. pose proof (H (S i) y Hy) as HT.
        replace (cursor + 8 * Z.of_nat (S i))%Z with (cursor + 8 + 8 * Z.of_nat i)%Z in HT by lia. exact HT.
Qed.
